import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetCutSections
import Langlands.GroupScheme.IdentityJetHomSections

/-! # Retained jet coordinates of the original actual subgroup -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem baseChangeHom_fst {S T : Scheme.{u}} {G H : GroupScheme S}
    (f : H ⟶ G) (b : T ⟶ S) :
    ((GroupScheme.baseChange b).map f).hom.hom.left ≫ Limits.pullback.fst G.X.hom b =
      Limits.pullback.fst H.X.hom b ≫ f.hom.hom.left :=
  Limits.pullback.lift_fst _ _ _

private theorem baseChange_affine {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChange_affine

private theorem homSections_smul_coordinate {S : Scheme.{u}} {G H : GroupScheme S}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (f : H ⟶ G)
    {B : CommRingCat.{u}} (j : G.X.left ⟶ Spec B) (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : B) :
    IdentityJet.homSections f n U
        (a • (IdentityJet.quotientMap G n).app U (IdentityJet.coordinateMap G j U c)) =
      a • (IdentityJet.quotientMap H n).app U
        (IdentityJet.coordinateMap H (f.hom.hom.left ≫ j) U c) := by
  rw [(IdentityJet.homSections f n U).map_smul,
    IdentityJet.homSections_quotientMap, IdentityJet.homGroupSections_coordinateMap]

private theorem coordinateMap_of_comparison {S : Scheme.{u}} (H : GroupScheme S)
    {A C : CommRingCat.{u}} (j : H.X.left ⟶ Spec C) (k : H.X.left ⟶ Spec A)
    (φ : A →+* C) (hφ : j ≫ Spec.map (CommRingCat.ofHom φ) = k)
    (U : S.Opens) (a : A) :
    IdentityJet.coordinateMap H j U (φ a) = IdentityJet.coordinateMap H k U a :=
  (IdentityJet.coordinateMap_comp_specMap H j φ U a).symm.trans
    (congrArg (fun k => IdentityJet.coordinateMap H k U a) hφ)

namespace SelfNormalizingAmbient.ProperQuotientJetData

open AffineCoordinates Corepresented IdentityJet

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i}
  (D : ProperQuotientJetData i Q)

private theorem source_affine (hi : IsClosedSubgroup i) : IsAffineHom H.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

private theorem cut_affine : IsAffineHom D.cutGroup.X.hom := by
  let : IsAffine D.cutGroup.X.left := by
    change IsAffine (Spec (CommRingCat.of (algebra G ⧸ D.ideal)))
    infer_instance
  infer_instance

attribute [local instance] cut_affine

variable {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- The cut representative preserves the original ambient coordinates after base change. -/
theorem originalCutProjection_eq_ambientProjection (hi : IsClosedSubgroup i) :
    ((GroupScheme.baseChange b).map (D.cutRepresentativeIso hi).hom).hom.hom.left ≫
      Limits.pullback.fst D.cutGroup.X.hom b ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.ideal)) =
      ambientProjection G b ((GroupScheme.baseChange b).map i) := by
  rw [← Category.assoc, baseChangeHom_fst, Category.assoc,
    D.cutRepresentativeIso_hom_left]
  rw [ambientProjection, ← Category.assoc
    ((GroupScheme.baseChange b).map i).hom.hom.left, baseChangeHom_fst]
  simp only [Category.assoc]

/-- Retained jet coordinates identify the actual original subgroup's jet sections. -/
def originalBaseChangeJetEquiv (hi : IsClosedSubgroup i) (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (algebra G ⧸ jetIdeal (corepresentation G) D.ideal n) ≃ₗ[Γ(S, U)]
      Γ(module ((GroupScheme.baseChange b).obj H) n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  letI : IsAffineHom H.X.hom := source_affine hi
  exact (cutBaseChangeJetEquiv (isCutOutBy_range D.ideal_range) b n U).trans
    (isoSections ((GroupScheme.baseChange b).mapIso (D.cutRepresentativeIso hi)) n U)

/-- Each retained ambient generator maps to its prescribed actual subgroup jet function. -/
theorem originalBaseChangeJetEquiv_tmul_mk (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    originalBaseChangeJetEquiv D b hi n U
        (a ⊗ₜ[R] Ideal.Quotient.mk (jetIdeal (corepresentation G) D.ideal n) c) =
      a • (quotientMap ((GroupScheme.baseChange b).obj H) n).app U
        (coordinateMap ((GroupScheme.baseChange b).obj H)
          (ambientProjection G b ((GroupScheme.baseChange b).map i)) U c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : IsAffineHom H.X.hom := source_affine hi
  change isoSections ((GroupScheme.baseChange b).mapIso (D.cutRepresentativeIso hi)) n U
    (cutBaseChangeJetEquiv (isCutOutBy_range D.ideal_range) b n U
      (a ⊗ₜ[R] Ideal.Quotient.mk (jetIdeal (corepresentation G) D.ideal n) c)) = _
  rw [isoSections_apply, cutBaseChangeJetEquiv_tmul_mk]
  refine (homSections_smul_coordinate
    ((GroupScheme.baseChange b).map (D.cutRepresentativeIso hi).hom)
    (Limits.pullback.fst D.cutGroup.X.hom b) n U a (Ideal.Quotient.mk D.ideal c)).trans ?_
  apply congrArg (a • ·)
  change (inclusion ((GroupScheme.baseChange b).obj H) n).app
    (((GroupScheme.baseChange b).obj H).X.hom ⁻¹ᵁ U) _ = _
  apply congrArg ((inclusion ((GroupScheme.baseChange b).obj H) n).app
    (((GroupScheme.baseChange b).obj H).X.hom ⁻¹ᵁ U))
  have hj := (Category.assoc
    ((GroupScheme.baseChange b).map (D.cutRepresentativeIso hi).hom).hom.hom.left
    (Limits.pullback.fst D.cutGroup.X.hom b)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.ideal)))).trans
      (D.originalCutProjection_eq_ambientProjection b hi)
  exact coordinateMap_of_comparison ((GroupScheme.baseChange b).obj H)
    (((GroupScheme.baseChange b).map (D.cutRepresentativeIso hi).hom).hom.hom.left ≫
      Limits.pullback.fst D.cutGroup.X.hom b)
    (ambientProjection G b ((GroupScheme.baseChange b).map i))
    (Ideal.Quotient.mk D.ideal) hj U c

end SelfNormalizingAmbient.ProperQuotientJetData
end Langlands.GroupScheme
