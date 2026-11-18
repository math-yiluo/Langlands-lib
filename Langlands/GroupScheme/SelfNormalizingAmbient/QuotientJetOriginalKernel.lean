import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetOriginalSections

/-! # Actual original subgroup jet kernel at the identity orbit point -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData

open AffineCoordinates Corepresented IdentityJet

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i}
  (D : ProperQuotientJetData i Q)

private theorem source_affine (hi : IsClosedSubgroup i) : IsAffineHom H.X.hom := by
  let : IsClosedImmersion i.hom.hom.left := hi
  rw [← Over.w i.hom.hom]
  infer_instance

private theorem baseChange_affine {S T : Scheme.{u}} (K : GroupScheme S)
    [IsAffineHom K.X.hom] (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj K).X.hom := by
  change IsAffineHom (Limits.pullback.snd K.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChange_affine

private theorem tensorCoordinates_tmul_mk {S : Scheme.{u}}
    (K : GroupScheme S) [IsAffineHom K.X.hom] (b : S ⟶ Spec R)
    (j : K ⟶ (GroupScheme.baseChange b).obj G) (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    ambientTensorCoordinates G b j n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • (quotientMap K n).app U (coordinateMap K (ambientProjection G b j) U c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  rw [ambientTensorCoordinates_tmul]
  apply congrArg (a • ·)
  exact restrict_quotientCoordinates_mk K (ambientProjection G b j)
    (augIdeal (corepresentation G)) (ambientProjection_vanishesAtIdentity G b j) n U c

variable {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- The orbit map at the identity, in the retained ideal's fixed coordinates. -/
def originalOrbitOneMap (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →ₗ[Γ(S, U)]
      Γ(S, U) ⊗[R] (algebra G ⧸ jetIdeal (corepresentation G) D.ideal n) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact orbitLinearMap (corepresentation G)
    (show augIdeal (corepresentation G) ^ (n + 1) ≤
      jetIdeal (corepresentation G) D.ideal n from le_sup_right)
    (1 : (functor G).obj (CommAlgCat.of R Γ(S, U)))

/-- The actual original subgroup restriction is the identity orbit quotient,
followed by the actual original jet section equivalence. -/
theorem originalBaseChangeJetEquiv_comp_orbitOne (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : IsAffineHom H.X.hom := source_affine hi
    (D.originalBaseChangeJetEquiv b hi n U).toLinearMap.comp (D.originalOrbitOneMap b n U) =
      ambientTensorCoordinates G b ((GroupScheme.baseChange b).map i) n U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : IsAffineHom H.X.hom := source_affine hi
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    change D.originalBaseChangeJetEquiv b hi n U
      ((orbitMap (corepresentation G) le_sup_right
        (1 : (functor G).obj (CommAlgCat.of R Γ(S, U)))).hom
          (a ⊗ₜ[R] Ideal.Quotient.mk _ c)) = _
    rw [orbitMap_one_tmul]
    exact (D.originalBaseChangeJetEquiv_tmul_mk b hi n U a c).trans
      (tensorCoordinates_tmul_mk ((GroupScheme.baseChange b).obj H) b
        ((GroupScheme.baseChange b).map i) n U a c).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The actual original jet restriction has exactly the identity orbit kernel. -/
theorem ker_originalTensorCoordinates (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI : IsAffineHom H.X.hom := source_affine hi
    LinearMap.ker (ambientTensorCoordinates G b ((GroupScheme.baseChange b).map i) n U) =
      LinearMap.ker (D.originalOrbitOneMap b n U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : IsAffineHom H.X.hom := source_affine hi
  rw [← D.originalBaseChangeJetEquiv_comp_orbitOne b hi n U]
  ext z
  change D.originalBaseChangeJetEquiv b hi n U (D.originalOrbitOneMap b n U z) = 0 ↔
    D.originalOrbitOneMap b n U z = 0
  exact (D.originalBaseChangeJetEquiv b hi n U).map_eq_zero_iff

end Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData
