import Langlands.GroupScheme.Rational.ConjugateSection
import Langlands.Geometry.Building.UnramifiedConjugateZeroDatum
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
set_option maxHeartbeats 40000
namespace Langlands.Geometry.Building
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
  (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pullback_map_fst {S S' : Scheme.{u}} (a : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback a).map f).left ≫ CategoryTheory.Limits.pullback.fst Y.hom a =
      CategoryTheory.Limits.pullback.fst X.hom a ≫ f.left := by
  simp only [Over.pullback_map_left, CategoryTheory.Limits.pullback.lift_fst]

theorem UnramifiedZeroDatum.galoisTransport_i_left :
    (UnramifiedZeroDatum.galoisTransport F G E σ).i.hom.hom.left =
      ((Over.pullback (galoisBaseMap F (UnramifiedClosure F) σ)).map E.i.hom.hom).left ≫
      (descentBaseChangeIso (baseMap F (UnramifiedClosure F))
        (galoisBaseMap F (UnramifiedClosure F) σ)
        (galoisBaseMap_over F (UnramifiedClosure F) σ) G).hom.hom.hom.left := rfl

theorem UnramifiedZeroDatum.galoisTransport_i_fst :
    (UnramifiedZeroDatum.galoisTransport F G E σ).i.hom.hom.left ≫
      CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F)) =
    CategoryTheory.Limits.pullback.fst E.T.X.hom (galoisBaseMap F (UnramifiedClosure F) σ) ≫
      E.i.hom.hom.left ≫
      CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F)) := by
  have hraw :
      (((Over.pullback (galoisBaseMap F (UnramifiedClosure F) σ)).map E.i.hom.hom).left ≫
        (descentBaseChangeIso (baseMap F (UnramifiedClosure F))
          (galoisBaseMap F (UnramifiedClosure F) σ)
          (galoisBaseMap_over F (UnramifiedClosure F) σ) G).hom.hom.hom.left) ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F)) =
      CategoryTheory.Limits.pullback.fst E.T.X.hom (galoisBaseMap F (UnramifiedClosure F) σ) ≫
        E.i.hom.hom.left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F)) := by
    have hmap :
        ((Over.pullback (galoisBaseMap F (UnramifiedClosure F) σ)).map E.i.hom.hom).left ≫
          CategoryTheory.Limits.pullback.fst (baseChanged F (UnramifiedClosure F) G).X.hom
            (galoisBaseMap F (UnramifiedClosure F) σ) =
        CategoryTheory.Limits.pullback.fst E.T.X.hom (galoisBaseMap F (UnramifiedClosure F) σ) ≫
          E.i.hom.hom.left :=
      pullback_map_fst (galoisBaseMap F (UnramifiedClosure F) σ) E.i.hom.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z =>
        ((Over.pullback (galoisBaseMap F (UnramifiedClosure F) σ)).map E.i.hom.hom).left ≫ z)
        (descentBaseChangeIso_hom_fst (baseMap F (UnramifiedClosure F))
          (galoisBaseMap F (UnramifiedClosure F) σ)
          (galoisBaseMap_over F (UnramifiedClosure F) σ) G)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫
            CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F))) hmap).trans
            (Category.assoc _ _ _))))
  exact (congrArg (fun z => z ≫
    CategoryTheory.Limits.pullback.fst G.X.hom (baseMap F (UnramifiedClosure F)))
    (UnramifiedZeroDatum.galoisTransport_i_left F G E σ)).trans hraw

/-- Inclusion of the changed torus agrees on actual points with coefficient
conjugation in the original ambient group. -/
theorem UnramifiedZeroDatum.galoisTransport_map_point
    (t : rationalPoints E.T.toGrp) :
    rationalPoints.map (UnramifiedZeroDatum.galoisTransport F G E σ).i
        (baseChangeSectionHom (galoisBaseMap F (UnramifiedClosure F) σ) E.T.toGrp t) =
      rationalConjugate F (UnramifiedClosure F) G σ (rationalPoints.map E.i t) := by
  symm
  apply rationalConjugate_eq_of_fst F (UnramifiedClosure F) G σ
  simp only [rationalPoints.map_apply, Over.comp_left]
  rw [Category.assoc, UnramifiedZeroDatum.galoisTransport_i_fst,
    ← Category.assoc, ← Category.assoc, baseChangeSectionHom_fst]
  simp only [Category.assoc]

theorem UnramifiedZeroDatum.galoisTransport_section_mem_torusIwahori
    {t : rationalPoints E.T.toGrp} (ht : t ∈ E.torusIwahori) :
    baseChangeSectionHom (galoisBaseMap F (UnramifiedClosure F) σ) E.T.toGrp t ∈
      (UnramifiedZeroDatum.galoisTransport F G E σ).torusIwahori :=
  UnramifiedZeroDatum.map_torusIwahori_le_galoisTransport F G E σ
    (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)

theorem UnramifiedZeroDatum.galoisTransport_map_section_mem_zeroPoints
    {t : rationalPoints E.T.toGrp} (ht : t ∈ E.torusIwahori) :
    rationalPoints.map (UnramifiedZeroDatum.galoisTransport F G E σ).i
        (baseChangeSectionHom (galoisBaseMap F (UnramifiedClosure F) σ) E.T.toGrp t) ∈
      (UnramifiedZeroDatum.galoisTransport F G E σ).zeroPoints :=
  (UnramifiedZeroDatum.galoisTransport F G E σ).map_torusIwahori_le_zeroPoints
    (Subgroup.mem_map.mpr ⟨_,
      UnramifiedZeroDatum.galoisTransport_section_mem_torusIwahori F G E σ ht, rfl⟩)

/-- Coefficient conjugation sends the supplied torus's Iwahori contribution
into the original zero subgroup. -/
theorem UnramifiedZeroDatum.rationalConjugate_torusIwahori_mem_zeroPoints
    {t : rationalPoints E.T.toGrp} (ht : t ∈ E.torusIwahori) :
    rationalConjugate F (UnramifiedClosure F) G σ (rationalPoints.map E.i t) ∈
      E.zeroPoints := by
  have hzero := UnramifiedZeroDatum.galoisTransport_map_section_mem_zeroPoints F G E σ ht
  rw [UnramifiedZeroDatum.galoisTransport_map_point F G E σ] at hzero
  rwa [unramifiedZeroPointsIndependence F _ (UnramifiedZeroDatum.galoisTransport F G E σ) E]
    at hzero

/-- Galois stability of the torus contribution to the unramified zero subgroup. -/
def UnramifiedZeroTorusGaloisStabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)
    (t : rationalPoints E.T.toGrp), t ∈ E.torusIwahori →
      rationalConjugate F (UnramifiedClosure F) G σ (rationalPoints.map E.i t) ∈
        E.zeroPoints

end Langlands.Geometry.Building
