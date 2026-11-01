import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesStatement
import Langlands.AlgebraicGeometry.Picard.ClosedIrreducibleImagesValuativeCriterion

/-! # Scheme adapters for discrete valuative specialization lifting -/

universe u
open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_essFiniteType {S : Scheme.{u}} {x y : S} (h : x ⤳ y) :
    (S.presheaf.stalkSpecializes h).hom.EssFiniteType := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (U := ⊤) (x := y) trivial
  let hx := h.mem_open U.isOpen hy
  let : Algebra Γ(S, U) (S.presheaf.stalk x) :=
    S.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hg : (S.presheaf.germ U x hx).hom.EssFiniteType := by
    change (algebraMap Γ(S, U) (S.presheaf.stalk x)).EssFiniteType
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply RingHom.EssFiniteType.of_comp (S.presheaf.germ U y hy).hom
  simpa only [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes] using hg

theorem specializationResidueMap_essFiniteType {X S : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (x : X) (y : S) (h : p x ⤳ y) :
    (S.presheaf.stalkSpecializes h ≫ p.stalkMap x ≫ X.residue x).hom.EssFiniteType := by
  exact (stalkSpecializes_essFiniteType h).comp ((LocallyOfFiniteType.stalkMap p x).comp
    (RingHom.FiniteType.of_surjective _ (X.residue_surjective x)).essFiniteType)

set_option backward.isDefEq.respectTransparency false in
theorem specializationResidueMap_commutes {X S : Scheme.{u}} (p : X ⟶ S)
    (x : X) (y : S) (h : p x ⤳ y) :
    X.fromSpecResidueField x ≫ p =
      Spec.map (S.presheaf.stalkSpecializes h ≫ p.stalkMap x ≫ X.residue x) ≫
        S.fromSpecStalk y := by
  rw [Scheme.fromSpecResidueField, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  simp only [Spec.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem specializationResidueMap_local_imp_eq {X S : Scheme.{u}} (p : X ⟶ S)
    (x : X) (y : S) (h : p x ⤳ y)
    [IsLocalHom (S.presheaf.stalkSpecializes h ≫ p.stalkMap x ≫ X.residue x).hom] :
    p x = y := by
  let φ := S.presheaf.stalkSpecializes h ≫ p.stalkMap x ≫ X.residue x
  have hc : Spec.map φ (IsLocalRing.closedPoint (X.residueField x)) =
      IsLocalRing.closedPoint (S.presheaf.stalk y) :=
    IsLocalRing.comap_closedPoint φ.hom
  calc
    p x = (X.fromSpecResidueField x ≫ p) (IsLocalRing.closedPoint _) := by simp
    _ = (Spec.map φ ≫ S.fromSpecStalk y) (IsLocalRing.closedPoint _) :=
      congrArg (fun g : Spec (X.residueField x) ⟶ S => g (IsLocalRing.closedPoint _))
        (specializationResidueMap_commutes p x y h)
    _ = y := by rw [Scheme.Hom.comp_apply, hc, S.fromSpecStalk_closedPoint]

end Langlands.AlgebraicGeometry
