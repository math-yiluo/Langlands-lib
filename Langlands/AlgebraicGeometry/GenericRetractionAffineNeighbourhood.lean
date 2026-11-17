import Langlands.AlgebraicGeometry.DominantSectionAffineNeighbourhood
import Langlands.AlgebraicGeometry.RationalMapStalkExtension

/-! # Affine neighbourhoods from generic retractions with stalk extensions -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A rational map from an integral scheme to an affine scheme which is a
dominant inverse to `f` at the generic point is an open section on its domain. -/
theorem rationalMap_generic_retraction_section
    {X Z : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [IsReduced Z] [IsAffine Z]
    (f : Z ⟶ X) (r : X.RationalMap Z)
    [IsDominant r.fromFunctionField]
    (h : r.fromFunctionField ≫ f = X.fromSpecStalk (genericPoint X)) :
    IsDominant r.toPartialMap.hom ∧
      r.toPartialMap.hom ≫ f = r.domain.ι := by
  let q := r.toPartialMap
  have hq : q.fromFunctionField = r.fromFunctionField := by
    exact congrArg Scheme.RationalMap.fromFunctionField r.toRationalMap_toPartialMap
  have : IsDominant q.fromFunctionField := by rw [hq]; infer_instance
  have hdom : IsDominant q.hom := by
    let b := q.domain.fromSpecStalkOfMem (genericPoint X)
      ((genericPoint_specializes _).mem_open q.domain.isOpen
        q.dense_domain.nonempty.choose_spec)
    have hb : b ≫ q.hom = q.fromFunctionField := rfl
    have : IsDominant (b ≫ q.hom) := by rw [hb]; infer_instance
    exact IsDominant.of_comp b q.hom
  refine ⟨hdom, ?_⟩
  have he : (q.compHom f).toRationalMap = (𝟙 X : X ⟶ X).toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    change q.fromFunctionField ≫ f = (𝟙 X : X ⟶ X).toPartialMap.fromFunctionField
    rw [hq, h]
    simp [Scheme.PartialMap.fromFunctionField]
  have heq := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
    (S := ⊤_ Scheme)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp he)
  change q.hom ≫ f = q.domain.ι
  dsimp only [Scheme.PartialMap.compHom] at heq
  simpa only [Category.comp_id] using heq

set_option backward.isDefEq.respectTransparency false in
/-- A generic inverse with compatible stalk extensions at a finite set
constructs an actual common affine neighbourhood. -/
def affineNeighbourhoodOfGenericRetraction
    {X Z S : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [IsReduced Z] [IsAffine Z]
    (p : X ⟶ S) (q : Z ⟶ S) [LocallyOfFiniteType q]
    (f : Z ⟶ X) (hf : f ≫ p = q)
    (a : Spec X.functionField ⟶ Z) [IsDominant a]
    (ha : a ≫ f = X.fromSpecStalk (genericPoint X))
    (E : Set X) (hE : E.Finite)
    (hlocal : ∀ x ∈ E, ∃ φ : Spec (X.presheaf.stalk x) ⟶ Z,
      φ ≫ q = X.fromSpecStalk x ≫ p ∧
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ φ = a) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  have hbase : a ≫ q = X.fromSpecStalk (genericPoint X) ≫ p := by
    rw [← hf, ← Category.assoc, ha]
  let r := Scheme.RationalMap.ofFunctionField p q a hbase
  have hr : r.fromFunctionField = a :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField p q a hbase
  have : IsDominant r.fromFunctionField := by rw [hr]; infer_instance
  have hsection := rationalMap_generic_retraction_section f r (by rw [hr, ha])
  have : IsDominant r.toPartialMap.hom := hsection.1
  have hEr : E ⊆ r.domain := by
    intro x hx
    obtain ⟨φ, hφ, hη⟩ := hlocal x hx
    exact rationalMap_mem_domain_of_stalk_extension p q r x φ hφ (hη.trans hr.symm)
  exact affineNeighbourhoodOfDominantSection f r.domain r.toPartialMap.hom
    hsection.2 E hE hEr

end Langlands.AlgebraicGeometry
