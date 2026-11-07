import Langlands.Algebra.AxGrothendieckPoints
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Ax–Grothendieck on rational points of an affine scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
  Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- An injective endomorphism on rational points of an affine finite-type scheme
 over an algebraically closed field is surjective on those points. -/
theorem axGrothendieck_points
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (f : X ⟶ X)
    (hinj : Function.Injective
      (fun x : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X => x ≫ f)) :
    Function.Surjective
      (fun x : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X => x ≫ f) := by
  classical
  obtain ⟨D, ⟨e⟩⟩ := (essImage_algSpec (G := X)).mpr (inferInstance : IsAffine X.left)
  let A := D.unop
  have hft : LocallyOfFiniteType ((algSpec (CommRingCat.of k)).obj D).hom := by
    have h : LocallyOfFiniteType (e.hom.left ≫ X.hom) := inferInstance
    simpa only [Over.w] using h
  have : Algebra.FiniteType k A := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hft
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
    exact RingHom.finiteType_algebraMap.mp hft
  let e₀ : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) ≅
      𝟙_ (Over (Spec (CommRingCat.of k))) :=
    Over.isoMk (Iso.refl _) (by simp; rfl)
  let P : ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X) ≃ (A →ₐ[k] k) :=
    { toFun := fun x => (algSpec.fullyFaithful.preimage (e₀.hom ≫ x ≫ e.inv)).unop.hom
      invFun := fun a => e₀.inv ≫ (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom a).op ≫ e.hom
      left_inv := by intro x; simp
      right_inv := by intro a; simp }
  let fA : A →ₐ[k] A :=
    (algSpec.fullyFaithful.preimage (e.hom ≫ f ≫ e.inv)).unop.hom
  have hnat (x : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X) :
      P (x ≫ f) = (P x).comp fA := by
    have h : CommAlgCat.ofHom (P (x ≫ f)) = CommAlgCat.ofHom ((P x).comp fA) := by
      apply Quiver.Hom.op_inj
      apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
      simp [P, fA, Category.assoc]
    exact congrArg CommAlgCat.Hom.hom h
  have hsurj := Langlands.Algebra.axGrothendieck_algHom fA (by
    intro a b h
    apply P.symm.injective
    apply hinj
    apply P.injective
    rw [hnat, hnat, P.apply_symm_apply, P.apply_symm_apply]
    exact h)
  intro y
  obtain ⟨a, ha⟩ := hsurj (P y)
  refine ⟨P.symm a, P.injective ?_⟩
  rw [hnat, P.apply_symm_apply]
  exact ha

end Langlands.AlgebraicGeometry
