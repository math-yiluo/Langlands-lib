import Langlands.Cohomology.HyperextEdgeMapLinear
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Linearity of actual right-derived functors -/

noncomputable section
open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Cohomology

variable {R : Type*} [Ring R]
  {C D : Type*} [Category C] [Abelian C] [HasInjectiveResolutions C]
  [Category D] [Abelian D] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- Right-derived functors retain the scalar action on actual morphisms. -/
instance rightDerived_linear (n : ℕ) : (F.rightDerived n).Linear R where
  map_smul {X Y} f r := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    let t := InjectiveResolution.desc f J I
    have ht : I.ι.f 0 ≫ t.f 0 = f ≫ J.ι.f 0 := by
      change (I.ι ≫ t).f 0 = _
      rw [InjectiveResolution.desc_commutes, HomologicalComplex.comp_f,
        CochainComplex.single₀_map_f_zero]
    have hrt : I.ι.f 0 ≫ (r • t).f 0 = (r • f) ≫ J.ι.f 0 := by
      simp only [HomologicalComplex.smul_f_apply, Linear.comp_smul,
        Linear.smul_comp, ht]
    apply (cancel_mono (J.isoRightDerivedObj F n).hom).1
    rw [InjectiveResolution.isoRightDerivedObj_hom_naturality
        (r • f) I J (r • t) hrt F n,
      Linear.smul_comp,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f I J t ht F n,
      Functor.map_smul, Linear.comp_smul]

/-- The actual derived action on a hom space as a linear map. -/
def rightDerivedHomLinearMap (n : ℕ) {X Y : C} :
    (X ⟶ Y) →ₗ[R] ((F.rightDerived n).obj X ⟶ (F.rightDerived n).obj Y) where
  toFun := (F.rightDerived n).map
  map_add' := by
    intro f g
    let I := injectiveResolution X
    let J := injectiveResolution Y
    rw [F.rightDerived_map_eq n (f + g)
        (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I)
        (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
          InjectiveResolution.desc_commutes, Functor.map_add, Preadditive.add_comp]),
      F.rightDerived_map_eq n f _ (InjectiveResolution.desc_commutes f J I),
      F.rightDerived_map_eq n g _ (InjectiveResolution.desc_commutes g J I),
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' := fun r f => (F.rightDerived n).map_smul r f

@[simp]
lemma rightDerivedHomLinearMap_apply (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    rightDerivedHomLinearMap (R := R) F n f = (F.rightDerived n).map f := rfl

end Langlands.Cohomology
