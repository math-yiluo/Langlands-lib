/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement

/-!
# Continuous coefficients in the universe of module values

The coefficient universe is allowed to be the larger site universe. The old
small-coefficient constructions and slice-site inclusion remain available.

## References

* Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
* Bhatt--Scholze, Definition 6.8.1
* Bhatt--Scholze, Definition 6.8.1 and Lemma 4.2.12
* Bhatt--Scholze, Lemma 6.8.2
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuous functions with pointwise ring operations, allowing larger coefficients. -/
def lisseContinuousCommRingPresheafSized (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom.comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous-function presheaf is a sheaf, with no small-coefficient restriction. -/
theorem isSheaf_lisseContinuousCommRingPresheafSized (X : Scheme.{u})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (lisseContinuousCommRingPresheafSized X T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X)
    (lisseContinuousCommRingPresheafSized X T) (forget CommRingCat.{u + 1})]
  let e : lisseContinuousCommRingPresheafSized X T ⋙ forget CommRingCat.{u + 1} ≅
      (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙
        continuousMapPresheaf T ⋙ uliftFunctor.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  rw [Presheaf.isSheaf_of_iso_iff e]
  refine Functor.op_comp_isSheaf_of_isSheaf
    (F := Scheme.ProEt.forget X ⋙ Over.forget X)
    (J := Scheme.ProEt.topology X) (K := Scheme.proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le
    Scheme.proetaleTopology_le_fpqcTopology

/-- The continuous coefficient sheaf in the module-value universe. -/
def lisseContinuousCommRingSheafSized (X : Scheme.{u}) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨lisseContinuousCommRingPresheafSized X T,
    isSheaf_lisseContinuousCommRingPresheafSized X T⟩

/-- The rational coefficients with the spectral norm topology. -/
def lisseFieldSheafSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheafSized X E

/-- The integral coefficients with the subspace topology. -/
def lisseIntegerSheafSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  lisseContinuousCommRingSheafSized X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion. -/
def lisseIntegerToFieldSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheafSized l E X ⟶ lisseFieldSheafSized l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Padic.coefficientExtensionIntegers l E).subtype.compLeftContinuous _
           continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The constant integral section, in the same topology as the coefficient sheaf. -/
def lisseIntegerConstantSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (lisseIntegerSheafSized l E X).obj.obj U :=
  letI := spectralNorm.normedField ℚ_[l] E
  ULift.up (ContinuousMap.const U.unop.left a)

/-- The constant rational section. -/
def lisseFieldConstantSized (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (a : E) : (lisseFieldSheafSized l E X).obj.obj U :=
  letI := spectralNorm.normedField ℚ_[l] E
  ULift.up (ContinuousMap.const U.unop.left a)

/-- The existing pointwise continuous-function presheaf, retaining commutativity. -/
def lisseContinuousCommRingPresheafUniverses (X : Scheme.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    X.ProEtᵒᵖ ⥤ CommRingCat.{max (u + 1) v} where
  obj U := CommRingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := CommRingCat.ofHom ((continuousMapRingPresheaf X T).map f).hom
  map_id _ := rfl
  map_comp _ _ := rfl

end AlgebraicGeometry.ProEtale
