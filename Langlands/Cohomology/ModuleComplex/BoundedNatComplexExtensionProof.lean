import Langlands.Cohomology.ModuleComplex.BoundedNatComplexExtensionStatement

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ModuleComplex

theorem boundedNatComplexExtension : BoundedNatComplexExtensionStatement.{u} := by
  intro R _ K n hbound hterms
  refine ⟨⟨0, (n : ℤ), inferInstance, ?_⟩, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro z hz
    obtain h | ⟨i, hi⟩ := (ComplexShape.embeddingUpNat.r z).eq_none_or_eq_some
    · exact K.isZero_extend_X' _ z h
    · have he : (i : ℤ) = z :=
        ComplexShape.embeddingUpNat.f_eq_of_r_eq_some hi
      let := hbound i (by omega)
      exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton (K.X i))
        (K.extendXIso _ he)
  · intro z
    obtain h | ⟨i, hi⟩ := (ComplexShape.embeddingUpNat.r z).eq_none_or_eq_some
    · let := ModuleCat.subsingleton_of_isZero (K.isZero_extend_X' _ z h)
      exact ⟨inferInstance, inferInstance⟩
    · let := (hterms i).1
      let := (hterms i).2
      let e := K.extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat.f_eq_of_r_eq_some hi)
      exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
        Module.Projective.of_equiv' e.symm.toLinearEquiv⟩

end Langlands.Cohomology.ModuleComplex
