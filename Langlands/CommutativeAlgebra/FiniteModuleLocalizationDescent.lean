import Mathlib.RingTheory.Localization.Finiteness

/-! # Descent of a finite module over a localization -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- A finite module over a localization is the localization of a finite
submodule over the original ring. -/
theorem exists_fg_submodule_isLocalizedModule
    {R : Type u} [CommRing R] (S : Submonoid R)
    {N : Type v} [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N] [Module.Finite (Localization S) N] :
    ∃ K : Submodule R N, K.FG ∧ IsLocalizedModule S K.subtype := by
  obtain ⟨s, hsfin, hspan⟩ := Submodule.fg_def.mp
    (Module.Finite.fg_top (R := Localization S) (M := N))
  let K := Submodule.span R s
  refine ⟨K, Submodule.fg_span hsfin, ?_⟩
  refine
    { map_units := (isLocalizedModule_id S N (Localization S)).map_units
      surj := ?_
      exists_of_eq := ?_ }
  · intro y
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S (Localization S)
      s y (by rw [hspan]; trivial)
    exact ⟨(⟨t • y, ht⟩, t), rfl⟩
  · intro x y h
    exact ⟨1, by simpa using (Subtype.ext h : x = y)⟩

end Langlands.CommutativeAlgebra
