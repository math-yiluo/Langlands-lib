/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth (f := t) x
  have hle' : V ≤ t ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := le_top
  have hQ : (t.appLE ⊤ V hle').hom.Smooth :=
    HasRingHomProperty.appLE @Smooth t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hle'
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let ψ : R →+* Γ(T, V) := (t.appLE ⊤ V hle').hom.comp e.toRingHom
  have hψ : ψ.Smooth := RingHom.Smooth.respectsIso.2 _ e hQ
  letI : Algebra R Γ(T, V) := ψ.toAlgebra
  haveI : Algebra.Smooth R Γ(T, V) := RingHom.smooth_algebraMap.mp hψ
  letI : Algebra Γ(T, V) (T.presheaf.stalk x) := (T.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R Γ(T, V)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (T.presheaf.stalk x)
