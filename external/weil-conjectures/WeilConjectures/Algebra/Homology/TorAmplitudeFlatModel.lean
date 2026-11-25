/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Bounded flat models of complexes of modules of finite Tor amplitude

Source: Stacks Project, More on Algebra, Lemma 15.59.3 (Tag 0654)
(blueprint: lem-pc-module-tor-amplitude-flat-model).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

-- The fixed interface includes `hab`; the generic equivalence needs no interval ordering.
set_option linter.unusedVariables false in
/-- (blueprint: lem-pc-module-tor-amplitude-flat-model) Stacks Project, More on Algebra,
Lemma 15.59.3 (Tag 0654): for a commutative ring `A`, a cochain complex `M` of `A`-modules and
integers `a ≤ b`, the complex `M` has Tor amplitude in `[a, b]` (that is,
`H^i(M ⊗ᴸ_A N) = 0` for every `A`-module `N` and every `i ∉ [a, b]`) if and only if there is a
cochain complex `P` of flat `A`-modules with `P^i = 0` for `i ∉ [a, b]` and an isomorphism
`M ≅ P` in `D(A)`.

Proof: specialize the proved source theorem
`DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat` to `ModuleCat A` and `Q.obj M`.
The instance `ModuleCat.hasFunctorialFlatResolution` supplies its resolution hypothesis.
Categorical flatness and module flatness both mean that `tensorLeft` preserves finite
limits, by `ObjectProperty.flat_iff_preservesFiniteLimits` and
`Module.Flat.iff_preservesFiniteLimits_tensorLeft`. Convert `IsStrictlyGE a` and
`IsStrictlyLE b` to vanishing of the terms below `a` and above `b`, and reverse the
isomorphism of derived objects. The generic equivalence does not need `a ≤ b`. -/
theorem module_torAmplitudeIn_iff_exists_flat_model {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b) :
    torAmplitudeIn (ModuleCat.{u} A) a b (Q.obj M) ↔
      ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (∀ i : ℤ, Module.Flat A (P.X i)) ∧
        (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (Q.obj M ≅ Q.obj P) := by
  have hflat (N : ModuleCat.{u} A) :
      ObjectProperty.flat N ↔ Module.Flat A N :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).trans
      (Module.Flat.iff_preservesFiniteLimits_tensorLeft N).symm
  constructor
  · intro hM
    obtain ⟨P, hge, hle, hP, ⟨e⟩⟩ :=
      (torAmplitudeIn_iff_exists_iso_Q_obj_flat a b (Q.obj M)).mp hM
    refine ⟨P, fun i ↦ (hflat (P.X i)).mp (hP i), ?_, ⟨e.symm⟩⟩
    intro i hi
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  · rintro ⟨P, hP, hzero, ⟨e⟩⟩
    have hge : P.IsStrictlyGE a :=
      (P.isStrictlyGE_iff a).mpr (fun i hi ↦ hzero i (Or.inl hi))
    have hle : P.IsStrictlyLE b :=
      (P.isStrictlyLE_iff b).mpr (fun i hi ↦ hzero i (Or.inr hi))
    exact (torAmplitudeIn_iff_exists_iso_Q_obj_flat a b (Q.obj M)).mpr
      ⟨P, hge, hle, fun i ↦ (hflat (P.X i)).mpr (hP i), ⟨e.symm⟩⟩

end DerivedCategory
