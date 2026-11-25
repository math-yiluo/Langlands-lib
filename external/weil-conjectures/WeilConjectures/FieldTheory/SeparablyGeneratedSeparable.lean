/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Mathlib.FieldTheory.SeparablyGenerated

/-!
# Separably generated field extensions are separable

Source: Stacks Project, Algebra, Lemma 10.44.3 (Tag 030X)
(blueprint: lem-weil-pbc-separably-generated-separable).
-/

@[expose] public section

universe u v

namespace Algebra

set_option linter.style.haveILetI false in
/-- A separably generated field extension is separable: every finitely generated intermediate
field is separably generated over the base field.
Source: Stacks Project, Algebra, Lemma 10.44.3 (Tag 030X), with Definition 10.42.1 (Tag 030O)
(blueprint: lem-weil-pbc-separably-generated-separable).

Proof:
1. Split according to the characteristic of `k`. In characteristic zero, every field extension
   is separable by `lem-weil-pbc-char-zero-field-extension-separable`.
2. In prime characteristic, let `L/k` be any field extension. Since `L` is reduced, apply
   `lem-weil-pbc-separably-generated-tensor-reduced` (Tag 030U) to the separably generated
   extension `K/k` and the reduced algebra `L`. Thus `K ⊗[k] L` is reduced for every `L`.
3. Apply `lem-weil-pbc-geometrically-reduced-extension-separable` (Tag 030W, (4) implies (1))
   to obtain separability of `K/k`: each finitely generated intermediate field is separably
   generated, precisely clause (2) of `def-weil-pbc-separable-field-extension`.
-/
theorem isSeparableExtension_of_isSeparablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (h : Algebra.IsSeparablyGenerated k K) : Algebra.IsSeparableExtension k K := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hz
  · letI : Fact (ringChar k).Prime := ⟨hp⟩
    exact isSeparableExtension_of_forall_isReduced_tensorProduct k K (ringChar k)
      (fun L _ _ => isReduced_tensorProduct_of_isSeparablyGenerated k K L h)
  · haveI : CharZero k := by
      letI : CharP k 0 := hz ▸ inferInstance
      exact CharP.charP_to_charZero k
    intro F hF
    letI : Algebra.EssFiniteType k F :=
      (IntermediateField.essFiniteType_iff).2 hF
    rcases exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F with ⟨s, hs, hsep⟩
    refine ⟨(s : Set F), ?_, ?_⟩
    · exact hs
    · exact hsep

end Algebra
