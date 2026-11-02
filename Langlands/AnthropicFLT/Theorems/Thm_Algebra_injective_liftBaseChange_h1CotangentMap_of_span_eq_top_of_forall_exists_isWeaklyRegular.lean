/-
Ported from `Theorems/Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (s : Set T) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, ∃ (ι : Type w') (x : ι → Localization.Away g) (f : List (MvPolynomial ι S)),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) ∧
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) =
        Ideal.ofList f ∧
      ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) :=
  P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.solution s hs H
