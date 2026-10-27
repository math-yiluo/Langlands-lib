# Proof of mixed-scalar separation of ideal tensor kernels

This module proves the published proposition
`Langlands.Algebra.IdealTensorKernelSeparationStatement.{u,v,w}`, imported by
Lean module name from `Langlands.Algebra.IdealTensorKernelSeparationStatement`.
It does not change that statement pair or anything it imports. The closing
theorem is `Langlands.Algebra.idealTensorKernelSeparation.{u,v,w}`. Its entire
type is `IdealTensorKernelSeparationStatement.{u, v, w}`, with three independent
universes and no further hypotheses or parameters.

## Helper results

Both helpers are in the namespace
`Langlands.Algebra.IdealTensorKernelSeparationProof`. They are stated for
`R : Type u`, `S : Type v`, `M : Type w`, commutative rings `R` and `S`, an
algebra `R → S`, and an additive group `M` with compatible `R`- and
`S`-module structures, `[IsScalarTower R S M]`. Neither helper needs a
Noetherian hypothesis.

- `finite_tensor` takes an `R`-module `N` with `[Module.Finite S M]` and
  `[Module.Finite R N]`. It proves `Module.Finite S (M ⊗[R] N)`, where
  `M ⊗[R] N` carries Mathlib's `S`-module structure from the left factor.
  Mathematically: if \(M\) is finite over \(S\) and \(N\) is finite over
  \(R\), then \(M\otimes_R N\) is finite over \(S\).
- `pow_smul_top_le` takes an ideal `I : Ideal R`, `n : ℕ`, and an additive
  group `P` with compatible `R`- and `S`-module structures,
  `[IsScalarTower R S P]`. It proves
  `(I ^ n • ⊤ : Submodule R P) ≤ ((I.map (algebraMap R S) ^ n • ⊤ :
  Submodule S P).restrictScalars R)`. With \(J=IS\), this is
  \(I^nP\subseteq J^nP\).

## Implemented proof

`finite_tensor`. `Module.Finite.exists_fin'` gives `n : ℕ` and a surjective
`R`-linear map `f : (Fin n → R) →ₗ[R] N`. The `S`-linear equivalence
`TensorProduct.piScalarRight R S M (Fin n)` identifies
`M ⊗[R] (Fin n → R)` with `Fin n → M`. That product is finite over `S`, so
`Module.Finite.equiv` makes `M ⊗[R] (Fin n → R)` finite over `S`. The
`S`-linear map `TensorProduct.AlgebraTensorModule.lTensor S M f` has the same
underlying function as `LinearMap.lTensor M f`. That function is surjective
by `LinearMap.lTensor_surjective`. `Module.Finite.of_surjective` therefore
gives finiteness of `M ⊗[R] N` over `S`.

`pow_smul_top_le`. By `Submodule.smul_le` it is enough to show `r • y` lies
in the right side when `r ∈ I ^ n` and `y : P`. The scalar tower rewrites
`r • y` as `algebraMap R S r • y` (`algebraMap_smul`). Now
`Ideal.mem_map_of_mem` and `Ideal.map_pow` put `algebraMap R S r` in
`I.map (algebraMap R S) ^ n`, and `Submodule.smul_mem_smul` with
`Submodule.mem_top` concludes.

`idealTensorKernelSeparation`. After introducing the data, the Jacobson
premise `hJ` and the kernel-bound premise `hker`, the proof rewrites flatness
by `Module.Flat.iff_lTensor_injective'`. It remains to show that
`LinearMap.lTensor M a.subtype` is injective for every ideal `a`. Since `R`
is Noetherian, `a` is finite over `R`; this is found by instance search.
Then `finite_tensor` gives `Module.Finite S (M ⊗[R] a)`. By
`injective_iff_map_eq_zero` it suffices to show that each kernel element `x`
is zero. For each `n`, `hker a n` puts `x` in the `R`-submodule
`I ^ n • ⊤`, and `pow_smul_top_le` moves it into the `S`-submodule
`I.map (algebraMap R S) ^ n • ⊤`. Hence `x` lies in the infimum over all `n`
of these `S`-submodules (`Submodule.mem_iInf`). Krull's intersection theorem
in the form `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` uses that `S` is
Noetherian, that `M ⊗[R] a` is finite over `S`, and `hJ`. It shows that this
infimum is `⊥`. Thus `x = 0` by `Submodule.mem_bot`.

The Noetherian hypothesis on `R` is used only for finiteness of the ideals
`a`. The Noetherian hypothesis on `S` and the Jacobson premise are used only
in Krull's intersection theorem. Finiteness of `M` over `S` is used only in
`finite_tensor`. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Sources and attribution

The route is that of the final paragraph of the proof of Stacks Project
Lemma 10.99.7, tag [00MK](https://stacks.math.columbia.edu/tag/00MK). It uses
finiteness of the ideal tensor product over \(S\) and Krull separation to
make the kernel, which lies in every power of the ideal, zero. That passage
was read in registered source `stacks-algebra-flatness-criteria-2026-10-22`,
content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00MK.html`. The statement pair records the bounded current-page check
`stacks-flatness-00mk-00mj-current-2026-10-26`; no source-specific errata note
is present in the project or Library notes. Stacks Lemma 10.99.6, tag 00MJ,
and the derivation of the power bounds are not used here: the bounds are a
premise.

The implementation follows the outline in the external lead
`finite_lTensor_ideal` and the end of `flat_of_torVanish_pow`, namespace
`P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime`,
file `P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`.
It is in registered source `anthropic-flt-complete-lean-source-6e837e75`,
content SHA256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, revision
`6e837e75355538c7f80bab5b956861e86c4eacc2`; that source is Copyright 2026
Anthropic, PBC, under Apache-2.0. No code was extracted from it. Worker 735
wrote this proof independently, and its Lean text differs from the source.
The source proves finiteness by an explicit span induction over product
generators. This module instead pushes a finite free presentation forward
along `piScalarRight`. It also replaces the source's element induction for the
power transport with `Submodule.smul_le`. Neither the external source nor
`P2M.Util` is imported.
