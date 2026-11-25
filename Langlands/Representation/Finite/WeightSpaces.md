# Weight spaces of a commuting normal subgroup, and traces of permuted summands

`Langlands.Representation.Finite.WeightSpaces`. For a complex representation `σ` of a finite group `K`
and a subgroup `A` whose image commutes, `W` splits into the weight spaces of `A`; when `A` is normal,
`K` permutes them through its conjugation action on weights. A trace formula for maps that permute
the summands of a direct sum completes the toolkit. These are the representation-theoretic steps of
the monomial case of Brauer's theorem (`MonomialTrace`), and the retained-subgroup variant
`DegreeZeroMonomial` uses them as well.

## Statements

In namespace `Langlands.FiniteRep.WeightSpaces`, with `{K : Type u} [Group K] [Fintype K]`,
`{W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]`, `σ : Representation ℂ K W` and
`A : Subgroup K` (lemmas that do not need `[Fintype K]` or `[FiniteDimensional ℂ W]` do not take them):

- `isSemisimple k`: `Module.End.IsSemisimple (σ k)`; `maxGenEigenspace_eq`: generalized eigenspaces
  of `σ k` are eigenspaces.
- `act σ k : W ≃ₗ[ℂ] W` is `σ k` as an equivalence (`act_apply`, scoped `simp`; `act_symm_apply`);
  `trace_conj`: `trace (σ (x⁻¹ * g * x)) = trace (σ g)`.
- `wt σ A χ : Submodule ℂ W`, for `χ : A → ℂ`, is `⨅ a, maxGenEigenspace (σ a) (χ a)`;
  `mem_wt`: `v ∈ wt σ A χ ↔ ∀ a, σ a v = χ a • v`.
- With `hcomm : ∀ a b : A, σ a * σ b = σ b * σ a`: `isInternal_wt : DirectSum.IsInternal (wt σ A)`.
  `finite_wt`: only finitely many weight spaces are nonzero. `mapsTo_wt_of_comm`: a map commuting
  with every `σ a` preserves each weight space.
- For a weight with `wt σ A χ ≠ ⊥`: `exists_ne_zero_of_ne_bot`, `weight_mul`, `weight_one`,
  `weight_ne_zero`, and the character `weightHom σ A hχ : A →* ℂˣ` (`weightHom_apply`, scoped `simp`).
- For `[A.Normal]`: the scoped instance `weightAction : MulAction K (A → ℂ)`,
  `(k • χ) a = χ ⟨k⁻¹ * a * k, _⟩` (`smul_weight_apply`); `mapsTo_smul`: `σ k` maps `wt σ A χ` into
  `wt σ A (k • χ)`; `map_wt_eq`: onto; `wtEquiv σ A k χ` the resulting linear equivalence
  (`wtEquiv_apply`, `wtEquiv_symm_apply`); `wt_smul_ne_bot_iff`; `trace_restrict_conj`: the trace of
  `σ g` on `wt σ A (k • χ)` equals that of `σ (k⁻¹ * g * k)` on `wt σ A χ`; `mapsTo_of_smul_eq`; and for a
  subgroup `H₁` fixing `χ`, the representation `stabRep σ A χ H₁ hH₁ : Representation ℂ H₁ (wt σ A χ)`
  (`stabRep_apply`).
- Section `Trace`: `mapsTo_of_eq` (transport of `Set.MapsTo` along `j = i`) and

  ```lean
  theorem trace_eq_sum_fixed {ι : Type*} [DecidableEq ι] {N : ι → Submodule ℂ W}
      (h : DirectSum.IsInternal N) (s : Finset ι) (hs : ∀ i, N i ≠ ⊥ → i ∈ s) (π : ι → ι)
      (f : W →ₗ[ℂ] W) (hf : ∀ i, Set.MapsTo f (N i) (N (π i))) :
      LinearMap.trace ℂ W f =
        ∑ i ∈ s, if hi : π i = i then LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi))
          else 0
  ```

## Proofs

`σ k` is annihilated by `X ^ |K| - 1`, which is separable over `ℂ`, hence semisimple, so generalized
eigenspaces are eigenspaces. For a commuting family, Mathlib's simultaneous generalized-eigenspace
decomposition (`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
and `independent_iInf_maxGenEigenspace_of_forall_mapsTo`) gives the internal direct sum. A nonzero
vector of `wt σ A χ` shows that `χ` is multiplicative and nonzero. Conjugation of `a` by `k` moves weight
spaces (`σ a (σ k v) = σ k (σ (k⁻¹ a k) v)`); `wtEquiv` is the restriction of `act σ k`, which gives
`trace_restrict_conj` by conjugation invariance of the trace. For `trace_eq_sum_fixed`, the trace is
computed in the basis collected from bases of the nonzero summands: a basis vector of `N i` with
`π i ≠ i` is sent into another summand and contributes `0` to the diagonal.

## Declarations

In order, all in `Langlands.FiniteRep.WeightSpaces`: theorems `isSemisimple`, `maxGenEigenspace_eq`;
def `act`; theorems `act_apply`, `act_symm_apply`, `trace_conj`; def `wt`; theorems `mem_wt`,
`isInternal_wt`, `mapsTo_wt_of_comm`, `finite_wt`, `exists_ne_zero_of_ne_bot`, `weight_mul`,
`weight_one`, `weight_ne_zero`; def `weightHom`; theorem `weightHom_apply`; instance `weightAction`;
theorems `smul_weight_apply`, `mapsTo_smul`, `map_wt_eq`; def `wtEquiv`; theorems `wtEquiv_apply`,
`wtEquiv_symm_apply`, `wt_smul_ne_bot_iff`, `trace_restrict_conj`, `mapsTo_of_smul_eq`; def `stabRep`;
theorem `stabRep_apply`; (section `Trace`) theorems `mapsTo_of_eq`, `trace_eq_sum_fixed`.

## Source and licence

Adapted from one file of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`), its sections `Rep` and `Trace`; the rest of the file is
in `MonomialTrace`:

| FLT file | SHA-256 |
| --- | --- |
| `P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean` | `910c22f00318287de2d1eb773450fdc51522dfa63ba5df2e50624f908557f3bb` |

The SHA-256 values are those recorded for the FLT files in the evidence appendix of the Library's
audit `notes/reuse/anthropic-brauer-audit.md`.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not list
this file as containing third-party material.

### Changes against the FLT file

- The declarations move from `P2MW.S_…_of_pow_prime_pow_mem.MonomialProof` to
  `Langlands.FiniteRep.WeightSpaces` with their short names unchanged; the scoped attributes and the scoped instance are scoped to the new name space.
- Universes: `K : Type u`, `W : Type v` (FLT: both `Type`), and the index type of `mapsTo_of_eq` and
  `trace_eq_sum_fixed` is `Type*` (FLT: `Type`); the proofs are unchanged.
- `import Mathlib` is replaced by five Mathlib modules. No option is set (FLT: the package options
  `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`, `autoImplicit false`, and four linters off).
- With the linters on, instance arguments that a declaration does not use are omitted
  (`omit … in`): `[FiniteDimensional ℂ W]` from `isSemisimple`, `maxGenEigenspace_eq`, `mem_wt`,
  `mapsTo_wt_of_comm`, `weight_mul`, `weight_one`, `weight_ne_zero`, `weightHom_apply`, `mapsTo_smul`,
  `map_wt_eq`, `wtEquiv_apply`, `wtEquiv_symm_apply`, `wt_smul_ne_bot_iff`, `trace_restrict_conj`,
  `mapsTo_of_smul_eq`, `stabRep_apply`, `mapsTo_of_eq`; `[Fintype K]` and `[FiniteDimensional ℂ W]` from
  `act_apply`, `act_symm_apply`, `trace_conj`, `exists_ne_zero_of_ne_bot`; `[Fintype K]` from
  `smul_weight_apply`. As a consequence the definitions `weightHom`, `wtEquiv` and `stabRep` no longer
  take `[FiniteDimensional ℂ W]`. The statements are otherwise unchanged. One unused `simp` argument is
  removed, an unused binder is written `_`, and one `haveI` is `have`; deprecated names are replaced
  (`dif_pos` → `dite_eq_left`, …).
- Docstrings and this page are added.

## Literature

Jean-Pierre Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977) (literature
`serre-1977-linear-representations`), read in the library copy:

- §7.1, Proposition 19, printed p.55: if `V = ⊕ W_i` with the `W_i` permuted transitively by `G`, then
  `V` is induced from the stabilizer of one `W_i` (monomial when `dim W_i = 1`). `wtEquiv`, `stabRep`
  and `trace_eq_sum_fixed` are the trace form of this for the weight spaces.
- §8.1, Proposition 24, printed p.61: for a normal subgroup `A`, `G` permutes the isotypic components
  of `Res_A ρ`, and either `ρ` is induced from a proper subgroup containing `A` or `Res_A ρ` is isotypic
  (for abelian `A`: `ρ(A)` consists of homotheties). Here the isotypic components of an abelian `A` are
  the weight spaces `wt σ A χ` and the permutation is `weightAction`.
