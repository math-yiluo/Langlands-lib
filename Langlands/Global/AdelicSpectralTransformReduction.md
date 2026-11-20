# Reduction of the unitary spectral transform to its inputs

Module `Langlands.Global.AdelicSpectralTransformReduction` states and proves
`Langlands.Global.SpectralTransformReductionStatement`:

```
ImaginaryIntertwiningExistenceStatement → SymmetricFamilyDensityStatement →
  EisensteinImaginaryContinuationStatement → SymmetricFamilyGramStatement →
  WavePacketTranslationStatement → SpectralTransformStatement
```

The premises S1, S2, S3', S3, S4 are the propositions of
`Langlands.Global.AdelicSpectralTransformInputs` (see its Markdown for their
content and sources). The conclusion is the published
`Langlands.Global.SpectralTransformStatement` (Arthur 2005, Theorem 7.2 (b);
Getz–Hahn (10.22)–(10.24)), unchanged. The proof is
`Langlands.Global.spectralTransformReduction`. It does not prove
`SpectralTransformStatement`: it isolates the analytic input (existence of the
operators, density, Eisenstein continuations, the Gram identity of wave packets,
translation of wave packets) from the Hilbert space argument that assembles the
spectral transform, which is carried out here in full. The module also proves
general lemmas about Hilbert spaces and `Lp` spaces, and the closedness and
completeness of Arthur's space `L̂`.

## General lemmas

Section `Hilbert` (types `S`, `V`, `H`; `V`, `H` complex inner product spaces):

- `exists_linearIsometry_of_inner_eq`: if `φ : S → V` spans a dense subspace,
  `H` is complete, and `W : S → H` satisfies `⟪W s, W s'⟫ = ⟪φ s, φ s'⟫` for all
  `s, s'`, there is a linear isometry `Ē : V →ₗᵢ[ℂ] H` with `Ē (φ s) = W s`.
  Proof: the linear combination maps `ℂ^{(S)} → V` and `ℂ^{(S)} → H` have equal
  inner products, hence equal norms; the first has dense range
  (`Finsupp.range_linearCombination`), and `LinearMap.extendOfIsometry` extends
  the second through it.
- `isClosed_range_linearIsometry`: the range of a linear isometry out of a
  complete space is complete, hence closed.
- `range_invariant_of_generators`: if the range of `Ē` is closed, `φ` spans a
  dense subspace and a bounded operator `R` maps every `Ē (φ s)` into the
  closure of the range, then `R` preserves the range. Proof: the preimage
  `{x | R (Ē x) ∈ range Ē}` is a closed subspace containing every `φ s`.

Sections `Intertwined` and `IntertwinedFamily`:

- `isClosed_setOf_ae_intertwined`: for `A : α → E →L[ℂ] E'`, a map
  `τ : α → β` with `Tendsto τ (ae ma) (ae nb)` and `ae ma ≤ ae ma1`, the pairs
  `(f, f') ∈ Lq(ma1) × Lq(nb)` with `f'(τ x) = A x (f x)` for `ma`-almost every
  `x` form a closed set. Proof: sequential closedness, passing to almost
  everywhere convergent subsequences of both components
  (`tendstoInMeasure_of_tendsto_Lp`, `exists_seq_tendsto_ae`).
- `isClosed_setOf_forall_ae_intertwined`: the same for families indexed by
  `i, i', t`, as preimages under continuous maps `Z → Lq`.

Sections `Assembly` and `AssemblySubmodule`:

- `exists_linearIsometry_of_wavePackets`: let `V` be a Hilbert space, `D ⊆ V`
  span a dense subspace, `Rel : V → (X → ℂ) → Prop` a relation with
  (i) every `Φ ∈ D` related to some `f`; (ii) related functions square
  integrable with `∫ conj (f x) * f' x ∂m = ⟪Φ, Φ'⟫` whenever `Rel Φ f`,
  `Rel Φ' f'`; (iii) maps `τ y : X → X` preserving `m`; (iv) for `Rel Φ f`,
  every `y` and `ε > 0` some `Rel Φ' f'` with
  `eLpNorm (fun x => f (τ y x) - f' x) 2 m < ε`. Then there is
  `Ē : V →ₗᵢ[ℂ] L²(X, m)` with `Ē Φ = f` almost everywhere whenever `Rel Φ f`,
  closed range, and for every `g` in the range and every `y` some `g'` in the
  range equal almost everywhere to `x ↦ g (τ y x)`. Proof: apply
  `exists_linearIsometry_of_inner_eq` to the related pairs (the `L²` inner
  product of the classes is the integral in (ii), `MeasureTheory.L2.inner_def`);
  the related vectors contain `D`, so they span a dense subspace; the range is
  closed by `isClosed_range_linearIsometry`; with
  `R = Lp.compMeasurePreservingₗᵢ ℂ (τ y)`, (iv) puts `R (Ē Φ)` in the closure
  of the range for every related `Φ`, and `range_invariant_of_generators`
  concludes.
- `exists_linearIsometry_of_wavePackets_submodule`: the same lemma for a
  complete subspace `V` of an inner product space `E`, with the inner product
  of (ii) computed in `E`. It is the previous lemma applied to `V`; the main
  proof uses this form.

## Arthur's space

Section `Families`, in the data of the target:

- `isClosed_symmetricFamilySpace`: `L̂ = symmetricFamilySpace … T cw π hw Mop`
  is closed in `spectralFamilySpace`. It is
  `isClosed_setOf_forall_ae_intertwined` for the coordinate maps
  `Φ ↦ Φ i` (continuous, `PiLp.continuous_apply`), the coordinate changes
  `x ↦ (e i')⁻¹ (realWeylParameter (l i) (cw i i' t) (π i') (e i x))` and the
  operators `Mop i i' t x`. The null sets of the scaled measures
  `(nP i)⁻¹ • spectralMeasure (n i)` and of `spectralMeasure (n i)` are those
  of Lebesgue measure (`ae_spectralMeasure_eq`, `ae_smul_spectralMeasure_eq`),
  and `hw` makes the coordinate changes quasi measure preserving.
- `completeSpace_symmetricFamilySpace`: `L̂` is complete, as a closed subspace
  of the complete space `spectralFamilySpace` (each `H_{P i}` is an `L²` space).

## Proof of the reduction

`spectralTransformReduction` introduces S1–S4 and the data of the target.

1. Part 1 of the target: `choose` applied to S1 for each pair `(i, i')` and
   `t`, with the data `(P i, M i, U i)`, `(P i', M i', U i')`,
   `(w i i' t, cw i i' t)` and `hw i i' t`, gives the family `Mop`.
2. Part 2: fix `Mop` with `IsImaginaryIntertwiningOperator`. `L̂` is complete
   (`completeSpace_symmetricFamilySpace`). Right translation: for
   `y ∈ G(𝔸)`, the map `z ↦ mk (z.out * y)` on `G(F) \ G(𝔸)` is
   `LeftCosetSpace.rightTranslate (rationalSubgroup F G) y`
   (`rightTranslate_mk` and `Quotient.out_eq`), which preserves `μG` by
   `LeftCosetSpace.measurePreserving_rightTranslate_discrete`; the
   unimodularity of `G(𝔸)` it needs is the published
   `adelicHaarUnimodularity` (module
   `Langlands.Global.AdelicHaarUnimodularityProof`).
3. Apply `exists_linearIsometry_of_wavePackets_submodule` with `E` the space
   `spectralFamilySpace`, `V = L̂`, `X = G(F) \ G(𝔸)`, `m = μG`, `D` the smooth
   compactly supported families of `L̂` (dense by S2), `τ y = rightTranslate y`,
   and `Rel Φ f`: there are `k, v, c, E, D` with
   `IsSmoothCompactFamily … k v c Φ.1`, `IsEisensteinContinuation` for every
   `i`, and `f = wavePacketSum e nP c E`. Its hypotheses:
   - (i) for `Φ ∈ D` with representation `(k, v, c)`, S3' applied to each
     `v i` (square integrable by `IsSmoothCompactFamily`) gives `E i`, `D i`;
   - (ii) is S3;
   - (iii) is step 2;
   - (iv) is S4.
4. The resulting `Ē` gives part 2: density is S2; the formula clause holds
   because the target's conditions on its continuations `E i j` with domain
   `D i` are `IsEisensteinContinuation`, so `(Φ, wavePacketSum e nP c E)` is
   related, and `wavePacketSum` evaluates at `y.out` as the target's formula
   does; closedness and invariance of the range are the remaining conclusions
   of the lemma.

## Notes

- The main theorem and the closedness and completeness lemmas set
  `synthInstance.maxHeartbeats 400000` (instance search on the families of
  induced Hilbert spaces); the rest uses default limits.
- The general lemmas take the vector space and the subspace explicitly; with
  the space left implicit, unification was very slow.
