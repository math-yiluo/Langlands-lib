# Second adjointness on Levi points from the literal Levi image

Lean module: `Langlands.Representation.Exponents.LeviSecondAdjointnessTransport`. The
generic lemma is in namespace `Langlands.Aubert.General`, the represented-parabolic
corollary in `Langlands.Aubert.General.RepresentedParabolic`.

## Provenance

Internal infrastructure for Renard 2026, VI.9.6 Theorem (VI.9.6.1) (printed p.201, PDF
p.207). The Library states (VI.9.6.1) for represented parabolics
(`RepresentedParabolic.LeviSecondAdjointnessStatement`) with functors on smooth
representations of `M(F)` itself. Those functors are defined from functors on smooth
representations of the literal Levi image `pointImage (m ≫ p)` in `G(F)`:

- `leviInductionFunctor p m n …` is `SmoothRep.pullbackFunctor (leviPointsEquiv p m hp hm).symm`
  followed by `inductionFunctor p m n …`, which is `normalizedInductionFunctor` of the
  decomposition `isSemidirectDecomposition_pointImage`
  (`Exponents/ArbitraryParabolicLeviPoints.lean`, `Exponents/ArbitraryParabolicInduction.lean`);
- `leviJacquetFunctor pbar mbar nbar …` is `normalizedJacquetFunctor` of
  `pointImage (nbar ≫ pbar)` to `pointImage (mbar ≫ pbar)`, followed by
  `SmoothRep.pullbackFunctor (leviPointsEquiv pbar mbar hpbar hmbar)`
  (`Exponents/ArbitraryParabolic.lean`, `jacquetFunctor`).

A second adjunction constructed for abstract closed subgroups of `G(F)` therefore has to be
moved across these pullbacks. Renard does not state this step, because he identifies `M(F)`
with its image in `G(F)`. The module contains only this bookkeeping and no analytic input.
It is the analogue for (VI.9.6.1) of `Aubert/General/ContragredientJacquetTransport.lean`
and `Exponents/LeviJacquetContragredientReduction.lean` for (VI.9.6.2).

## Declarations

### `Langlands.Aubert.General.nonempty_pullback_induction_jacquet_adjunction`

Setting: `G` is a locally compact nonarchimedean topological group (universe `uG`) and `H`
is a topological group in the same universe. The data are

- subgroups `P`, `M₁`, `M₂`, `U` of `G` with `hM : M₁ = M₂`, a semidirect decomposition
  `h : IsSemidirectDecomposition P M₁ U` and `hU : IsClosed U`;
- a closed subgroup `Ubar` (`hUbar`) normalized by `M₂` (`hMUbar₂`);
- isomorphisms of topological groups `e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` with
  `(e₁ x : G) = e₂ x` for all `x` (`he`);
- `hadj`: for every proof `hMUbar₁` that `M₁` normalizes `Ubar`,

  `Nonempty (normalizedInductionFunctor.{uG, max uG uV} h hU ⊣ normalizedJacquetFunctor.{uG, max uG uV} Ubar M₁ hUbar hMUbar₁)`.

The conclusion is

`Nonempty (SmoothRep.pullbackFunctor e₁.symm ⋙ normalizedInductionFunctor h hU ⊣ normalizedJacquetFunctor Ubar M₂ hUbar hMUbar₂ ⋙ SmoothRep.pullbackFunctor e₂)`,

with all functors at universes `.{uG, uG, max uG uV}` or `.{uG, max uG uV}` as in the
Lean statement. In words: if `i_U ⊣ r_{Ū}` on smooth representations of `M₁`, then
`A ↦ i_U((e₁⁻¹)^* A)` is left adjoint to `π ↦ e₂^*(r_{Ū} π)` on smooth representations
of `H`. The two Levi subgroups are kept separate for the same reason as in
`ContragredientJacquetTransport`: for represented parabolics the Levi image for `P` is
`pointImage (m ≫ p)` and the one for `P̄` is `pointImage (mbar ≫ pbar)`. These are equal but
not syntactically the same.

### `Langlands.Aubert.General.RepresentedParabolic.nonempty_leviSecondAdjunction_of_pointImage`

Setting: a field `k` with a Hausdorff topology, an affine group scheme `G` over `k` whose
rational points (with `RationalPointFamily.pointTopology`) are locally compact and
nonarchimedean, and two represented parabolics with the same Levi `M`:

- `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `hp`, `hm`, `hn`, `hmul`;
- `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with `hpbar`, `hmbar`,
  `hnbar`, `hmulbar`;
- `hP : mbar ≫ pbar = m ≫ p`;
- `hadj`: for every proof `hUbar` that `pointImage (nbar ≫ pbar)` is closed and every proof
  `hMUbar` that `pointImage (m ≫ p)` normalizes it,

  `Nonempty (inductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣ normalizedJacquetFunctor.{u, max u v} (pointImage (nbar ≫ pbar)) (pointImage (m ≫ p)) hUbar hMUbar)`.

  This is second adjointness `i_N ⊣ r_{N̄}` between smooth representations of the literal
  Levi image `pointImage (m ≫ p)` and of `G(F)`.

The conclusion, with `M(F)` carrying `leviPointTopology m hm`, is

`Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣ leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar)`,

which is the conclusion of `LeviSecondAdjointnessStatement`. The hypothesis
`P(F) ∩ P̄(F) = M(F)` of that statement and the reductivity and local-field hypotheses are
not used here; they are needed only to prove `hadj`.

## Proof

`nonempty_pullback_induction_jacquet_adjunction`: substitute `hM`, so `M₂` becomes `M₁`.
The isomorphisms `e₁` and `e₂` then have the same target and agree pointwise by `he`, so
`e₁ = e₂` by `ContinuousMulEquiv.ext` and `Subtype.ext`. With an adjunction
`adj : i_U ⊣ r_{Ū}` from `hadj hMUbar₂`, the composite

`(SmoothRep.pullbackEquivalence e₁).symm.toAdjunction.comp adj`

has the required type. Here `SmoothRep.pullbackEquivalence e₁`
(`Aubert/General/CuspidalRemainderTransport.lean`) is the equivalence between smooth
representations of `M₁` and of `H` given by pullback along `e₁`. Its inverse has functor
`pullbackFunctor e₁.symm` and inverse functor `pullbackFunctor e₁`.

`nonempty_leviSecondAdjunction_of_pointImage` applies the generic lemma with

- `Ubar = pointImage (nbar ≫ pbar)`, closed by `isClosed_pointImage_comp pbar nbar …`;
- `M₁ = pointImage (m ≫ p)`, `M₂ = pointImage (mbar ≫ pbar)`, with `hM` from `hP`;
- `h = isSemidirectDecomposition_pointImage p m n …` and
  `hU = isClosed_pointImage_comp p n …`, so that `normalizedInductionFunctor h hU` is
  `inductionFunctor p m n …`;
- `hMUbar₂ = pointImage_le_normalizer pbar mbar nbar hnbar`;
- `e₁ = leviPointsEquiv p m hp hm` and `e₂ = leviPointsEquiv pbar mbar hpbar hmbar`.
  They agree in `G(F)` by `leviPointsEquiv_apply_coe` and `hP`;
- `hadj hUbar` for the remaining hypothesis.

The resulting functors are `leviInductionFunctor p m n …` and
`leviJacquetFunctor pbar mbar nbar …` by definitional unfolding.

## Use

With this theorem, `LeviSecondAdjointnessStatement` reduces to second adjointness for the
subgroups `pointImage (m ≫ p)`, `pointImage (n ≫ p)` and `pointImage (nbar ≫ pbar)` of
`G(F)`. That is a statement about normalized induction and normalized Jacquet functors of
closed subgroups. It can be proved with the generic chain lemmas of
`Category/ChainUnitAdjunction.lean`, without the Levi pullbacks.
