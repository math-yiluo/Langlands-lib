# Reduction of segment-pair L compatibility to supercuspidal pairs

Author: Worker 1706.

This module is a second conditional step toward
`Langlands.Correspondence.AssemblyLInheritanceStatement`
(`AssemblyLFactorStatement`). The first step, module `AssemblyLReduction`,
reduces the target to four premises; one of them is segment-level L inheritance
`SupercuspidalSegmentPairLInheritance`. This module derives that premise, and
then the target, from three further premises:

- the L-factor formula of Henniart 2002, §2.6, for pairs of segment heads, the
  published statement `RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}`;
- the corresponding product formula for arithmetic L-factors of pairs of
  uncentered special blocks (`ArithmeticBlockPairLFactor`);
- compatibility of the supercuspidal correspondence with pair L-factors after
  twisting the first factor by `ν^x`, `x ∈ ℕ`
  (`SupercuspidalTwistedPairLInheritance`).

**None of these premises is proved here, and the module does not prove the
target statement.** The final theorem has the target statement as its
conclusion, but it keeps the premises of both modules as hypotheses.

All definitions and theorems are in namespace `Langlands.Correspondence`.
Throughout, `F : PadicField.{uF} p` and `[Fact p.Prime]`. The universes are
those of the target: Weil–Deligne carriers in `uP`, automorphic carriers in `uA`.
Write `ω` for `(Weil.Local.localNormCharacter F).toMonoidHom`, the norm
character of the Weil group (Henniart's `ν` on `W_F`), and `ν_n` for
`F.canonicalTopologicalData.determinantNorm n`, the character `|det|` of
`GL_n(F)`. Under geometric normalization `ω` sends a geometric Frobenius to
`q⁻¹ = |ϖ|`, so `ω` and `|·|` correspond.

## Definitions

### `ArithmeticBlockPairLFactor.{uF, uP} F`

For all local Weil representations `B`, `B'` (carriers in `uP`) and `a b : ℕ`,

`arithmeticPairLFactor F [block ω B (a + 1)] [block ω B' (b + 1)]
  = ∏ j : Fin (min (a + 1) (b + 1)),
      arithmeticPairLFactor F [zeroMonodromy ω (twist (ω ^ (a + b - j)) B)]
        [zeroMonodromy ω B']`

in `RatFunc ℂ`. Here `[·]` is `WeilDeligneRepresentation.classOf`,
`WeilDeligneRepresentation.block ω B (a + 1)` is the published uncentered special
block `B ⊗ Sp(a + 1)` used by `IsBlockSum`, `zeroMonodromy ω C` is the
Weil–Deligne representation with Weil part `C` and monodromy `0`, and
`FiniteRepresentation.twist` is the twist by a character. The subtraction `a + b - j` is in `ℕ`; it is exact, since
`j ≤ min a b`.

### `TwistedSupercuspidalPairLCompatibility F c0`

Take the following data:

- a nontrivial `ψ` and a self-dual `ν`;
- irreducible Weil classes `σ` of rank `d + 1` and `τ` of rank `t + 1`, with
  representatives `B` and `B'`;
- supercuspidal representations `A` of `GL_(d+1)(F)` and `A'` of `GL_(t+1)(F)`
  (carriers in `uA`) with `A.isoClass = c0 σ` and `A'.isoClass = c0 τ`;
- `x : ℕ`.

Then one polynomial `P : ℂ[X]` does both of the following:

- `RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν (ν_(d+1)^x A) A' P` holds,
  where `ν_(d+1)^x A` is `realPowerTwist (ν_(d+1)) x A`; that is,
  `L(s, ν^x A × A') = 1 / P(q^(-s))`;
- `arithmeticPairLFactor F [zeroMonodromy ω (twist (ω ^ x) B)]
  [zeroMonodromy ω B']` equals `(algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹`.

### `SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F`

Every supercuspidal map `c0` with `IsSupercuspidalCorrespondence F c0` satisfies
`TwistedSupercuspidalPairLCompatibility F c0`.

## Theorems

```lean
theorem isPadicRankLPolynomial_congr_equiv
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}
    {ν : LocalAdditiveHaarMeasure F} {n t : ℕ} {V W V₂ W₂ : Type*} …
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear t F.Carrier) W}
    {π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂}
    {σ₂ : Representation ℂ (GeneralLinear t F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {P : ℂ[X]} :
    RankinSelberg.IsPadicRankLPolynomial F ψ ν π σ P ↔
      RankinSelberg.IsPadicRankLPolynomial F ψ ν π₂ σ₂ P
```

The arbitrary-rank L relation is invariant under equivalences of both
representations; the carriers may lie in different universes. Proof: when both
ranks are positive this is the published
`RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv`; when one rank is `0`
both sides are `False`.

```lean
theorem segmentPairLCompatibility_of_segmentHeads
    {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : TwistedSupercuspidalPairLCompatibility F c0) :
    SegmentPairLCompatibility F c0
```

Proof as implemented. Fix `ψ`, `ν`, `σ`, `τ`, `B`, `B'` and segment head models
`Q`, `Q'` of `Δ = segmentOf F c0 σ a` and `Δ' = segmentOf F c0 τ b`.

1. `IsSegmentHeadModel` gives `n = Δ.degree`, a head `P0` of `Δ` with carrier in
   `max uF uA`, and an equivalence `e` from `Q` to `P0`; likewise `P0'` and `e'`.
   After substituting the rank equalities, `IsSegmentHead` gives supercuspidal
   representatives `A` of `c0 σ` and `A'` of `c0 τ`.
2. `hH`, applied to `ψ`, the self-dual measure `⟨ν, hνψ⟩`, `Δ`, `Δ'`, `P0`,
   `P0'`, `A` and `A'`, gives `P` with
   `IsPadicRankLPolynomial F ψ ν P0 P0' P`, polynomials `R j` for
   `j : Fin (min (a + 1) (b + 1))` with
   `IsPadicRankLPolynomial F ψ ν (ν_(d+1)^((a+1) + (b+1) - 2 - j) A) A' (R j)`,
   and `P = ∏ j, R j`. Transport along `e.symm` and `e'.symm`
   (`isPadicRankLPolynomial_congr_equiv`) makes `P` the L-polynomial of
   `(Q, Q')`.
3. `hB` rewrites the arithmetic L-factor of the two special blocks as the
   product over `j` of the factors of `ω^(a+b-j) B` and `B'`; `P = ∏ j, R j`,
   `map_prod` and `Finset.prod_inv_distrib` rewrite the inverse of the image of
   `P` as the product of the inverses of the images of `R j`.
4. For each `j`, `hT` at `x = a + b - j` gives `P_j` that is the L-polynomial of
   `(ν^(a+b-j) A, A')` and whose inverse is the arithmetic factor of
   `ω^(a+b-j) B` and `B'`. Since `j < min (a + 1) (b + 1)`, the real exponent
   `(a + b - j : ℕ)` equals `(a + 1) + (b + 1) - 2 - j`
   (`Nat.cast_sub`, `push_cast`, `ring`). Uniqueness of the rank L-polynomial
   (`RankinSelberg.IsPadicRankLPolynomial.unique`, with
   `RankinSelberg.isPadicRankLPolynomial_succ`) gives `P_j = R j`, so the
   factors agree.

```lean
theorem supercuspidalSegmentPairLInheritance_of_segmentHeads
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F) :
    SupercuspidalSegmentPairLInheritance.{uF, uP, uA} F
```

This applies the previous theorem to `hT c0 hc0` for every supercuspidal
correspondence `c0`.

```lean
theorem assemblyLInheritance_of_segmentHeads
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F
```

This combines `assemblyLInheritance_of_segmentPairs` (module
`AssemblyLReduction`) with the previous theorem. The six hypotheses are the
remaining premises of the target.

## Provenance

The three new premise definitions are derived internal formulations. They
support the reduction and are not new literature claims. Each corresponds to a
step of Henniart 2002 (`henniart-2002-characterization`):

- `ArithmeticBlockPairLFactor`. Henniart 2002 §2.4 (printed p.594, PDF p.8)
  states, for `ρ`, `ρ'` irreducible and `n, n' ≥ 1`,
  `L(s, (ρ ⊗ St_n) ⊗ (ρ' ⊗ St_n')) = ∏_j L(s, ν^(n+n'-1-j) ⊗ ρ ⊗ ρ')` for `j`
  from `1` to `inf(n, n')`. With `n = a + 1`, `n' = b + 1` and Henniart's `j`
  equal to `j + 1` for our `j : Fin (min (a + 1) (b + 1))`, the exponent is
  `a + b - j`. The premise states this for the published uncentered blocks
  `block ω B (a + 1)`, with arbitrary representatives `B`, `B'`, and writes
  the factors `ν^k ⊗ ρ ⊗ ρ'` as pair factors of the zero-monodromy Weil–Deligne
  representations `ω^k B` and `B'`.
- `TwistedSupercuspidalPairLCompatibility`. Henniart 2002 §2.7 (printed
  p.595, PDF p.9) deduces `L(s, π_2(σ) × π_2(σ')) = L(s, σ ⊗ σ')` "from 2.4 and
  2.6"; comparing the two products uses
  `L(s, ν^k π_0(ρ) × π_0(ρ')) = L(s, ν^k ρ ⊗ ρ')` for `k ≥ 0`. The premise
  states this for the supercuspidal map `c0`, all representatives and every
  self-dual measure. It follows from the twist and factor compatibilities in
  `IsSupercuspidalCorrespondence` (`SupercuspidalTwistCompatibility` with the
  character `|·|^x`, and `SupercuspidalFactorCompatibility`). That derivation
  is not in this module; module `AssemblyLTwistedSupercuspidal` carries it out.
- `SegmentHeadLFactorStatement` is a published Library statement (Henniart 2002
  §2.6, printed p.595, first display), used here as a hypothesis at universes
  `{uF, uA, uA}`. Its index `j` is Henniart's `j - 1`, so its exponent
  `(a + 1) + (b + 1) - 2 - j` is Henniart's `n + n' - 1 - j`.

The theorems are derived: they compose the premises with the published
uniqueness and equivalence invariance of the pair L relation. No L-factor
formula is proved here; each is assumed only as one of the named premises.
