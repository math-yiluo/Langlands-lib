# Exactness of the general-linear derivatives: proof

Author: Worker 237.

This module proves the published proposition
`Langlands.Derivative.GeneralLinearDerivativeExactnessStatement.{uF, uV} F T`
of `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement`,
with the theorem

```
theorem Langlands.Derivative.generalLinearDerivativeExactness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GeneralLinearDerivativeExactnessStatement.{uF, uV} F T
```

The level parameters are `uF, uV`, in that order, and they are independent. The
theorem adds no premise. It covers every supplied nontrivial continuous unitary
additive character `ψ`, every rank `N` and every order `k ≤ N`, including
`N = 0`, `k = 0`, `k = N` and `N = 1`. For each of them,
`generalLinearDerivative T ψ N k hk` sends a short exact sequence of actual
intertwiners in `SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)` to one in
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N - k) F.Carrier)`. Short exactness means an
injective underlying map, range equal to kernel, and a surjective underlying map, as
in `Mirabolic.MapsShortExactIntertwiners`.

## Source of minus exactness

Exactness of the two determinant-normalized minus functors comes from the published
theorem `Langlands.Derivative.Mirabolic.minusExactness` of
`Langlands.Representation.Derivative.MirabolicMinusExactnessProof`. That theorem
proves `Mirabolic.MinusExactnessStatement.{uF, uV} F T`. It is the independently
accepted and published proof of task `b65bc667-6951-4bd5-82af-10fb7046df7f`
revision 1. This module applies the theorem to the same `F` and `T`, and uses only
two of its clauses:

- clause 3 (`.2.2.1`): every normalized `Mirabolic.psiMinus T n` is exact;
- clause 4 (`.2.2.2`): every normalized `Mirabolic.phiMinus T ψ n` is exact.

The proposition `MinusExactnessStatement` is not a hypothesis of any theorem here,
and this module does not reprove minus exactness.

## Implemented proof

The functors are the published constructions of
`Langlands.Representation.Derivative.Iteration`, used unchanged. The proof follows
their construction equations.

1. **Identity and composition** (reused helpers from `ShortExactFunctorLaws`,
   retaining their `Langlands.Derivative.LevelCalculus` names). The identity functor is exact,
   because `(𝟭 _).map i` is `i`. If `J₁` and `J₂` are exact, so is `J₁ ⋙ J₂`. The
   three conclusions for `J₁` are the hypotheses that `J₂` needs for `J₁.map i` and
   `J₁.map q`, and `(J₁ ⋙ J₂).map f` is `J₂.map (J₁.map f)`. These helpers are
   generic in the groups, with universes `uG, uH, uK` for the groups and a common
   carrier universe `uV`.
2. **Restriction** (`generalLinearRestriction_mapsShortExact`). The restriction
   `generalLinearRestriction T n : GL_(n+1) → P_(n+1)` keeps the underlying map of
   every morphism. Injectivity and surjectivity transfer by the published pointwise
   equation `generalLinearRestriction_map_apply`. The range–kernel equality transfers
   by rewriting both sides with the published
   `generalLinearRestriction_map_toLinearMap`.
3. **Rank transport** (`generalLinearRankCast_mapsShortExact`). For an equality of
   ranks `h : a = b`, the proof eliminates `h` with `subst`. It then rewrites with the
   published `generalLinearRankCast_refl` to get the identity functor and applies
   step 1.
4. **Iterated `Φ⁻`** (`phiMinusIterate_mapsShortExact`). This step is by induction
   on `k`. The case `k = 0` is the identity (`phiMinusIterate_zero`). In the
   successor case, `phiMinusIterate_succ` writes the functor as
   `Mirabolic.phiMinus T ψ (n + k) ⋙ phiMinusIterate T ψ n k`. Clause 4 of
   `minusExactness` makes the first factor exact, and step 1 combines it with the
   induction hypothesis.
5. **Mirabolic derivative** (`mirabolicDerivative_mapsShortExact`). By
   `mirabolicDerivative_eq`, `mirabolicDerivative T ψ n k` is
   `phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`. This is exact by step 4,
   clause 3 of `minusExactness` and composition.
6. **Positive derivative** (`generalLinearDerivativePositive_mapsShortExact`). By
   `generalLinearDerivativePositive_eq`, the functor is
   `generalLinearRestriction T (n + k) ⋙ mirabolicDerivative T ψ n k`, which is
   exact by steps 2 and 5.
7. **Main theorem** (`generalLinearDerivativeExactness`). After `letI := T.topology`
   and introducing `ψ N k hk`, the proof does case analysis on `k`. For `k = 0`,
   `generalLinearDerivative_zero` gives the identity functor (step 1). For `k + 1`,
   `generalLinearDerivative_succ` gives
   `generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙
   generalLinearDerivativePositive T ψ (N - (k + 1)) k`, which is exact by steps 3
   and 6.

The case analysis covers every `N` and `k ≤ N`. The edge cases need no separate
argument: `N = 0` forces `k = 0`, and `k = N`, including `N = 1`, falls into the
successor case. The proof uses the published functor `generalLinearDerivative`
itself, with codomain `GeneralLinear (N - k)`. It does not use the extra
`Nat.sub_self` cast of the published top-derivative equations.

The public theorems of steps 2–6 have the same outer telescope
`{p} [Fact p.Prime] (F) (T)`. The order of the remaining arguments is as in the
corresponding `Iteration` functor: `n` for restriction, `{a b} (h : a = b)` for the
rank transport, and `ψ n k` for steps 4–6. They are unconditional and may be reused
by later work. Each applies to the actual published functor.

## Source and provenance

The registered original is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I*, Ann. Sci. ÉNS (4) 10 (1977), 441–472, source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Pages are
printed numbers, with one-based PDF pages in parentheses. The following passages
were read:

- §3.2, printed pp.450–451 (PDF pages 11–12). Here `Ψ⁻ = r_{V,1}` and
  `Φ⁻ = r_{V,θ}`, and Proposition 3.2(a) states that all the functors `Ψ⁻`, `Ψ⁺`,
  `Φ⁻`, `Φ⁺`, `Φ̂⁺` are exact.
- §3.5, printed p.452 (PDF page 13). For `τ ∈ Alg P_n`, the derivative is
  `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ)` for `k = 1, …, n`, with `(Φ⁻)^m` the composite
  `Alg P_n → … → Alg P_(n-m)` (footnote (2)).
- §4.3, printed p.454 (PDF page 15). For `π ∈ Alg G_n`, `π^(0) = π` and
  `π^(k) = (π|_(P_n))^(k)` for `k = 1, …, n`.

No applicable errata entry was found in the central-library literature index
(`/home/taskhub/pilot/literature/_central-library-pointers.md`), the public notes or
the published `Iteration`, `MirabolicMinus`, `MirabolicMinusExactnessStatement` and
`GeneralLinearDerivativeExactnessStatement` pairs.

### What comes from the source and what is derived

- **Source assertion.** The source asserts that `Ψ⁻` and `Φ⁻` are exact
  (Proposition 3.2(a)). The Library form of this assertion, for the
  determinant-normalized functors, is clauses 3 and 4 of
  `MinusExactnessStatement`. Its proof is the published `minusExactness`, not this
  module.
- **Source definitions.** The derivative is defined as the composite of
  restriction, `(Φ⁻)^(k-1)` and `Ψ⁻`, and the zeroth derivative is the identity
  (§§3.5, 4.3). The Library realizes this composite in `Iteration`.
- **Derived argument.** The cited pages do not state exactness of `π ↦ π^(k)` as a
  numbered result. This module derives it from four facts: the identity is exact;
  exactness is closed under composition; restriction keeps underlying maps; and the
  rank transport is the identity after eliminating the equality. These four facts,
  and the induction over the iterate, are internal arguments, not quotations.
- **Internal packaging.** Two choices are internal Library conventions rather than
  source constructions. Exactness is expressed as `MapsShortExactIntertwiners`, using
  injectivity, range = kernel and surjectivity of underlying maps. The derivative is
  indexed by source rank `N`, order `k ≤ N` and rank cast `generalLinearRankCast`.

The Library normalizes `Ψ⁻` and `Φ⁻` by fixed determinant-character twists, where
the source uses `mod_V^(-1/2)`. This proof only uses the exactness that
`minusExactness` proves for the normalized functors. It does not identify the
determinant character with a Haar modulus.

## Imports and independence

The direct imports are the unchanged statement module
`Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement`,
the published proof module
`Langlands.Representation.Derivative.MirabolicMinusExactnessProof`, and
`Langlands.Representation.Derivative.ShortExactFunctorLaws`.
The original 70 dependencies remain byte-identical to Library commit
`9a8ca758097242bde4147f33304f43fceef22fa4`. They are the union of the statement's
closure (54 modules including the statement) and the minus-exactness proof's
closure (68 modules including that proof), which share 52 modules. Integration
adds only `ShortExactFunctorLaws`, for 71 dependencies excluding this module.
That helper imports only the already present minus-exactness statement and
retains the existing identity/composition lemmas with independent group universes.

Besides the derivative modules above, the closure consists of modules on groups,
local fields, smooth representations, twists, compact averaging, coinvariants and
localization exactness, matrix coefficients, Whittaker characters and unipotent
unimodularity. `Representation/Dual/Definitions` only builds algebraic dual maps of
intertwiners and states no duality theorem. The closure contains no segment,
multisegment, socle, classification, square-integrable, tempered, plus-functor,
adjunction, filtration, Leibniz, pairing, irreducibility-criterion or commutation
module. No Lean source in the closure mentions
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`, `UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` or
`SegmentSocleProductIrreducibility`. No result of the excluded exhaustion,
existence, coverage, conversion, uniqueness, socle-commutation, gluing or
segment-classification tasks is used.

The published `Langlands.Representation.Derivative.LevelCalculus` contains
analogous conditional exactness lemmas that take `MinusExactnessStatement` as a
hypothesis. It serves the segment-socle homogeneity route, so this module neither
imports nor uses that module. Its existing identity and composition lemmas were
extracted unchanged into `ShortExactFunctorLaws`, preserving their public names.
Both proofs now reuse that shared module without introducing any dependency on
derivative detection or the segment-socle route.

## Development validation

The module was compiled with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library base `9a8ca758`, with no errors
or warnings. Declaration inspection of `generalLinearDerivativeExactness` reports
kind `theorem`, level parameters `uF, uV`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. A private check printed its type as
`∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (F : PadicField p) (T : F.TopologicalData),
GeneralLinearDerivativeExactnessStatement F T`. It also confirmed that the
universe-explicit term `generalLinearDerivativeExactness.{uF, uV} F T` has type
`GeneralLinearDerivativeExactnessStatement.{uF, uV} F T`. No `sorry`, `admit` or new
axiom is used. These checks are separate from independent review and publication.

This module proves no parent irreducibility criterion, derivative filtration,
Leibniz rule or other consumer statement.
