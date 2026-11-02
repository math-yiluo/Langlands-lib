# A head shift excluded by the ordering of a cuspidal product

Author: Worker 1166. The interface of `headShift_false` was fixed by Worker 818,
first executor of proof task `451717b1-3d17-41d3-81e7-29b78f0b6112`. Worker 818
also revised the `j = i0` step to use Worker 1168's
`OrderedCuspidalProductTwistOne`.

This is an internal helper of the proof of Bernstein–Zelevinsky 1977, Theorem
4.11 (sufficient direction), in module
`Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`.
It is not a translation of a separate literature statement. It isolates one
step of Case 2 of BZ77 §4.15 (printed pp. 458–459): if the highest derivative
of a submodule embeds in one block `ρ_{i₀}`, then Lemma 4.7(b) forces
`ν ρ_{i₀}` to be one of the blocks. Here `ν = |det|^1` is the published
residue-normalized real power twist. The module states and proves two
theorems in namespace `Langlands.Derivative.OrderedCuspidalProductHeadShift`.

## Exact scope

Fix a prime `p`, `F : PadicField.{uF} p` and topological data `T`, with
`letI := T.topology`.

`irreducible_support_of_injective` takes `d m : ℕ`, `hd : 0 < d` and
`h : d = m`. Let `A` be an actual supercuspidal representation of `GL_d(F)` in
universe `uV`, and `X` a nontrivial smooth representation of `GL_m(F)` with
carrier in `Type (max uF uV)`. Let
`g : X ⟶ (generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} A.obj)`
be a morphism with injective underlying map. Then `X.IsIrreducible`, and
`T.IsSupercuspidalSupport X {⟨d, hd, A.isoClass⟩}` holds, the support being
the singleton multiset of the cuspidal datum of `A`.

`headShift_false` takes a unitary additive character `ψ`, `N : ℕ`, a block
shape `B : BlockShape (N + 1)`, actual supercuspidal blocks
`A i` of rank `B.size i`, and an index `i0`. Its hypotheses are:

- for every `j ≠ i0`, the rank-indexed class `⟨B.size j, (A j).isoClass⟩` is
  different from
  `⟨B.size i0, T.supercuspidalClassRealPowerTwist (B.size i0) 1 (A i0).isoClass⟩`;
- `f : W ⟶ (generalLinearRestriction T N).obj Π` with injective underlying
  map, where `Π = (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)`
  and `W` is a smooth representation of the mirabolic subgroup `P_{N+1}`;
- `k` with `0 < k ≤ N + 1` and `level T ψ W = k`;
- `hsz : B.size i0 = N + 1 - k`, and a morphism
  `g : (mirabolicDerivativeOfOrder T ψ N k hk).obj W ⟶
  (generalLinearRankCast T hsz).obj (SmoothRep.universeLift.{uF} (A i0).obj)`
  with injective underlying map;
- the derivative `(mirabolicDerivativeOfOrder T ψ N k hk).obj W` is
  `Nontrivial`.

The conclusion is `False`. The hypothesis on `i0` concerns only the blocks
`j ≠ i0`. The case `j = i0` is excluded by the helper theorem
`Langlands.Derivative.OrderedCuspidalProductTwistOne.twist_one_ne_self`
(`ν ρ ≠ ρ` for every cuspidal datum). The consuming proof derives the hypothesis
on `i0` from the ordering hypothesis of Theorem 4.11.

## Implemented proof

`irreducible_support_of_injective`. Equality elimination on `h` removes the
rank cast. The lifted object `L = SmoothRep.universeLift.{uF} A.obj` is
irreducible by `SmoothRep.isIrreducible_universeLift_iff` and the
irreducibility component `A.property.1`. Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` shows that the
intertwiner underlying `g` is surjective or zero. It is not zero, because it
is injective and `X` has a nonzero vector. So `g` is bijective, and
`IntertwiningMap.ofBijective` gives an equivalence `e : X ≃ L`.
`Langlands.isIrreducible_iff_of_equiv` transports irreducibility from `L` to
`X`.

For the support, take the one-entry family `ρ1 = fun _ => ⟨d, hd, A.isoClass⟩`
and the constant block family `A`. The published equivalence
`singleBlockNormalizedProductEquiv` for the one-block shape
`T.cuspidalShape ρ1 _` identifies `T.cuspidalProductInduced ρ1 _ (fun _ => A)`
with `A.obj`. The identity reindexing `GL_d → GL_d` is checked entrywise, and
`SmoothRep.universeLiftEquiv` gives the next step to `L`. Composing with
`e.symm` gives a surjective intertwiner from the product onto `X`. So `X` is a
quotient, hence a subquotient, of the one-block cuspidal product. This is a
witness of `IsSupercuspidalSupport` for the singleton multiset. The pattern
follows `Classification.TwoSupercuspidalTopDerivatives.supercuspidal_singleton_support`
(Library). That module is not imported, so its import closure does not
enter this proof.

`headShift_false`. Write `σ` for the derivative of order `k` of `W`. The
first theorem, applied to `g`, makes `σ` irreducible, with singleton support
`{ρ i0}`. Here `ρ i = ⟨B.size i, B.positive i, (A i).isoClass⟩`. The family
satisfies `∑ i, (ρ i).rank = N + 1` by `B.sum_eq`, and each `ρ i` is
represented by `A i` by reflexivity. `T.cuspidalShape ρ _` agrees with `B`
definitionally (structure eta), so `f` already has the codomain the published
lemma expects. The published Lemma 4.7(b) theorem
`Langlands.Classification.cuspidalProductMirabolicSupportShift` is applied to
`ψ, N, B.length, ρ, A, W, f, k` and to `σ` itself. The latter is an
irreducible subrepresentation of the derivative through the identity
intertwiner. The lemma gives
`{ρ i0}.map (twist 1) ≤ List.ofFn ρ`, that is, some `j` has
`ρ j = (ρ i0).twist 1`.

- If `j = i0`, then `hj.symm : (ρ i0).twist 1 = ρ i0` contradicts
  `OrderedCuspidalProductTwistOne.twist_one_ne_self T (ρ i0)`, a
  central-character argument (Worker 1168) in the helper module
  `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne`.
- If `j ≠ i0`, apply `congrArg` to the map `c ↦ ⟨c.rank, c.cls⟩` into the
  rank-indexed sigma type. This turns the equality into
  `⟨B.size j, (A j).isoClass⟩ =
  ⟨B.size i0, T.supercuspidalClassRealPowerTwist (B.size i0) 1 (A i0).isoClass⟩`,
  because the rank and class of `CuspidalDatum.twist 1` are by definition
  `B.size i0` and that real power twist. This contradicts the hypothesis
  on `i0`.

## Normalizations and universes

The product `Π` is the Library's normalized block induction
`T.normalizedProductInductionFunctor B` (positive half-modulus
`T.leviModulus B`). The derivatives are the Library's
`mirabolicDerivativeOfOrder`, normalized `Ψ⁻`/`Φ⁻`. Both are used unchanged,
through the published 4.7(b) theorem, which uses the same objects.

The universes `uF`, `uV` are independent. The blocks have carriers in `uV`,
and `W`, its derivatives and `Π` have carriers in `max uF uV`. The block
`A i0` is compared with the derivative through `SmoothRep.universeLift.{uF}`.

## Imports and dependency note

Direct imports:

- `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof`
  (Lemma 4.7(b), task `0b3bf4c1-9878-444f-899e-ba29d7679c29`);
- `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne`
  (helper of task `451717b1`: `ν ρ ≠ ρ`);
- `Langlands.Representation.Induction.SingleBlock` (Worker 163);
- `Langlands.Representation.Category.UniverseLift`.

For task `451717b1`, the operator answered question `f489243c6b4e5a93a776216687d56d51`
with response `09565d9017ef55faa68ad9890c242aed`. It allows importing
`cuspidalProductMirabolicSupportShift` with its whole closure, including
`Classification.CuspidalProductDerivativeQuotientSupport`, `WholeLeviTransport`
and `Derivative.PartialDerivativeJacquetComparisonProof`. The conditions are
those of response `f6869c7da0bf5bb4a8b006fdf51ba668`: the final Markdown must
audit the complete import closure and proof dependencies against every
exclusion of the task, and must cite the response. The audit of this
module's own closure is at the end of this section.

An earlier version of this module imported
`Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof`
for the case `j = i0`. The earliest published artifact of that module,
`a7545313`, belongs to task `67279e36-f3c2-42e3-9302-11729784042e`, which the
contract of task `451717b1` excludes. Following the operator's rule in response
`09565d9017ef55faa68ad9890c242aed` (an import whose audit finds an excluded task
is not used), the import was replaced by the helper module
`OrderedCuspidalProductTwistOne`. The removal also takes
`Classification.CuspidalIntegralTwistFreenessStatement` out of the closure.

At Library commit `b1c8a5e809be36100da09da81385a7ca6789ae80`, the recursive
project import closure of the 4.7(b) proof module has 606 `Langlands` modules.
The other three direct imports add exactly four modules outside it:

- `Langlands.LocalField.Uniformizer` (uniformizer as a field unit; imports
  only local-field normalization definitions; its own Markdown says that it holds
  the constructions of Worker 33 and Worker 20, which the Integrator moved out of
  `LocalFactor.Abelian.Padic`);
- `Langlands.Representation.Category.UniverseLift` (carrier universe lifts;
  introduced by definition artifact `b6075d7d`, task `4d079ce9`);
- `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne` (the new
  helper above; not yet published);
- `Langlands.Representation.Induction.SingleBlock` (one-block induction
  evaluation; introduced by definition artifact `fcc278b3`, task `8c397428`).

Each published module of this closure was checked against every task that
published an artifact containing it: the task recorded on the artifact, or the
host task of its review. None of the tasks behind these four modules, or behind
the Lean modules they import, is excluded by the contract of task `451717b1`.
None of these four modules uses a segment derivative formula, a segment socle,
head or Jacquet result, a classification or exhaustion theorem, or a Whittaker
finiteness result. `TwoSupercuspidalTopDerivatives`, the repeated cuspidal
support shift, the integral twist freeness modules and
`Parabolic.RightProductExactness` are not imported.

Audit of this module's whole closure at the same commit. The recursive project
import closure of this module has 611 `Langlands` modules. 599 of them have
published artifacts. The other 12 have no task owner: this module,
`OrderedCuspidalProductTwistOne`, and ten integrator extractions of
infrastructure (`Group.GL.OneBlockShape`, `Group.GL.Transvection`,
`HarmonicAnalysis.FiniteProductMeasureScaling`,
`HarmonicAnalysis.PadicLatticeTopology`, `Compact.OrbitMeanTranslation`,
`CuspidalSupport.WholeLeviTransport`, `Derivative.MirabolicDeterminant`,
`Representation.OrbitSpan`, `Smooth.Transfer.GroupEquivalence` and
`Topology.CompactNormCharacter`). The owning tasks of the published modules
are 705 tasks. With all their contract requirements, followed transitively,
there are 708 tasks. These were compared with the 38 task IDs that the
contract of task `451717b1` excludes, and two of them occur:

- Task `62de5903-b616-4b5c-88eb-a066b77c5467` owns proof `001944f3`. That
  proof only bundles byte-identical copies of seven modules of the 4.7(b)
  closure: `Derivative.MirabolicDerivativeVanishing`,
  `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
  `MirabolicPhiMinusNondegeneratePairing`,
  `PartialDerivativeJacquetComparisonStatement`, and
  `Geometric.ParabolicOrbitSectionComparison` and
  `ParabolicOrbitStagesCoefficient`. These modules were accepted earlier under
  other tasks: proof `f957ae76` (task `a925b519`, BZ77 3.8), statement
  `5d596030` (task `087df35f`) and definitions `a84b7e4a` and `4bfd5d0d`
  (task `18915f54`). The conclusion of `62de5903`,
  `Whittaker.SupercuspidalCoinvariantFinitenessStatement`, is not in the
  closure.
- Task `8e5b4563-0365-41c7-b134-70f2a0b36292` occurs only as a contract
  requirement of task `f81d9b36`. That task owns the quotient-support helper
  `bf38b454`, which response `09565d90` authorizes by name. No module of
  `8e5b4563` is in this closure. In particular, neither
  `SegmentSocleDerivativesStatement` nor any `HighestDerivativeSupportShift`
  module is in it.

A scan of the 611 Lean files found no excluded declaration or module name and
no excluded task ID. The scanned names are those listed in the contract,
together with `CuspidalIntegralTwistFreeness`, `RepeatedCuspidalSupportShift`,
`TopProduct` and the Whittaker coinvariant-finiteness statements. The final
proof Markdown of task `451717b1` contains the audit of the complete proof
closure.
