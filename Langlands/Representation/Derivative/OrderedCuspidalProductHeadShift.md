# A head shift excluded by the ordering of a cuspidal product

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
  central-character argument in the helper module
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
  (Lemma 4.7(b), `cuspidalProductMirabolicSupportShift`);
- `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne`
  (helper of the 4.11 proof: `ν ρ ≠ ρ`);
- `Langlands.Representation.Induction.SingleBlock`;
- `Langlands.Representation.Category.UniverseLift`.

The module imports `cuspidalProductMirabolicSupportShift` with its whole
closure, including `Classification.CuspidalProductDerivativeQuotientSupport`,
`WholeLeviTransport` and `Derivative.PartialDerivativeJacquetComparisonProof`.
The complete import closure and proof dependencies are audited below against
every exclusion of the 4.11 proof; the audit of this module's own closure is
at the end of this section.

For the case `j = i0` the module uses the helper module
`OrderedCuspidalProductTwistOne`, not
`Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof`:
that module was first published with the individual
special-head/reverse-socle existence result, which the 4.11 proof excludes.
So `Classification.CuspidalIntegralTwistFreenessStatement` is not in the
closure either.

At Library commit `b1c8a5e809be36100da09da81385a7ca6789ae80`, the recursive
project import closure of the 4.7(b) proof module has 606 `Langlands` modules.
The other three direct imports add exactly four modules outside it:

- `Langlands.LocalField.Uniformizer` (uniformizer as a field unit; imports
  only local-field normalization definitions; its own Markdown says that it holds
  the uniformizer-unit constructions moved out of `LocalFactor.Abelian.Padic`);
- `Langlands.Representation.Category.UniverseLift` (carrier universe lifts);
- `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne` (the
  helper above);
- `Langlands.Representation.Induction.SingleBlock` (one-block induction
  evaluation).

None of these four modules, or of the Lean modules they import, belongs to a
result excluded from the 4.11 proof. None of these four modules uses a segment derivative formula, a segment socle,
head or Jacquet result, a classification or exhaustion theorem, or a Whittaker
finiteness result. `TwoSupercuspidalTopDerivatives`, the repeated cuspidal
support shift, the integral twist freeness modules and
`Parabolic.RightProductExactness` are not imported.

Audit of this module's whole closure at the same commit. The recursive project
import closure of this module has 611 `Langlands` modules. It was compared
with the results excluded from the 4.11 proof, and two of them touch it:

- The proof of `Whittaker.SupercuspidalCoinvariantFinitenessStatement` was
  published together with byte-identical copies of seven modules of the 4.7(b)
  closure: `Derivative.MirabolicDerivativeVanishing`,
  `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
  `MirabolicPhiMinusNondegeneratePairing`,
  `PartialDerivativeJacquetComparisonStatement`, and
  `Geometric.ParabolicOrbitSectionComparison` and
  `ParabolicOrbitStagesCoefficient`. These modules were published earlier, with
  the BZ77 3.8 proof and with other statements and definitions. The conclusion
  `Whittaker.SupercuspidalCoinvariantFinitenessStatement` is not in the
  closure.
- The derivative statements of `Classification.SegmentSocleDerivativesStatement`
  are reached only as a prerequisite of the proof of their statement (c),
  `HighestDerivativeSupportShift`, to which the quotient-support helper
  `Classification.CuspidalProductDerivativeQuotientSupport` belongs.
  No module of those statements is in this closure. In particular, neither
  `SegmentSocleDerivativesStatement` nor any `HighestDerivativeSupportShift`
  module is in it.

A scan of the 611 Lean files found no excluded declaration or module name.
The scanned names are those of the excluded results, together with
`CuspidalIntegralTwistFreeness`, `RepeatedCuspidalSupportShift`, `TopProduct`
and the Whittaker coinvariant-finiteness statements. The Markdown of
`OrderedCuspidalProductNondegeneracyProof` contains the audit of the complete
proof closure.
