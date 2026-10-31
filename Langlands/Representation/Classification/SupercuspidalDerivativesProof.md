# Derivatives of irreducible supercuspidal representations: proof

Author: Worker 818. Coauthor: Worker 1025, who wrote the imported unit
`Derivative.MinusVanishing` of this task and audited the multiplicity-one
route. The imported Whittaker multiplicity one is Worker 16's published proof.

`Langlands.Classification.supercuspidalDerivatives` proves the published
`Langlands.Classification.SupercuspidalDerivatives.{uF,uW} F T` of
`Langlands.Representation.Classification.SupercuspidalDerivativesStatement`.
Its type is

```text
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  SupercuspidalDerivatives.{uF, uW} F T
```

with no other premise. For every nontrivial unitary additive character `ψ`
(for `T.topology`), every `n`, and every irreducible
`A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier)` with
`GeneralLinear.IsSupercuspidal A.representation`, it proves both clauses:

1. for every `k` with `0 < k < n + 1`, the derivative
   `(Derivative.generalLinearDerivative T ψ (n + 1) k hk).obj A` is
   `Subsingleton`;
2. the top derivative
   `(Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A`
   has `Module.finrank ℂ` equal to `1`. So it is nonzero and
   finite-dimensional, not merely of dimension at most one.

The target's Lean/Markdown pair and every pair it imports are unchanged.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §4.4, printed p.454 (one-based PDF page 15), Theorem (Gelfand–Kazhdan):
  "Let π ∈ Alg G_n be quasicuspidal. Then π^(k) = 0 for 0 < k < n. If π is
  cuspidal and irreducible, then π^(n) = 1 is a one-dimensional
  representation." The source gives no proof: "For the proof, see ([1],
  chap. III)", i.e. Gelfand–Kazhdan. The converse remarked after the theorem
  is not proved here.
- §4.3, printed p.454, and §3.5, printed p.452: the derivatives are
  `π^(k) = Ψ⁻ (Φ⁻)^(k-1) (π|_(P_n))`.

The source's "cuspidal" and "quasicuspidal" are represented by the published
`IsSupercuspidal` (admissibility together with vanishing of every proper
Jacquet module). No errata entry for BZ77 is registered in the project
literature index, the central library or the public notes. The Zelevinsky
1980 paper (`zelevinsky-1980-induced-ii`) is not used.

## Parameters, universes and normalization

- `p` is implicit with `[Fact p.Prime]`; `F : PadicField.{uF} p` and
  `T : F.TopologicalData` are explicit. Every statement installs
  `letI := T.topology`, the topology supplied by `T`.
- The character is any `ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`.
  Existence of such a character is not assumed anywhere.
- The level parameters of `supercuspidalDerivatives` are `uF` and `uW`
  (`lean_check` inspection). The carrier universe `uW` of `A` is independent
  of the field universe `uF`. The helper namespace uses the name `uV` for the
  same carrier universe.
- The derivative is the published `Derivative.generalLinearDerivative`, with
  its determinant `|det|^(-1/2)` normalization of `Φ⁻`, used unchanged. The
  normalization plays no role: every normalizing character that occurs is
  evaluated at a unipotent element, where it is `1`
  (`phiMinusCharacter_eq_one` in unit 1, `phiMinusCharacter_eq_one_of_upper`
  in the helper `SupercuspidalTopDerivative`). No Haar-modulus normalization
  appears in any argument, so the Haar-modulus comparison of tasks
  `a622f240-4846-4086-b34f-f650ba636ee4` and
  `f947a735-872d-44db-a9ea-954d17dec4bd` is not needed.

## Implemented proof

Line numbers refer to `SupercuspidalDerivativesProof.lean`. The helper
declarations are in the namespace
`Langlands.Classification.SupercuspidalDerivativesProof`.

### Vanishing clause

This is the published
`SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative`
(module `Classification.SupercuspidalDerivativeVanishing`, unit 1 of this
task). For `0 < k < N` it shows that the derivative of a supercuspidal `A`
factors through the coinvariants of the unipotent radical of the proper
parabolic of the two-block shape `(N - k, k)`. Those coinvariants vanish by
the Jacquet clause of `IsSupercuspidal`.

### Top clause

- `finrank_eq_one_of_dual` (l.29): linear algebra. If `f₀` is a nonzero
  linear functional on `V` and every functional is a scalar multiple of
  `f₀`, then `f₀` is injective (functionals separate points) and surjective,
  so `finrank V = 1`.
- `finrank_top_of_multiplicityOne` (l.44): for any smooth `A` of
  `GL_(0+n+1)`, if the space `Whittaker.glFunctionals ψ (0 + n)` of standard
  Whittaker functionals on `A` satisfies multiplicity one (every functional is
  a unique multiple of each nonzero one) and the top derivative
  `generalLinearDerivativePositive T ψ 0 n` of `A` is nonzero, then that top
  derivative has finrank `1`. The published helper module
  `Classification.SupercuspidalTopDerivative` supplies the surjective top
  quotient map `topQuotient T ψ n A : A → Ψ⁻ (Φ⁻)^n (A|P)`
  (`topQuotient_surjective`) and shows that `f ∘ topQuotient` is a standard
  Whittaker functional for every functional `f` on the top derivative
  (`comp_topQuotient_mem_glFunctionals`). Choose a nonzero vector and a
  functional `f₀` not vanishing on it. Then `f₀ ∘ topQuotient` is a nonzero
  Whittaker functional, multiplicity one writes `f ∘ topQuotient` as
  `c • (f₀ ∘ topQuotient)`, and surjectivity gives `f = c • f₀`. Now apply
  `finrank_eq_one_of_dual`.
- `multiplicityOne_of_topologicalData` (l.73): the published
  `Langlands.Whittaker.multiplicityOne.{uF,uV}` is stated with the topology of
  `F.canonicalNormedField`. The published
  `PadicField.TopologicalData.topology_eq_canonicalNormTopology`
  (`LocalField.Normalization.Proof`) says that `T.topology` is that topology.
  Rewriting with it gives multiplicity one for `T.topology`, for every rank,
  carrier, character, admissible irreducible representation and pair of
  functionals.
- `finrank_generalLinearDerivativePositive_top` (l.88): for irreducible
  supercuspidal `A` of `GL_(0+n+1)`, the top derivative has finrank `1`.
  Admissibility (`hsc.1`, the first clause of `IsSupercuspidal`) and
  irreducibility give multiplicity one by the previous lemma. Nonvanishing is
  the published `nontrivial_generalLinearDerivativePositive_top` of the
  helper module, applied with `nontrivial_of_isIrreducible`.
- `finrank_generalLinearDerivative_top` (l.103): the same for the actual
  `generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl`. By definition this
  functor is the rank cast `generalLinearRankCast T (rank_eq_of_succ_le le_rfl)`
  followed by `generalLinearDerivativePositive T ψ ((n + 1) - (n + 1)) n`. The
  proof replaces `(n + 1) - (n + 1)` by a variable `m` with `m = 0`,
  substitutes, and applies the previous lemma to the rank-cast
  representation. It remains irreducible and supercuspidal by the published
  `isIrreducible_rankCast` and `isSupercuspidal_rankCast`.

### Main theorem

`supercuspidalDerivatives` (l.131) introduces `ψ`, `n`, `A` and the two
hypotheses. The first clause is unit 1 and the second is
`finrank_generalLinearDerivative_top`.

The cited Gelfand–Kazhdan argument uses the restriction of a cuspidal
representation to the mirabolic group and uniqueness of the Whittaker model.
The Lean proof follows that outline. The helper module shows, through the
mirabolic restriction, that the top derivative is a nonzero quotient of `A`
whose functionals pull back to Whittaker functionals. Whittaker multiplicity
one then makes its dual one-dimensional.

## Published inputs

Every mathematical prerequisite is a published, independently accepted
proof or definition, imported by Lean name.

- `Classification.SupercuspidalDerivativeVanishing` (unit 1 of this task,
  candidate `058d858f-f57b-412f-bf13-837f81a1fefe`): vanishing of the
  intermediate derivatives, `isSupercuspidal_rankCast`.
- `Classification.SupercuspidalTopDerivative` (helper of this task, candidate
  `d033aab5-6e23-4918-9fc9-a3bc0d0edaff`): `topQuotient`, its surjectivity and
  Whittaker equivariance, and nonvanishing of the top derivative. It uses
  `Derivative.MinusVanishing` (Worker 1025, candidate
  `c6026915-8731-45a8-bd21-ef1ac39654b8`).
- `Whittaker.MultiplicityOneProof` (task
  `209cde88-bab8-4a85-8a9d-72b8864b6fa0`, Worker 16, accepted candidate
  `ba2dff22-6ead-4dae-b282-909919295be6`):
  `Langlands.Whittaker.multiplicityOne`. Its proof applies the published
  Gelfand–Kazhdan contragredient theorem, the Shalika distribution
  invariance, the generalized-coefficient kernel criterion and the
  Haar-symmetry results. The multiplicity-one task `bb8e9d9d` and its
  `WhittakerPrerequisitesStatement` interface are not used.
- `LocalField.Normalization.Proof`: `topology_eq_canonicalNormTopology`.
- The target statement module, which imports the definitions
  `Classification.Supercuspidal`, `Derivative.Iteration` and
  `HarmonicAnalysis.Basic`.

## Dependency audit

The transitive import closure of `SupercuspidalDerivativesProof` in the
Library at commit `c6045fe1328899de3416096b16eb72db93a6c7fc` contains 303
`Langlands` modules, plus Mathlib. It was searched for every excluded
proposition name and for the modules of every excluded task, read from those
tasks' contracts. None occurs. The statement modules in the closure only
define propositions. Each one is either the target, the statement of a
published proof used above, or a statement imported by a published proof
module. No statement is used as a hypothesis. The only modules in the
closure whose names mention segments, socles or heads are
`Classification.Segments` (segment and multisegment data, linkage relations,
transport lemmas for irreducible socles, heads and quotients along
equivalences) and `Classification.ConstituentRelations` (the relation
definitions). They enter only through the Gelfand–Kazhdan contragredient
proof used by multiplicity one, along the import chain
`Smooth.Contragredient.GelfandKazhdanAssembly` → `CompactCoefficient.GroupTransport`
→ `CuspidalSupport.CuspidalTensorAssociationProof` →
`CuspidalSupport.CuspidalTensorStatement` → `Classification.SupercuspidalSupport`
→ `Classification.Segments` → `Classification.ConstituentRelations`. They
contain no segment theorem, and this proof uses none of their declarations.

Condition by condition:

- **Exact target, telescope and premises.** The theorem's type is exactly
  the target with the outer telescope
  `{p} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and
  `T.topology`. It quantifies over every supplied character and has no
  additional premise; finiteness, genericity, character existence and
  multiplicity one are not hypotheses. The published `generalLinearDerivative`
  is used unchanged; no stand-in functor is used.
- **Universes.** Level parameters `uF`, `uW`, independent.
- **Proved inputs only.** All inputs are listed under "Published inputs".
  No pending task, draft, citation or proposition definition is used as a
  proof.
- **Haar-modulus normalization.** Not used (see above).
- **Worker 357's units.** Minus/GL derivative exactness (`b65bc667`,
  `30fc529b`), the BZ77 4.5/4.6 Leibniz filtration, binary and mixed products
  (`85af02b8`, `fb4abf4e`), partial derivatives (`e9266fda`) and Ze80 3.7/3.8
  are not used. The only derivative modules in the closure are
  `Derivative.MirabolicMinus`, `MirabolicCharacter`, `MirabolicLatticeBox`,
  `Iteration` and `MinusVanishing`.
- **Independence section.** None of `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`
  (tasks `23e98d90`, `a55c4267`, `8fa9f68b`),
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom` (`7ff2a1e9`),
  `SegmentSocleProductIrreducibility` (`2ae5cbe5`),
  `AdjacentUnlinkedSegmentSocleSwap` (`e3634665`, `cded83f3`),
  `TwoSegmentSocleCommutation` (`426911b4`, `66e3b87c`),
  `LinkedSegmentSocleGluing` (`c84cd52c`, `6780b79c`),
  `OrderedMultisegmentSocleExistence` (`23189526`), socle exhaustion
  (`f3a69bc8`), segment analytic classification (`aca8805b`), special-head
  exhaustion (`3bfb61fa`), ordered special-head existence (`ebea9a8a`),
  quotient coverage (`20e4e1c6`), ordered conversion (`8252833d`), tempered
  block uniqueness (`52e97845`), `GenericSegmentProductUniqueness`
  (`30341ae4`), `SquareIntegrableLanglandsClassification` (`1cb45da2`),
  square-integrable exhaustion (`cd8ab97c`), regular exhaustion (`bf433f0a`)
  or forward special-segment square-integrability (`5eece9e8`), nor any of
  their statement or proof modules, is in the closure or used.
- **Special-head criterion.** `SegmentHeadProductIrreducibility`
  (`8364e73f`) is not used.
- **BZ77-only upstream restrictions.** No segment derivative formula, no
  segment socle/head existence (`67279e36`, `4ca79bbd`), no segment Jacquet
  formula (`SegmentFullJacquetFormula`/`ed48ae06`,
  `SegmentHeadJacquetFormula`/`55ad1e10`, `SegmentSocleJacquetFormula`/`b95105c6`,
  `SegmentSpecialJacquetExponentNormFormula`/`92aea10f`), no segment
  classification, no `SegmentSpecialEssentialSquareIntegrability`,
  `MultisegmentSocleExhaustion` or other consumer conclusion in the list. Not
  used: `TwoSupercuspidalNonadjacentProductIrreducible` (`3c9849a4`) and
  `TwoSupercuspidalProductStructure` (`ab61f565`); no `TwoSupercuspidal`
  module is in the closure. Parent statements (b), (d), (e), (f) are not used.
- **Full-formula consumer restrictions.** No Ze80 segment derivative formula
  (§3.5, §9.6), no segment product irreducibility criterion (Ze80 4.2, 9.7),
  no analytic or square-integrability result (Ze80 9.3), no classification or
  exhaustion theorem. Every derivative result used (units 1, 2 and the
  helper) is published.
- **Whittaker-finiteness independence.** Not used:
  `IrreducibleCoinvariantFinitenessStatement` (`5ab445dc`),
  `LeviCuspidalCoinvariantFinitenessStatement` and its proof `3ff5c8fb`, and
  the mirabolic finite-length route `MirabolicFiniteLength` (`5428fe2c`).
  None of their modules is in the closure. The finiteness of the top
  derivative is a consequence of multiplicity one here, not an input.
- **Validation.** `lean_check` in environment
  `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: lake build, 0 errors, 0 warnings.
  The axioms are `propext`, `Classical.choice` and `Quot.sound`. No `sorry`,
  `admit` or new axiom is used.
