# The product of two supercuspidal representations (Ze80 1.11), proof

Author: Worker 892 (task `ab61f565-1427-4746-ba77-46097563e962`, with Worker
163 as collaborator). This module is a final assembly. It copies no code, and
every input is a published theorem imported by Lean name. The authors of
those inputs are listed under "Inputs" below.

## Statement proved

```lean
theorem Langlands.Classification.twoSupercuspidalProductStructure
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalProductStructure.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.TwoSupercuspidalProductStructure.{uF,uV} F T` of
`Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement`.
The proposition is unchanged, and the theorem has no hypotheses beyond the
outer telescope. That proposition is Zelevinsky 1980, Proposition 1.11 in
full. It is the conjunction of three clauses:

1. `TwoSupercuspidalNonadjacentProductIrreducible F T` (part (a)). Take
   positive ranks `k, l` and supercuspidal `ρ` of `GL_k` and `ρ'` of `GL_l`.
   Suppose `⟨l, [ρ']⟩ ≠ ⟨k, [νρ]⟩` and `⟨k, [ρ]⟩ ≠ ⟨l, [νρ']⟩` in
   `Σ d, SupercuspidalClass (n := d)`. Then the product `ρ × ρ'` is
   irreducible. Unequal ranks are included.
2. `TwoSupercuspidalAdjacentProductComposition F T` (part (b), structure).
   Take positive `k` and supercuspidal `ρ, ρ'` of `GL_k` with
   `[ρ'] = [νρ]` or `[ρ] = [νρ']`, and let `P = ρ × ρ'`. Then
   `HasCompositionSeriesLength P.obj 2` holds. There is exactly one invariant
   subspace `S : Subrepresentation P.representation` with `S ≠ ⊥` and
   `S ≠ ⊤`, unique as an invariant subspace. For every such `S`, the actual
   subrepresentation on `S` and the actual quotient `P / S` are irreducible.
3. `TwoSupercuspidalAdjacentProductJacquet F T` (part (b), Jacquet modules).
   Under the same hypotheses, every invariant subspace `S ≠ ⊥, ⊤` comes with
   actual `Representation.Equiv` witnesses. The first goes from the
   normalized `(k, k)` Jacquet module of `S` to
   `FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ.obj ρ'.obj)`,
   that is `ρ ⊗ ρ'`. The second goes from the normalized Jacquet module of
   `P / S` to `ρ' ⊗ ρ`.

Since the theorem is a proof of this exact proposition, it claims nothing
beyond the statement's Markdown.

## Normalization, factor order and universes

- *Twist.* `ν = |det|` is `T.determinantPowerCharacter k 1`, with the
  residue-normalized absolute value. On classes it acts by
  `T.supercuspidalClassRealPowerTwist k 1`. Both adjacency alternatives are
  used exactly as stated, in the order `ρ' ≅ νρ` or `ρ ≅ νρ'`.
- *Product and factor order.* The product is
  `(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
  (twoBlockFactors hk hl ρ.obj ρ'.obj)`. `ρ` sits in block `0`, the upper
  left `GL_k`, and `ρ'` in block `1`. This object is upper block parabolic
  normalized induction: the covariance carries the positive half-modulus
  `δ_P^(1/2)` (`T.leviHalfCharacter`), and the group acts by right
  translation. No input replaces this object. The helper module works with
  `T.normalizedParabolicInduced 𝔅 σ.representation`,
  `σ = ρ ⊗ ρ'`, which equals it by the published `rfl` lemmas
  `normalizedProductInductionFunctor_obj` and `normalizedProductInduced_eq`.
- *Jacquet modules.* `T.normalizedJacquetFunctor (twoBlocks k k hk hk)` is
  the actual coinvariant quotient by the upper unipotent radical, normalized
  by the inverse half-modulus `δ_P^(-1/2)`. The submodule has Jacquet module
  `ρ ⊗ ρ'`, with `ρ` acted on by the first block. The quotient has
  `ρ' ⊗ ρ`, with the factors exchanged.
- *Universes.* The field lives in `uF` and the carriers of `ρ, ρ'` in `uV`.
  These are independent universe parameters of the theorem
  (`level_parameters = [uF, uV]` in the `lean_check` inspection). The product,
  its invariant subspaces, its quotients and their Jacquet modules have
  carriers in `max uF uV`. The tensor targets have carriers in `uV`. The
  Jacquet clause therefore uses cross-universe `Representation.Equiv`
  values, not class equality or Jordan–Hölder counts. Every input is
  instantiated at the same `F`, `T`, `uF` and `uV`.
- *Generality.* The prime `p`, the finite extension `F` and the compatible
  topology `T` are arbitrary. So are all positive ranks.

## Implemented proof

The proof is one term:

```lean
TwoSupercuspidalAdjacent.productStructure_of F T
  (twoSupercuspidalNonadjacentProductIrreducible F T)
  (twoSupercuspidalAdjacentProductReducible F T)
  (fun n => CuspidalSupport.nonassociatedJacquetSubquotients F T n)
  (fun n => CuspidalSupport.associatedJacquetFiltration F T n)
```

`productStructure_of` (module
`Langlands.Representation.Classification.TwoSupercuspidalAdjacentStructure`)
derives `TwoSupercuspidalProductStructure F T` from four theorem-valued
arguments. Here each argument is a published theorem with no premises, so
the result is unconditional. The three conjuncts arise as follows.

### Conjunct 1: nonadjacent irreducibility

This conjunct is `twoSupercuspidalNonadjacentProductIrreducible F T`
(Worker 745, module `TwoSupercuspidalNonadjacentIrreducibilityProof`). It
carries out the argument of BZ77 Theorem 4.2 for `ρ × ρ'` with
Bernstein–Zelevinsky derivatives:

- The Leibniz filtration (BZ77 4.14(c)) and the derivatives of supercuspidal
  representations (BZ77 4.4) describe the derivatives of `π = ρ × ρ'`. The
  top derivative is one-dimensional. At each intermediate order, every
  graded piece is zero or a rank cast of `ρ` or `ρ'`. The pieces for
  `ν π~` are likewise zero or rank casts of `ν ρ~` or `ν ρ'~`.
- Let `S` be a nonzero proper subrepresentation. Exactness of the top
  derivative gives a constituent `X ∈ {S, π/S}` whose top derivative is zero.
  Detection by derivatives (BZ77 3.5) gives a highest nonzero derivative of
  `X`, at an intermediate order `d`.
- BZ77 Proposition 3.8 turns the twisted evaluation pairing of `X` and
  `ν X~` into a nonzero invariant form on their `d`-th derivatives.
- A nonzero invariant form between supercuspidal `A` and `ν B~` forces
  `[B] = ν[A]`. The two nonadjacency hypotheses, together with integral twist
  freeness (`[A] ≠ ν[A]`), rule out every such form between the pieces. This
  is a contradiction.

Its Markdown gives the full argument.

### Conjunct 2: length two and the unique proper subspace

For given `k, ρ, ρ'` and adjacency `h`, `productStructure_of` takes the first
component of `adjacentStructure F T hk (hnon (k + k)) (hfilt (k + k)) ρ ρ' h`
and applies it to the reducibility `twoSupercuspidalAdjacentProductReducible
F T k hk ρ ρ' h : ¬ P.IsIrreducible`. The helper module (Worker 892) proves
this component with the argument of BZ77 §2.16(1) for `GL_{2k}` and the
shape `(k, k)`:

- The published filtration theorem `associatedJacquetFiltration` (BZ77
  2.13(c)) filters the normalized `(k, k)` Jacquet module of `ρ × ρ'` by the
  Weyl transports of `σ = ρ ⊗ ρ'`. There are exactly two minimal conjugating
  permutations, and they give `σ` and `σ' = ρ' ⊗ ρ`.
- In the adjacent case, `σ ≇ σ'`. A scalar uniformizer placed in the first
  block acts on the two tensors by central characters that differ by
  `ν(ϖ) = q^(-k) ≠ 1`.
- With `nonassociatedJacquetSubquotients` (BZ77 2.13(b)), the Jacquet count
  `S ↦ jacquetLength T {𝔅} S` is strictly monotone on invariant subspaces,
  with values `0` at `⊥` and `2` at `⊤`. So every proper nonzero `S` satisfies
  `⊥ ⋖ S ⋖ ⊤`.
- Reducibility supplies some `S ≠ ⊥, ⊤`. Hence the product has length two.
  The subrepresentation and the quotient are irreducible, since their graded
  pieces are simple. The subspace is unique: a second one `S'` would satisfy
  `S' ≅ P / S`. This would give `ρ ⊗ ρ' ≅ ρ' ⊗ ρ` through the Jacquet
  equivalences of conjunct 3, which is impossible.

### Conjunct 3: ordered Jacquet factors

This conjunct is the second component of the same `adjacentStructure`. It
needs no irreducibility or reducibility hypothesis. Frobenius reciprocity
turns the inclusion `S → i(σ)` into a nonzero map `r(S) → σ`. Since `r(S)`
has Jacquet length one, Schur's lemma makes this map an equivalence,
`r(S) ≅ ρ ⊗ ρ'`. Exactness of the normalized Jacquet functor and a
Jordan–Hölder comparison with the transport filtration then give
`r(P / S) ≅ ρ' ⊗ ρ`. No step infers an equivalence of whole Jacquet modules
from composition factors alone. Both equivalences come from actual maps:
Frobenius reciprocity together with Schur, and the comparison of two actual
length-two series of `r(P)`. Second adjointness is not used. The same
conjunct is also published as
`twoSupercuspidalAdjacentProductJacquet` (module
`TwoSupercuspidalAdjacentJacquetProof`, Worker 163). This module does not
import it.

### The adjacent-reducibility step

Ze80 gives only a sketch of reducibility in the adjacent case. The
published proof `twoSupercuspidalAdjacentProductReducible` (Worker 1023,
module `TwoSupercuspidalAdjacentReducibilityProof`) completes the sketch for
the actual Library objects. Each obligation of the sketch is a published,
proved theorem there, not structure data:

- *Unitary twist.* `supercuspidalRealUnitarization` gives a real `t` such
  that `ν^t ρ` is unitarizable. Put `ρ₀ = ν^t ρ`. Real twists compose
  additively, so for `ρ' ≅ νρ` the product `ρ × ρ'` is equivalent to a
  character twist (`twistedProductCharacterTwist`) of
  `π_(-1/2) = ν^(-1/2) ρ₀ × ν^(1/2) ρ₀`. Hence it is enough to show that
  `π_(-1/2)` is reducible.
- *Common compact realization.* `glParabolicCompactScalarIntegral` supplies a
  compact open `K` with `G = P K` and a Haar probability measure on `K`.
  `exponentHeight` (`ExponentFamily`) realizes all `π_s = ν^s ρ₀ × ν^(-s) ρ₀`
  on one space of functions. These representations agree on `K`, and
  `exponentFamilyEquiv` identifies each with the actual product.
- *Invariant Hermitian forms.* Suppose `π_(-1/2)` is irreducible. Then
  `twoSupercuspidalNonadjacentProductIrreducible` makes every `π_s` with
  `s ≤ 0` irreducible: at `s ≠ -1/2` the factors are nonadjacent, by twist
  freeness. The compact pairing `normalizedIntegralForm` pairs `π_s` with
  `π_(-s)`, and the irreducible swap `irreducibleTwoFactorProductSwap` gives
  `π_s ≅ π_(-s)`. Together they produce a nonzero invariant sesquilinear form
  on each `π_s`.
- *Positivity argument.* `unitarizabilityContinuation` uses weak continuity
  in `s` and unitarizability at `s = 0` (`familyZeroForm`). It propagates
  positivity along the connected set `(-∞, 0]`, so `π_s` is unitarizable for
  every `s ≤ 0`.
- *Unbounded matrix coefficient.* `twoBlockLargeExponentNonUnitarizable`
  exhibits an unbounded matrix coefficient of `π_s` for `s < -k/2`. So `π_s`
  is not unitarizable at `s = -k/2 - 1`, a contradiction.

The alternative `ρ ≅ νρ'` reduces to `ρ' ≅ νρ` by the irreducible product
swap. The Markdown of that module gives the details.

## Inputs

| Input | Lean name and module | Status, authors |
| --- | --- | --- |
| algebraic part of (b) and assembly | `TwoSupercuspidalAdjacent.productStructure_of`, `Classification.TwoSupercuspidalAdjacentStructure` | published, Worker 892 (source preserved by Worker 163) |
| (a) nonadjacent irreducibility | `twoSupercuspidalNonadjacentProductIrreducible`, `Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` | published, artifact `98cc1114`, task `3c9849a4`, Worker 745 |
| adjacent reducibility | `twoSupercuspidalAdjacentProductReducible`, `Classification.TwoSupercuspidalAdjacentReducibilityProof` | published, artifact `5d030a71`, task `0988a3e0`, Worker 1023 |
| nonassociated Jacquet subquotients (BZ77 2.13(b)) | `CuspidalSupport.nonassociatedJacquetSubquotients`, `CuspidalSupport.NonassociatedJacquetSubquotientsProof` | published, artifact `8c6610e7`, Workers 169 and 191 |
| associated Jacquet filtration (BZ77 2.13(c)) | `CuspidalSupport.associatedJacquetFiltration`, `CuspidalSupport.AssociatedProof` | published, artifact `df6d40a0`, Workers 168 and 193 |

Each input is applied at the same `F`, `T`, `uF` and `uV`. None takes a
premise.

## Dependency audit

### Import closure

The module imports the statement module and the five input modules above. A
recursive scan of `import` lines over Library commit
`c3ba00e3ca28c64aeaf5b8f4af3c8994940184d8` gives 879 project modules in the
transitive closure, this module included. Per input, the closures have the
following sizes:

- `TwoSupercuspidalAdjacentStructure`: 197 modules.
- `TwoSupercuspidalNonadjacentIrreducibilityProof`: 656 modules.
- `TwoSupercuspidalAdjacentReducibilityProof`: 738 modules. This closure
  contains the nonadjacent one.
- `NonassociatedJacquetSubquotientsProof`: 400 modules.
- `AssociatedProof`: 296 modules.

Outside the reducibility closure, the helper and the two Jacquet theorems
add 140 modules. These are the geometric lemma and the filtration, count
and length machinery of the Jacquet modules.

### Independence list

- *Task IDs and declarations.* A scan of every Lean file in the closure finds
  none of the 22 task-ID prefixes of the Independence list, nor `8e5b4563`. It
  also finds none of the declaration names `SegmentFullJacquetFormula`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
  `SegmentSpecialJacquetExponentNormFormula`,
  `SegmentSocleProductIrreducibility`, `MultisegmentSocleExhaustion`,
  `OrderedMultisegmentSocleExistence`, `GenericSegmentProductUniqueness`,
  `SquareIntegrableLanglandsClassification` and
  `SegmentSpecialEssentialSquareIntegrability`. Nor does it find the
  segment-socle statements of task `8e5b4563`: `SegmentSocleDerivatives`,
  `HighestDerivativeSupportShift`,
  `NonjuxtaposedSegmentSocleConstituentLevel` and `castRank`. These names
  occur only in the audit sections of some Markdown files.
- *Source locators.* No Lean file in the closure cites Ze80 §3.5, §9.3,
  §9.6, Theorem 4.2 or 9.7. The references to "3.5" and "Theorem 4.2" in
  the closure are to BZ77 §3.5 (detection by derivatives) and to BZ77
  Theorem 4.2, whose argument conjunct 1 carries out. The closure cites
  Zelevinsky 1980 only at these places:
  - Proposition 1.11, in its own pieces;
  - §1.10, for the definitions in `SupercuspidalSupport`;
  - Theorem 1.9, irreducible equal-rank case, which is the proved
    `irreducibleTwoFactorProductSwap`;
  - §6.7, in `Combinatorics.RelationInversions`.

  The last module imports only Mathlib and counts inversions of a relation
  on lists. It enters through `Group.GL.UpperBruhatFiltration`. It states no
  representation-theoretic result.
- *Segment-named modules.* The closure reaches `Classification.Segments`
  and `Classification.ConstituentRelations`. Four inputs reach them: the
  helper, the nonadjacent and reducibility proofs, and
  `nonassociatedJacquetSubquotients`. All four do so through
  `SupercuspidalSupport`, and the first three also through
  `CuspidalIntegralTwistFreenessStatement`. `AssociatedProof` does not reach
  them. Through `ExponentFamily`,
  `TwoBlockExponentNonUnitarizabilityStatement` and
  `UnitaryGenericCompatibilityStatement`, the reducibility proof alone also
  reaches `Classification.Tempered`, `Classification.LanglandsData` and
  `Classification.ConstituentCompatibility`. These modules contain
  definitions (segments, linkage, real twists, segment product data, the
  head/socle and tempered/square-integrable predicates, compatibility
  propositions) and elementary lemmas. The lemmas cover equivalence
  invariance, admissibility of tempered representations, twist and rank
  arithmetic, and the unfolding of `IsLanglandsHead` and
  `IsZelevinskySocle`. They state or prove no existence, Jacquet-formula,
  irreducibility, classification, exhaustion or square-integrability
  theorem.
- *Square-integrable coefficients.* `Unitary.SquareIntegrableProof` lies in
  the closure. It proves that a representation with square-integrable
  coefficients modulo the centre is unitarizable, and it enters only through
  `supercuspidalRealUnitarization`. It is general harmonic analysis, not Ze80
  9.3 or a classification result.
- *Mathematical dependencies.* The proof uses only the five inputs above,
  and through them the published theorems listed in their Markdown. It uses
  no segment product irreducibility criterion (Ze80 4.2 or 9.7), no
  analytic or square-integrability classification (Ze80 9.3), and no
  classification or exhaustion theorem. In particular it does not use Ze80
  4.2's linked-pair converse, so there is no circularity with Ze80 §2. The
  related proposition definitions `SupercuspidalProductIrreducibilityCriterion`
  and `SupercuspidalProductReducibilityTheorem` are not used. No proposition
  definition enters as a premise.

### Derivative route (operator decision)

The task forbids assuming a derivative formula. Conjunct 1 is proved with
Bernstein–Zelevinsky derivatives. The trusted operator's decision on
request `a8463ee15d57588c8de10306748b2538` (correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca`, `sender_role: operator`) allows a fully
proved derivative route under the following conditions. Each holds for this
closure.

1. *Only BZ77's general derivative theory.* All 158 closure modules named
   `Derivative`, `Mirabolic`, `Whittaker` or `GelfandKazhdan` lie in the
   closure of the nonadjacent proof. The helper and the two Jacquet theorems
   also reach `Whittaker.Iwasawa`, but that module is the Iwasawa
   decomposition of `GL_n` and contains no derivative. The derivative inputs
   are general BZ77 theory: the derivative functors, exactness, detection
   (BZ77 3.5), BZ77 Proposition 3.8, the Leibniz filtration BZ77 4.14(c) and
   BZ77 4.4. The last is proved via Whittaker multiplicity one and
   Gelfand–Kazhdan. No segment derivative formula (Ze80 3.5 or 9.6) is
   stated or used.
2. *Every derivative result is proved, accepted and published.* These are
   the exactness, detection, BZ77 3.8, BZ77 4.4 and Leibniz proofs listed in
   the nonadjacent proof's Markdown (tasks `44f58b77`, `a925b519`,
   `2e5183b1`, `4e10058b`), and the nonadjacent proof itself (artifact
   `98cc1114`). This module uses them only through that premise-free
   theorem, and no derivative statement is a hypothesis here.
3. *Excluded tasks.* By the scans above, the closure contains none of
   `ed48ae06`, `b95105c6`, `55ad1e10`, `92aea10f`, `2ae5cbe5`, `8364e73f`,
   nor any other Independence task. It also contains no segment-socle
   statement of `8e5b4563`. Only that task's cuspidal part enters, as
   `SupercuspidalDerivatives` with its separate published proof (task
   `2e5183b1`).
4. *Reuse of the infrastructure.* The derivative functors are the published
   `Derivative.generalLinearDerivative` (task `d3e94f0f`) and `level` (task
   `dfae49d8`). The Gelfand–Kazhdan realization (task `2206daa6`) enters
   through BZ77 4.4. No derivative functor is redefined.
5. *Audit recorded.* This section records the audit. The nonadjacent and
   reducibility proofs record the same audit for their own closures.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  Proposition 1.11 and its proof, printed p.175 / PDF p.12. Its conventions
  are in §1.1 (p.170 / PDF p.7) and §§1.8–1.10 (p.174 / PDF p.11).
  Literature ID `zelevinsky-1980-induced-ii`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), §2.16(1) (printed
  pp.449–450 / PDF pp.10–11) and Theorem 4.2 (printed p.454 / PDF p.15).
  Literature ID `bernstein-zelevinsky-1977-induced-i`.

The implemented route follows Ze80's proof. Ze80 derives the dichotomy "irreducible or
the conclusions of (b)" immediately from BZ77 §2.16(1). Conjunct 2 carries
this out for the actual objects. Conjunct 3 makes the ordered Jacquet
factors explicit, using first adjointness, Jacquet exactness and a
Jordan–Hölder comparison. Ze80 cites BZ77 Theorem 4.2 for part (a), and
conjunct 1 proves that argument with derivatives. The reducibility step
completes Ze80's sketch.
