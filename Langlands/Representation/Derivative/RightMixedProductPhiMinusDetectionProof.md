# Detection by Φ⁻ in a right mixed product

## Exact statement and conventions

`Langlands.Derivative.rightMixedProductPhiMinusDetection` proves the existing
proposition `Langlands.Derivative.RightMixedProductPhiMinusDetection.{uF,uV} F T`
from [MixedProductDerivativeStatement](MixedProductDerivativeStatement.md), with
outer telescope

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
```

The field and representation universes `uF` and `uV` are independent. After
installing the supplied `T.topology`, the proposition quantifies every unitary
additive character `ψ`, every `k r : ℕ`, every smooth complex representation
`B` of `mirabolic r F.Carrier`, every smooth complex representation `A` of
`GeneralLinear (k+1) F.Carrier`, and every nonbottom invariant subrepresentation
`U` of `(T.rightMixedProductFunctor (k+1) r).obj (B,A)`. It asserts nontriviality
of the carrier of

```lean
(Mirabolic.phiMinus T ψ (k + r)).obj
  ((mirabolicRankCast T (Nat.add_right_comm k 1 r)).obj
    (SmoothRep.subrepresentation _ U))
```

Here `mirabolic r` is the source's `P_(r+1)`. The mixed product has ambient
group `mirabolic ((k+1)+r)`, or `P_(k+r+2)`. The equality
`Nat.add_right_comm k 1 r` is precisely `(k+1)+r = (k+r)+1`; its actual
`mirabolicRankCast` transports the subrepresentation to the source of `phiMinus`
with index `k+r`. No representation is replaced by an abstract isomorphic one.
The mixed-product carrier lives in `Type (max uF uV)`; the radical-triviality
helper is instantiated at that carrier universe when applied to `U`.

All `k,r`, including `k=0` and `r=0`, are covered. Thus the smallest GL factor
is `GL_1`, and `B` can be a representation of `P_1`. The proof imposes no
admissibility, irreducibility, dimension, length, genericity, chosen-vector,
canonical-topology or exactness premise.

## Original source and implemented route

The original source is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant passages are §§3.2–3.3, printed pp.450–452 (one-based PDF pp.11–13),
§4.12(III) and Proposition 4.13(d), printed pp.457–458 (PDF pp.18–19), and the
proof in §7.3, printed p.471 (PDF p.32). These original passages, including the
matrix diagrams, were read and visually inspected. The registered literature
index and available project errata notes were checked; no applicable correction
to these passages was found.

The theorem is exactly the source's 4.13(d) in the published Library conventions.
The implemented proof uses the published Fourier proof that vanishing `Φ⁻`
forces trivial radical action. Its support argument is an internal simplification:
it lifts compact quotient support to a compact set in the group and applies a
single globally continuous inverse-matrix entry. It does not construct a closed
radical orbit or descend a coordinate map to that orbit. The matrix and topology
lemmas below are proved in this module; they are not additional results being
attributed to the original paper.

## Proof

Put `n = (k+1)+r`, `G = mirabolic n F.Carrier`, and
`H = MixedProduct.rightSubgroup (k+1) r F.Carrier`. In the coordinate partition
`(r,k+1,1)`, the subgroup consists of the actual matrices

```text
[d  X  z]
[0  a  0]
[0  0  1].
```

This is the published case (III) subgroup, with the last coordinate of the
mirabolic factor retained at the end. The quotient map `q` is
`Induction.quotientMap H`, whose relation is `QuotientGroup.rightRel H`; its
points are the left cosets `H g`.

### 1. The inverse entry on the relevant cosets

For `c : Fin n → F.Carrier`, let `v(c) = radicalElement c`, the actual radical
matrix with identity upper-left block and final column `c`. The private lemma
`radicalElement_mul_last` proves, over any commutative ring, that the
`(i,last)` entry of `v(c) g` is `g(i,last)+c(i)`. Matrix multiplication and the
fixed final row of a mirabolic matrix give this formula directly.

Choose the first middle-block row

```text
i = rightIndex (k+1) r (Sum.inr 0) = (r : Fin n).castSucc.
```

It exists because `k+1` is positive. The proof of the displayed equality is a
`Fin.ext` calculation, with the bound `r<n` discharged arithmetically. The final
column is `Fin.last n`; `rightIndex_last` identifies it with the final coordinate
of the first, mirabolic block in the subgroup's coordinate order.

The private lemma `inverse_entry_of_same_right_coset` proves

```text
q(g) = q(v(c)⁻¹)  implies  (g⁻¹)(i,last) = c(r).
```

Indeed quotient equality gives `h=g v(c) ∈ H`, so `g⁻¹=v(c) h⁻¹`.
Since `h⁻¹ ∈ H`, `mem_rightSubgroup_iff_entry` makes its middle-row/final-column
entry zero. The preceding multiplication formula then gives exactly `c(r)`.
The inverse in `q(v(c)⁻¹)` fixes the sign of this formula. The argument uses
subgroup closure under inversion, not a formula for an arbitrary diagonal
block inverse.

### 2. A radical-invariant function vanishes at one

The private lemma `eval_one_eq_zero_of_radical_invariant` considers a vector
`f` in the actual right mixed product satisfying

```text
rightMixedEval f (u⁻¹) = rightMixedEval f 1
```

for all radical elements `u`. Suppose its value at one is nonzero. Then every
`q(v(c)⁻¹)` belongs to `Induction.quotientSupport H (rightMixedEval f)`.
The published `T.rightMixedEval_isCompact_quotientSupport` makes that projected
support compact. The group is locally compact using
`T.generalLinearLocallyCompactSpace` and `Mirabolic.locallyCompactSpace`; `H`
is closed by `rightSubgroup_isClosed` with the supplied Hausdorff field topology.
The published theorem
`QuotientIntegration.leftQuotient_exists_isCompact_image` therefore supplies a
compact set `C ⊆ G` whose image is exactly this support.

Define on all of `G`

```text
E(g) = (g⁻¹)(i,last).
```

The actual matrix-entry map is continuous, and group inversion is continuous,
so `E` is continuous. For any `t ∈ F.Carrier`, choose the constant vector
`c(j)=t`. The support property and `q(C)=quotientSupport` supply `g ∈ C` with
`q(g)=q(v(c)⁻¹)`. Part 1 gives `E(g)=t`. Thus `E(C)=F.Carrier`, making the
whole field compact.

The private lemma `not_isCompact_field` rules this out for the supplied `T`.
It installs `T.valuativeRel`, `T.localField` and `T.fieldT2`. The algebra map
from `Padic p` into `F.Carrier` is injective, so the field is infinite. Mathlib's
`DivisionRing.finite_of_compactSpace_of_t2Space` says that a compact Hausdorff
topological division ring is finite, a contradiction. This uses no replacement
of `T` by a canonical topology. Hence `rightMixedEval f 1=0`.

Only the existence of the row `Sum.inr 0` uses positivity of the GL rank. The
zero-size first block when `r=0` and the one-dimensional middle block when
`k=0` do not affect any calculation.

### 3. Vanishing Φ⁻ and invariant subrepresentations

Assume that the carrier in the target is not nontrivial, hence is subsingleton.
The published theorem `Mirabolic.radical_acts_trivially_of_phiMinus` from
[MirabolicHighestDerivativeDescent](MirabolicHighestDerivativeDescent.md)
then makes the radical act trivially on `SmoothRep.subrepresentation _ U`.
The private wrapper `radical_triviality_rankCast` handles an arbitrary equality
`a=m+1` by `subst a`, reducing the actual rank cast to its reflexive definition.
It then applies the published theorem directly. The public proof instantiates
it with `a=(k+1)+r`, `m=k+r`, and `Nat.add_right_comm k 1 r`.

For clarity, that published radical-triviality theorem is a proved Fourier
argument, not an application of an unproved functor exactness statement. For
`y=ρ(u)x-x`, its trivial-character radical coinvariant is zero. Vanishing of the
nontrivial-character quotient and transitivity of the Levi action on nonzero
row characters put `y` in the relations for every coordinate character.
`Mirabolic.eq_zero_of_forall_mem_relations` turns this into `y=0`: smoothness
fixes `y` on a sufficiently small lattice box; relation membership makes the
character averages vanish on sufficiently large boxes; the finite Fourier
lemmas `exists_forall_characterAverage_eq_zero` and
`eq_zero_of_forall_characterAverage_eq_zero` in
[MinusVanishing](MinusVanishing.md) finish the argument.

Now take any `f ∈ U` and any `x ∈ G`. The actual invariant action gives the vector
`v = U.toRepresentation x ⟨f,hf⟩` in `U`. Apply radical triviality to `u⁻¹` and
`v`, then evaluate at one. The published right-translation action on
`T.rightMixedEval` gives the invariance hypothesis of Part 2. Consequently
`rightMixedEval v 1=0`, which is `rightMixedEval f x=0`. As this holds for every
`x`, `T.rightMixedEval_injective` gives `f=0`. Extensionality of actual
subrepresentations, implemented through `Subrepresentation.toSubmodule_injective`
and two submodule inclusions, gives `U=⊥`, contradicting its hypothesis.

### Normalization

Both input functors are exactly the published determinant-normalized functors.
For case (III), the right-product total character is
`ν_r(d)^(s/2) ν_s(a)^(-(r+1)/2)` with `s=k+1`, and
`rightLeviCharacter_eq_mul` retains its rectangle-half factor and the extra
`ν_s(a)^(-1/2)` factor. `phiMinus` uses the published inverse-half determinant
twist of the descended action. That twist leaves the coinvariant carrier
unchanged, as used by the radical-triviality theorem.

The support contradiction uses only the existing function realization,
right translation, injectivity and compact projected support. Its validity is
independent of the particular covariance character. No equality of determinant
powers with an actual Haar modulus is required, assumed, or proved here.
In particular, the formal character formulas of `MixedProducts` are not being
misrepresented as a formal Haar-modulus comparison.

## Published inputs and their proof provenance

All mathematical inputs are imported by their Lean names from the unchanged
Library base `b22e185743f7c318f709e14e422801f4360105d5`. The following receipt
identifiers record the audit of that public content; none is a mathematical
hypothesis. Each cited candidate has independent semantic acceptance and public
integration, with no unresolved reviewer qualifications.

| Published input | Verified receipt and publication | Use and provenance |
| --- | --- | --- |
| `MixedProductDerivativeStatement` | `845a8c59-87c5-4a25-bc55-aca6bdf165ad`, Reviewer 5791; `6cb15022e66f7f1f171e7e8d563e74b92072e5ba` | Supplies the exact proposition only. No other proposition defined alongside it is used as a theorem. |
| `MirabolicHighestDerivativeDescent` and `MirabolicDerivativeVanishing` | `f957ae76-3779-4436-bdcb-98bc63561e07`, Reviewer 4988; `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | Both pairs were included in the accepted proof's repository paths and match the frozen and integrated content. The semantic review explicitly checks the radical-triviality/Fourier argument. The former imports the latter to maintain a module chain; the radical-triviality proof does not use its joint-detection conclusion or any later pairing theorem. |
| `MinusVanishing` | `c6026915-8731-45a8-bd21-ef1ac39654b8`, Reviewer 4480; `771cfc69d1ff795522e29cdead1b7c40f1a1c308` | The current pair matches its frozen publication. Uses compact radical-box averaging, elementary Levi transitivity and finite Fourier inversion; no segment, finite-length or Whittaker-finiteness result is an input. |
| `Mirabolic.MixedProducts` | `ba418fcc-1120-4c27-b77c-05734e9bc195`, Reviewer 4998; `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` | The current pair matches the accepted documentation correction's frozen publication. The concrete compact-induction/smooth-part construction proves the evaluation, action, support and injectivity laws used here. Its normalization scope is as explained above. |
| `Analysis.Local.QuotientTopology` | `c3fe4e0d-cd8f-41b2-ac23-9a4d45950dd7`, Reviewer 253; `ef274d37c255e4b25a990dd377d10e2da436807d` | Current content matches the integrated publication. Integration consolidated the quotient projection into an abbreviation for `Induction.quotientMap` and added its defining import; the frozen pre-integration pair is therefore not byte-identical. The compact-lift theorem uses an open quotient map, compact neighborhoods and a finite subcover, followed by intersection with the closed preimage of the compact set. |
| `Group.GL.MirabolicMixedProductSubgroups` | `c2f9e770-dee5-4272-b796-46339512ca35`, Reviewer 4335; `4e6ed28ccc687ea7e0123318bc2516e1f4b79d11` | Current content matches the frozen and integrated pair. Provides actual matrix subgroups, coordinate identities and closedness, proved by matrix algebra and inherited topology. The review checks all ranks and its ten-module independent project closure. |

The complete required pairs `MixedProductDerivativeStatement`, `MixedProducts`,
`MirabolicMixedProductSubgroups`, `MirabolicMinus` and `Homogeneity`, and the
helper pairs used here, were read. The latter include `MinusVanishing`,
`MirabolicHighestDerivativeDescent`, `MirabolicDerivativeVanishing`,
`Filtration.InvariantBilinear`, `Induction.Definitions`, `QuotientTopology`,
`Group.GL.Mirabolic`, `MirabolicRadical`, `Group.GL.Padic` and the local-field
construction/topology pairs. The supplied topology and group instances are
those of these existing definitions. Mathlib's compact-field theorem is from
the pinned `Mathlib.Topology.Algebra.Field` source.

The shared lower proof routes were checked as follows.

- `MirabolicMinus` constructs character coinvariants and determinant twists;
  `Iteration` and `Homogeneity` construct actual rank transports and iterate
  those functors. Their Proposition definitions and zero-carrier laws do not
  supply an assumed detection theorem. Here the rank transport is eliminated
  by substitution.
- `MinusVanishing` reaches the coordinate-box and finite-mean machinery through
  `MirabolicLatticeBox`, `Jacquet.CharacterAveraging`, and the elementary
  last-row/lattice modules. The modules under `RankinSelberg` in this closure
  supply quotient measures, last-row compactness and cutoffs; they supply no
  functional equation, local-factor classification, segment formula or
  Whittaker-finiteness theorem.
- The `Whittaker.Algebraic` and `Whittaker.GeneralLinear` imports contain the
  algebraic character/model definitions, elementary unipotent laws and
  matrix-coefficient identities needed by that machinery. They do not import
  any of the prohibited coinvariant-finiteness statements or their proofs.
- `MixedProducts` reaches tensor products, smooth parts, pullbacks and normalized
  induction through the published `Induction` and `Tensor` construction modules.
  Compact support is part of the actual induced-function space. No derivative
  compatibility, Leibniz filtration or irreducibility theorem is hidden in this
  construction. Its shared helpers are algebraic/tensor/topology constructions,
  not assumptions taken from consumers.
- `QuotientTopology` reaches only the actual quotient and induction definitions,
  plus Mathlib topology. `Filtration.InvariantBilinear` contributes generic
  algebraic pairing infrastructure to the imported Descent module; this proof
  uses none of its pairing or filtration results. `Category.Basic` defines a
  group-algebra finite-length predicate, but neither this proof nor its shared
  lower proofs derive or invoke a mirabolic finite-length theorem from it.

## Condition-by-condition independence audit

Both complete exclusion sets in the task's context bind this proof and every
prerequisite. The table below audits their union, including the operator's
conditions. Every exclusion includes the mathematical conclusion, its proof
successors and its transitive proof dependencies/downstream consequences; an
absence claim is not limited to an exact task identifier or filename. The full
project import closure is listed in the next section. It has no classification,
segment, cuspidal-derivative, product-irreducibility or Whittaker-finiteness module.
The actual proof dependencies are the elementary constructions and accepted
Fourier lemmas described above. No conditional draft, pending repair, unproved
Prop definition, citation or consumer conclusion is used as proof evidence.

| Binding condition or excluded conclusion | Audit result |
| --- | --- |
| BZ77-only general derivative route; no unproved derivative input | The only substantive general derivative input is the independently accepted and published radical-triviality/Fourier route identified above. The remaining derivative imports construct the specified functors, statements and rank casts. |
| Ze80 segment derivative formulas §§3.5 or 9.6; six-statement consumer `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` items (b),(d),(e),(f) | No segment formula, parent conjunct, or proof depending on one is imported or used. |
| Segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | Neither it nor its cuspidal-derivative part is needed. The proof is for arbitrary smooth factors. |
| `OrderedMultisegmentSocleExistence`, `23189526-80b0-4828-a6d4-7ebec2cbeef5` | No ordered-socle construction or existence input. |
| `MultisegmentSocleExhaustion`, `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No socle exhaustion or classification input. |
| Analytic segment classification, `aca8805b-054f-4d56-8045-12db7f623404` | No analytic segment or classification module. |
| `UnlinkedSegmentSocleProductIrreducible`, `23e98d90-6055-4e35-91a9-b0f5d8a84961` | No segment product irreducibility input. |
| `LinkedSegmentSocleReverseProductStructure`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`; `LinkedSegmentSoclePairReducible`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | No linked-product structure or reducibility input. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, `7ff2a1e9-89dc-439e-a861-a567b3db92bf` | No juxtaposed-segment construction or quotient-hom input. |
| `SegmentSocleProductIrreducibility`, `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No final socle-product criterion. |
| `AdjacentUnlinkedSegmentSocleSwap`, `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | No adjacent socle commutation input. |
| `TwoSegmentSocleCommutation`, `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No two-segment commutation input. |
| `LinkedSegmentSocleGluing`, `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | No gluing input. |
| `SegmentHeadProductIrreducibility`, `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | No special-head product criterion. |
| Special-head exhaustion, `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No special-head or multisegment exhaustion. |
| Ordered special/strong-head existence, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No ordered-head existence input. |
| Quotient coverage, `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No classification quotient coverage. |
| Ordered special-segment conversion, `8252833d-c269-41a9-824c-5879e531b23b` | No head/socle conversion input. |
| Tempered block uniqueness, `52e97845-36bb-457d-b76f-70753334b88c` | No tempered uniqueness input. |
| `SquareIntegrableLanglandsClassification`, `1cb45da2-7007-4351-a694-594fb148b8d1` | No square-integrable classification. |
| Square-integrable exhaustion, `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No square-integrable exhaustion. |
| Regular exhaustion, `bf433f0a-921a-428c-b0c0-6475438125ac` | No regular exhaustion. |
| `GenericSegmentProductUniqueness`, `30341ae4-65f2-4a0e-9283-763db01a409e` | No generic segment uniqueness or parent consumer assumption. |
| `SegmentSpecialEssentialSquareIntegrability`, `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No forward special-segment square-integrability input. |
| Individual special-head/reverse-socle existence, `67279e36-f3c2-42e3-9302-11729784042e` | No individual head or reverse-socle construction. |
| Individual segment-socle/reverse-head existence, `4ca79bbd-589e-476b-9f65-661e799984b5` | No individual socle or reverse-head construction. |
| `SegmentFullJacquetFormula`, `ed48ae06-964c-4c84-9e62-978f5a953ca7`, and its exact proof successor | No segment full-Jacquet formula or consequence. |
| `SegmentHeadJacquetFormula`, `55ad1e10-62d8-46b7-a081-909ef0056426` | No segment head-Jacquet formula. |
| `SegmentSocleJacquetFormula`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | No segment socle-Jacquet formula. |
| `SegmentSpecialJacquetExponentNormFormula`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No segment exponent-norm formula. |
| Segment product criteria Ze80 4.2 or 9.7; analytic/square-integrability Ze80 9.3; circular use of Ze80 4.2 for Proposition 1.11 | No result from Ze80 is used in the proof or shared lower proof routes. |
| Combined Ze80 §5.4 reduction and mirabolic strong indecomposability, including `ff4738d8-47e3-433b-bedc-629bc2d492a7` | No strong-indecomposability consumer conclusion is imported or assumed. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | No two-supercuspidal irreducibility input. |
| `TwoSupercuspidalProductStructure`, `ab61f565-1427-4746-ba77-46097563e962`, including adjacent composition/Jacquet conjuncts | No full-product structure or its conjuncts. |
| Ze80 6.2 consumer `b711af72-fdf9-4b32-a450-937911426822` and GL Leibniz consumer `3238f371-e9a2-42ce-8b5d-9c4d3400ff55` | Neither consumer establishes this input. Their conclusions, successors and dependents are outside the closure. |
| `SupercuspidalCoinvariantFinitenessStatement`, all-character single-block `62de5903-b616-4b5c-88eb-a066b77c5467` | No supercuspidal coinvariant finiteness statement, proof, successor or consequence. |
| `IrreducibleCoinvariantFinitenessStatement`, `5ab445dc-d2b4-4072-80d1-6370870a4a26` | No parent Whittaker finiteness or consequence. |
| `LeviCuspidalCoinvariantFinitenessStatement`, `3ff5c8fb-397c-4345-bcb3-5d98a0993d18` | No Levi-cuspidal finiteness or consequence. |
| Mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | No such route, pending repair, or assumption. Defining `HasFiniteLength` in a general category module supplies no finite-length theorem and is not used here. |
| Operator-paused minus exactness `b65bc667-6951-4bd5-82af-10fb7046df7f`; Worker 127's pause | No minus-exactness module or theorem is used, no replacement task was created, and the paused worker/task was not contacted or resumed. Existing finite-length ownership/waits were also left intact. |
| BZ77 4.13(a)–(c), 4.14 and other mixed-product/Leibniz consumers | None is used. Companion proposition definitions are not treated as proved results. |
| Supplied topology, normalization and full rank/universe scope | The exact supplied objects are retained; the proof uses carrier-level vanishing and character-independent support. No extra hypothesis or Haar-modulus comparison is smuggled into the target. |

## Complete transitive project import closure

The four direct imports are
`Langlands.Representation.Derivative.MixedProductDerivativeStatement`,
`Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent`,
`Langlands.Analysis.Local.QuotientTopology`, and
`Mathlib.Topology.Algebra.Field`. Recursively resolving the project imports in
the audited Library yields exactly the following 101 modules, including the
three project roots and excluding this new proof module. There are no missing
project imports. All their Lean/Markdown pairs remain unchanged by this
contribution. The names under `Whittaker` and `RankinSelberg` have the elementary
roles described above; their presence is not use of the excluded finiteness
or consumer theorems.

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientTopology
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.InvariantBilinear
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```
