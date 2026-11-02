# Full cuspidal Jacquet modules of segment subrepresentations and quotients, proof

Author: Worker 964 (collaborator on task `b331611c-526d-4925-87fe-ea67ed6e6fed`,
whose first executor is Worker 890). This module is the final assembly. It
copies no code. Every input is a published declaration imported by Lean name.
The helper modules of the route are by Worker 964 (central-character
splitting and the two clauses) and Worker 890 (edge filtration, edge maps and
factor hypotheses). The authors of the three prerequisite theorems are listed
under "Inputs".

## Statement proved

```lean
theorem Langlands.Classification.segmentFullJacquetFormula
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentFullJacquetFormula.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.SegmentFullJacquetFormula.{uF,uV} F T` of
`Langlands.Representation.Classification.SegmentFullJacquetStatement`. The
statement pair and every pair it imports are unchanged. The theorem has no
hypotheses beyond the outer telescope `{p : ℕ} [Fact p.Prime]
(F : PadicField.{uF} p) (T : F.TopologicalData)`. It has no theorem-valued
premise. `lean_check` inspection reports `level_parameters = [uF, uV]` and
the axioms `propext`, `Classical.choice` and `Quot.sound` only.

The proposition is the conjunction of two clauses. Each quantifies over every
segment `Δ : T.Segment.{uV,uF}` with length `m = Δ.length` and cuspidal rank
`r = Δ.rank`, every actual supercuspidal representative
`A : SupercuspidalRep.{uF,uV} (n := Δ.rank)` with `Δ.base.IsRepresentedBy A`,
and every actual
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)`. Let
`β = BlockShape.uniform Δ.length Δ.rank Δ.rank_pos`, the shape `(r, …, r)`
with `m` blocks.

1. `SegmentSubrepresentationFullJacquet F T` (Ze80 3.1). If
   `T.IsSegmentSubrepresentation Δ π`, then there is a `Representation.Equiv`
   from the representation of `(T.normalizedJacquetFunctor β).obj π` to the
   representation of
   `FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos)`.
   This is `A ⊗ νA ⊗ … ⊗ ν^(m-1)A`, in increasing order.
2. `SegmentQuotientFullJacquet F T` (Ze80 9.1(*)). If `T.IsSegmentQuotient Δ π`,
   then there is a `Representation.Equiv` from the same normalized Jacquet
   module to the representation of
   `FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)`.
   This is `ν^(m-1)A ⊗ … ⊗ νA ⊗ A`, in decreasing order.

The hypotheses are the weak relations of the statement: `π` is some
irreducible subrepresentation, respectively quotient, of the increasing
segment induction `T.segmentInduced A'.obj Δ.length Δ.rank_pos` for some
representative `A'`. The proof does not strengthen them to `IsSegmentSocle`
or `IsSegmentHead`, and it assumes no existence of such `π`. The conclusions
are object-level equivalences of actual representations of the block Levi
`GL_r × ⋯ × GL_r`. Since the theorem is a proof of this exact proposition, it
claims nothing beyond the statement's Markdown.

## Implemented proof

The Lean proof is one term:

```lean
SegmentFullJacquet.segmentFullJacquetFormula_of_prerequisites F T
  (fun n => CuspidalSupport.associatedJacquetFiltration F T n)
  Geometric.padicGeometricLemma.{uF, uV}
  Geometric.padicGeometricLemma.{uF, max uF uV}
  (twoSupercuspidalProductStructure F T)
```

`segmentFullJacquetFormula_of_prerequisites` (module
`SegmentFullJacquetEdgeData`, Worker 964) derives
`SegmentFullJacquetFormula F T` from four theorem-valued arguments:

- `hassoc : ∀ n, AssociatedJacquetFiltrationTheorem.{uF,uV} F T n`, the
  Weyl-transport filtration of the Jacquet module of a quasicuspidal
  induction between associated Levis (BZ77 2.12–2.13(c));
- `hgeo : PadicGeometricLemmaTheorem.{uF,uV}`, the normalized geometric lemma
  (BZ77 2.12, Ze80 1.2–1.3) for carriers in `uV`;
- `hgeo' : PadicGeometricLemmaTheorem.{uF, max uF uV}`, the same lemma for
  carriers in `max uF uV`, where the edge families live;
- `h111 : TwoSupercuspidalProductStructure.{uF,uV} F T`, Ze80 Proposition
  1.11.

Here each argument is a published theorem without premises, so the result is
unconditional. `padicGeometricLemma` is universe-polymorphic, and it is
supplied at both universes. The rest of this section describes the route that
the helper modules implement. Their Markdown files list every declaration
with its hypotheses.

### Setting

Fix `Δ`, `A` and `π`. Write `σ i = ν^i A` for the increasing segment factors
(`T.segmentFactors A.obj m hr`), `I = i_β(σ)` for the segment induction,
`J = r_β(I)` for its normalized Jacquet module, and `γ = β.adjacentMerge k hk`
for the shape that merges blocks `k` and `k + 1`. The published
`isSegmentSubrepresentation_iff` and `isSegmentQuotient_iff` restate the
hypothesis on `π` with the quantified representative `A`. Then `π` is an
irreducible subrepresentation, respectively quotient, of `I` itself.

### The full cuspidal Jacquet module, split by a central element

- *Filtration* (`exists_segmentJacquetFiltration`, module
  `SegmentFullJacquetSplitting`). `hassoc` at rank `m r`, applied to the
  irreducible Levi-cuspidal tensor `σ_0 ⊗ ⋯ ⊗ σ_(m-1)` and the self-associated
  shape `β`, filters `J` by the transports `λ_w` of this tensor. These are
  indexed by the minimal permutations `w` conjugating the Levi of `β` to
  itself. Every graded piece is irreducible
  (`JacquetLength.isIrreducible_transport`).
- *Separating scalar* (modules `SegmentFullJacquetCentral` and
  `SegmentFullJacquetSplitting`). Let `ϖ` be the specified uniformizer and
  `z = diag(ϖ^(m^0) I_r, …, ϖ^(m^(m-1)) I_r)`, a central element of the
  uniform Levi. Let `ω` be the central character of `A`
  (`admissibleSchur_centralCharacter`). `z` acts on the piece `λ_w` by
  `segmentScalar T ω r m (blockPerm w)`, and this equals
  `(∏ j, ω(ϖ^(m^j))) · |ϖ|^(r · ∑ i, i · m^(g i))` for the block permutation
  `g = blockPerm w`. Distinct block permutations give distinct scalars
  (`segmentScalar_injective`: base-`m` digits are unique and
  `0 < |ϖ| < 1`), and `blockPerm` is a bijection onto the permutations of
  `Fin m`. So `z` has pairwise distinct scalars on the graded pieces.
- *Isolation* (module `Filtration.CentralEigenspaceSplitting`). The lemmas
  `nonempty_equiv_graded_of_sub` and `nonempty_equiv_graded_of_quot` concern
  a finite filtration `s` with irreducible graded pieces (`hs`) on which a
  central element acts by pairwise distinct scalars `c i`. They split the
  representation into eigenspaces `E_i` with Lagrange projectors, since the
  spaces are infinite-dimensional. The first lemma takes an injection
  `ι : τ → J` and a nonzero intertwiner from `τ` to a representation on which
  the element acts by `c i0`. For every `i ≠ i0` it needs a surjection `p`
  from `J` onto a representation `B` that separates `i` from `i0`: `B` has a
  filtration with irreducible pieces and distinct scalars, `i` occurs among
  them and `i0` does not, and `p ∘ ι` is injective or zero. It concludes that
  `τ` is equivalent to the `i0`-th graded piece of `s`. The second lemma is
  the dual, for a surjection `J → τ`, a nonzero intertwiner into `τ` and
  separating injections into `J`.

This central-character separation replaces the multiplicity bookkeeping of
Ze80 §2 (2.1–2.10). It needs no separate multiplicity-one theorem: distinct
scalars of `z` make the graded pieces pairwise non-isomorphic.

### The edge representations (Worker 890's modules)

For each `k` with `k + 1 < m`, merge blocks `k` and `k + 1`. The merged slot
carries the product `ν^k A × ν^(k+1) A`. These two factors are adjacent,
since `[ν^(k+1) A] = ν[ν^k A]`. Ze80 1.11(b), the second and third components
of `h111`, supplies an invariant subspace `W ≠ ⊥, ⊤` of this product. It also
supplies actual equivalences: the Jacquet module of `W` is
`ν^k A ⊗ ν^(k+1) A`, and that of the quotient is `ν^(k+1) A ⊗ ν^k A`.
Put `Y_L` for the slot family with the quotient in the merged slot and `Y_W`
for the family with `W` there. The other slots carry their slot products.

- (H1), vanishing of the Jacquet modules of each slot along every other shape,
  comes from `hgeo` (`FamilyJacquetVanishing`, via
  `segment_updateQuotient_hypotheses` and
  `segment_updateSubrepresentation_hypotheses`).
- (H2), the slot Jacquet equivalences, comes from 1.11(b) at the merged slot
  (`FamilyJacquetEquiv`).
- The published `segmentEdgeJacquetFiltration_of_padicGeometricLemma`, applied
  to `hgeo'`, gives `SegmentEdgeJacquetFiltration.{uF,uV,max uF uV}`. The
  `β`-Jacquet module of `i_γ(Y_L)` is filtered by the transports of the
  tensor with blocks `k` and `k + 1` exchanged. That of `i_γ(Y_W)` is
  filtered by the transports of `σ_0 ⊗ ⋯ ⊗ σ_(m-1)` itself. In both cases the
  index set is the set of minimal permutations that are also minimal for
  `(γ, β)`.
- One-slot exactness of product induction gives the edge maps
  `segmentEdgeQuotientMap : I ↠ i_γ(Y_L)` (surjective) and
  `segmentEdgeSubMap : i_γ(Y_W) ↪ I` (injective).
- `isMinimalRepresentative_adjacentMerge_iff` (module
  `SegmentFullJacquetSplitting`): the separating scalars on the pieces of
  `r_β(i_γ(Y_L))` are those of the block permutations with a descent at `k`.
  The pieces of `r_β(i_γ(Y_W))` correspond to the block permutations with an
  ascent at `k` (`transport_permuted_separatingScalar`, module
  `SegmentFullJacquetEdges`).

### Clause 1: subrepresentations, increasing order

This is `subrepresentation_jacquet_equiv`, module `SegmentFullJacquetAssembly`.

1. The normalized Jacquet functor is exact, so the embedding `π ↪ I` gives an
   injection `ι : r_β(π) → J`.
2. Frobenius reciprocity (`Parabolic.FirstAdjointness.equiv`, through
   `exists_jacquet_to_tensor_ne_zero`) turns `π ↪ I` into a nonzero map
   `r_β(π) → σ_0 ⊗ ⋯ ⊗ σ_(m-1)`. On its target `z` acts by the scalar of the
   identity block permutation.
3. Every block permutation `g ≠ 1` has a descent at some `k`
   (`exists_descent_of_ne_one`). Take the edge representation `i_γ(Y_L)` for
   this `k`. Its Jacquet pieces carry the scalar of `g` but not that of the
   identity. The Jacquet map of the surjection `I ↠ i_γ(Y_L)` is surjective.
   Its composite with `ι` is the Jacquet map of `π → I → i_γ(Y_L)`. This map
   is injective or zero, because `π` is irreducible. This is the test at the
   piece of `g`.
4. `nonempty_equiv_graded_of_sub` gives `r_β(π) ≃ λ_1`. The transport by the
   identity block permutation is equivalent to the increasing tensor
   (`nonempty_transport_equiv_permuted`). So
   `r_β(π) ≃ A ⊗ νA ⊗ … ⊗ ν^(m-1)A`, that is
   `T.segmentFactors A.obj m hr`.

### Clause 2: quotients, decreasing order

This is `quotient_jacquet_equiv`, module `SegmentFullJacquetAssembly`.

1. Exactness gives a surjection `J → r_β(π)` from the quotient map
   `I ↠ π`.
2. Second adjointness. `π` is admissible as a quotient of the admissible `I`
   (`isAdmissible_of_segmentQuotient`). Then
   `Parabolic.normalizedSecondAdjointness` turns `I ↠ π` into a nonzero map
   from the increasing tensor into the opposite normalized Jacquet module of
   `π`. `oppositeJacquetReverseEquiv` identifies that module with the upper
   normalized Jacquet module along `β.reverse = β`, pulled back along block
   reversal. Composing with the reversal automorphism `uniformReverse` of the
   uniform Levi gives a nonzero map into `r_β(π)` from the increasing tensor
   pulled back along `uniformReverse`. On its source `z` acts by the scalar of
   the reversal permutation (`exists_reversedTensor_to_jacquet_ne_zero`).
3. Every block permutation other than the reversal has an ascent at some `k`
   (`exists_ascent_of_ne_rev`). The edge sub `i_γ(Y_W) ↪ I` has a Jacquet
   module whose pieces carry the scalars of the permutations with an ascent
   at `k`. Its Jacquet map is injective. Its composite with `J → r_β(π)` is
   the Jacquet map of `i_γ(Y_W) → I → π`. This map is surjective or zero,
   because `π` is irreducible.
4. `nonempty_equiv_graded_of_quot` gives `λ_rev ≃ r_β(π)`. The reversal
   transport is the tensor with factor `ν^(rev i) A` in block `i`. Since
   `rev i = m - 1 - i` (`Fin.val_rev`), this is the decreasing tensor
   `ν^(m-1)A ⊗ … ⊗ νA ⊗ A`, that is `T.segmentFactorsDown A.obj m hr`.

## Normalization, factor order and universes

- *Jacquet functor.* `T.normalizedJacquetFunctor β` is the actual coinvariant
  quotient by the unipotent radical of the standard upper block parabolic of
  `β`. The Levi acts through its section, multiplied by the inverse half
  modulus `δ_P^(-1/2)` (`normalizedJacquet_mk_eq_inv_halfModulus`). This
  agrees with the statement's GL_2 check.
- *Induction.* `T.segmentInduced` is the normalized product induction
  `T.normalizedProductInductionFunctor β`, upper block parabolic induction
  with the positive half modulus `δ_P^(1/2)` (`T.leviHalfCharacter`). Block
  `i` carries `ν^i A`, with `ν = |det|` given by
  `T.determinantPowerCharacter r 1` and the residue-normalized absolute value.
  Both clauses use the increasing induction `A × νA × … × ν^(m-1)A`.
  `segmentInducedDown` is not used.
- *Factor order.* In clause 1 block `i` of the Levi acts on `ν^i A`
  (`segmentFactors`). In clause 2 block `i` acts on `ν^(m-1-i) A`
  (`segmentFactorsDown`).
- *Second adjointness.* Only clause 2 uses it, with the opposite normalized
  Jacquet module identified with the upper one through block reversal. The
  resulting conclusion is still the upper normalized Jacquet module
  `T.normalizedJacquetFunctor β`, as stated.
- *Universes.* The field lives in `uF` and the carriers of `A` and of the
  tensor products in `uV`. These are independent universe parameters of the
  theorem, and `uV` is not saturated. `π`, its Jacquet module, the segment
  induction and the edge representations have carriers in `max uF uV`. Hence
  the geometric lemma is supplied at `uV` (slot vanishing) and at
  `max uF uV` (edge filtration). `associatedJacquetFiltration` and
  `twoSupercuspidalProductStructure` are used at `uF, uV`. The equivalences
  are cross-universe `Representation.Equiv` values.
- *Generality.* The prime `p`, the p-adic field `F`, the compatible topology
  `T`, the segment, its length `m ≥ 1` and its rank `r ≥ 1` are arbitrary.

## Inputs

| Input | Lean name and module | Status, authors |
| --- | --- | --- |
| conditional assembly | `SegmentFullJacquet.segmentFullJacquetFormula_of_prerequisites`, `Classification.SegmentFullJacquetEdgeData` (with `SegmentFullJacquetCentral`, `…Splitting`, `…Adjunction`, `…Edges`, `…Assembly`) | published, artifact `f006c144`, Worker 964 |
| eigenspace isolation | `CentralEigenspaceSplitting.nonempty_equiv_graded_of_sub`, `…_of_quot`, `Filtration.CentralEigenspaceSplitting` | published, artifact `d6af361f`, Worker 964 |
| edge filtration, edge maps, (H1)/(H2) | `SegmentEdge.segmentEdgeJacquetFiltration_of_padicGeometricLemma`, `segmentEdgeQuotientMap`, `segmentEdgeSubMap`, `segment_updateQuotient_hypotheses`, `segment_updateSubrepresentation_hypotheses` in `SegmentEdgeJacquetReduction`, `SegmentEdgeMaps`, `SegmentEdgeFamilyHypotheses`, `SegmentEdgeFactorHypotheses` | published, Worker 890 |
| associated Jacquet filtration (BZ77 2.13(c)) | `CuspidalSupport.associatedJacquetFiltration`, `CuspidalSupport.AssociatedProof` | published, artifact `df6d40a0`, Workers 168 and 193 |
| geometric lemma (BZ77 2.12) | `Geometric.padicGeometricLemma`, `Geometric.GeometricLemmaProof` | published, artifact `f606bb75`, Workers 164 and 194 |
| Ze80 1.11 | `Classification.twoSupercuspidalProductStructure`, `Classification.TwoSupercuspidalProductStructureProof` | published, artifact `f10f67f3`, Worker 892 with Worker 163 |

Other published tools used by the helper modules are named above:
`Parabolic.FirstAdjointness.equiv`, `Parabolic.normalizedSecondAdjointness`,
`oppositeJacquetReverseEquiv`, `JacquetLength.isIrreducible_transport`,
`CuspidalSupport.glCuspidalTensor`, `segmentSupercuspidalFactor`
(`SegmentTensorStabilizerProof`), `segmentInductionAdmissibility`,
`admissibleSchur_centralCharacter`, and the scalar lemmas
`hasScalarCharacter_segmentFactor` and `coe_determinantPowerCharacter_scalar`
(`SegmentConstituentCentralCharacterProof`). Each is a proved, published
theorem or construction, not a premise.

## Dependency audit

### Import closure

The module imports the statement module, `SegmentFullJacquetEdgeData` and the
three prerequisite proof modules. A recursive scan of `import` lines over
Library commit `b1c8a5e809be36100da09da81385a7ca6789ae80` gives 1038 project
modules in the transitive closure, this module included. Per input:

- `TwoSupercuspidalProductStructureProof`: 879 modules. This is the closure
  audited in that module's Markdown at Library commit `c3ba00e3`, with the
  same count. It contains `AssociatedProof` (296 modules) and
  `GeometricLemmaProof` (283 modules).
- `SegmentFullJacquetEdgeData`: 489 modules. 158 of them lie outside the 1.11
  closure. These 158 modules are the helper modules of this route and the
  published tools they use: second adjointness, opposite Jacquet modules and
  reversal, central characters of segment constituents, admissibility of
  segment inductions, cuspidal embeddings of products, and the edge modules.

### Independence list

- *Task IDs and declarations.* A scan of every Lean file in the 1038-module
  closure finds none of the task-ID prefixes `8364e73f`, `30341ae4`,
  `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `8252833d`, `52e97845`, `1cb45da2`,
  `cd8ab97c`, `bf433f0a`, `5eece9e8`, `aca8805b`, `f3a69bc8`, `2ae5cbe5`,
  `e3634665`, `23189526`, `55ad1e10`, `b95105c6`, `92aea10f` or `8e5b4563`.
  It also finds none of the declaration names
  `SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
  `SquareIntegrableLanglandsClassification`,
  `SegmentSpecialEssentialSquareIntegrability`, `MultisegmentSocleExhaustion`,
  `SegmentSocleProductIrreducibility`, `OrderedMultisegmentSocleExistence`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
  `SegmentSpecialJacquetExponentNormFormula`,
  `SupercuspidalProductIrreducibilityCriterion` or
  `SupercuspidalProductReducibilityTheorem`. Nor does it find the
  segment-socle statements `SegmentSocleDerivatives`,
  `HighestDerivativeSupportShift` or
  `NonjuxtaposedSegmentSocleConstituentLevel`. `SegmentFullJacquetFormula`
  occurs only in the statement module, in `SegmentFullJacquetEdgeData` (as
  the conclusion of the conditional assembly) and in this module.
- *Source locators in the 158 new modules.* Their Lean files cite Zelevinsky
  1980 only at these places:
  - 1.11(b), in the edge modules and `SegmentFullJacquetEdgeData`;
  - 3.1 and 9.1(*), in the statement;
  - §§3.1 and 9.1 and Propositions 3.3 and 9.4, in the docstrings of the
    twist and contragredient compatibility propositions of
    `SegmentConstituentCompatibilityStatement`.

  None of these compatibility propositions is used. From that family the
  route uses only two elementary scalar lemmas of
  `SegmentConstituentCentralCharacterProof`. `hasScalarCharacter_segmentFactor`
  says that `ν^s A` has scalar character `ω ⊗ ν^s`, and
  `coe_determinantPowerCharacter_scalar` evaluates `|det|^s` on scalar
  matrices. No Lean file among the 158 cites Ze80 §3.5, §9.3, §9.6, 4.2 or
  9.7. The citations of the 1.11 closure are recorded in that module's
  Markdown.
- *One-block helper.* `SegmentQuotientJacquetSingleBlock` (Workers 485 and
  964) lies in the closure through `SegmentEdgeFactorHypotheses`. It was
  written as a one-block construction unit for the weak-segment
  Jacquet-factor work around the consumer `92aea10f`. The route uses only its
  `singleBlockNormalizedJacquetEquiv`: for a one-block shape, the Jacquet
  quotient map is an equivalence, since the half modulus is one. The module
  composes published maps. It proves neither the consumer's norm formula nor
  its all-shape factor assertion (task `15540667`, not imported). Its own
  96-module closure contains no `SegmentFullJacquet` module. So it is not a
  conclusion, proof successor or consequence of an excluded task, and it
  creates no circularity.
- *Segment-named modules.* The closure reaches `Classification.Segments`,
  `ConstituentRelations`, `CanonicalConstituents`, `ConstituentCompatibility`
  and its algebraic proof, `SegmentConstituentCompatibilityStatement` and its
  central-character proof, and the tempered and spherical statement modules
  (`TemperedInductionStatement` and `TemperedSupportStatement` through
  `Exponents.DualJacquetStatement` in the second-adjointness proof,
  `SphericalClassificationStatement` through
  `isAdmissible_of_surjective`). These contain definitions, proposition
  definitions and elementary lemmas about twisting, central characters,
  admissibility and the unfolding of head and socle predicates. None states
  or proves an existence, Jacquet-formula, irreducibility, classification,
  exhaustion or square-integrability theorem used here.
- *Mathematical dependencies.* The proof uses the three prerequisite theorems
  and published lower tools: Jacquet exactness, Frobenius reciprocity, second
  adjointness, opposite Jacquet reversal, the geometric lemma, the associated
  filtration and Ze80 1.11. It uses no segment product irreducibility
  criterion (Ze80 4.2 or 9.7), no segment derivative formula (Ze80 3.5 or
  9.6), no analytic or square-integrability result (Ze80 9.3), and no
  classification or exhaustion theorem. Ze80 1.11 concerns two supercuspidal
  representations. It is the lower ingredient named by the task, not such a
  criterion. No proposition definition enters as a premise.

### Derivative results

Neither this module nor the 158 modules outside the 1.11 closure contain a
derivative module. All 158 closure modules named `Derivative`, `Mirabolic`,
`Whittaker` or `GelfandKazhdan` lie in the 1.11 closure. The only one of them
reached from `SegmentFullJacquetEdgeData` is `Whittaker.Iwasawa`, the Iwasawa
decomposition of `GL_n`, which contains no derivative. Derivatives enter
only through conjunct (a) of 1.11, the published premise-free theorem
`twoSupercuspidalNonadjacentProductIrreducible`, which proves BZ77
Theorem 4.2 with Bernstein–Zelevinsky derivatives. This task's clause "do not
assume a derivative formula (Ze80 3.5 or 9.6, BZ77 derivative results)" was
inherited verbatim by the 1.11 task `ab61f565`. The trusted operator's
decision on request `a8463ee15d57588c8de10306748b2538` (correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca`, `sender_role: operator`) interprets it.
The clause forbids assuming derivative results without proof and any
circular dependency. It does not forbid a fully proved BZ77 derivative
route. The conditions of that decision hold for this closure:

1. only BZ77's general derivative theory is used, and no segment derivative
   formula (Ze80 3.5 or 9.6) is stated or used;
2. every derivative result is proved, accepted and published;
3. the closure contains no excluded task, nor the segment-socle part of task
   `8e5b4563`.

The 1.11 Markdown records the details of this audit. No derivative result is
a hypothesis anywhere in this proof.

## Relation to the source proof

Ze80 derives 3.1 and 9.1(*) from §2: Theorem 2.8, Corollary 2.9 and
Proposition 2.10, with 2.2, 2.4 and 2.7. That route bounds the Jacquet module of
each irreducible constituent of `ρ × νρ × … × ν^(m-1)ρ` through 1.11 on
adjacent pairs and multiplicity-freeness. The implemented route uses the same
ingredients in another form:

- the geometric lemma and the associated filtration give the full cuspidal
  Jacquet module;
- 1.11 on adjacent pairs gives the edge representations;
- Frobenius reciprocity and second adjointness give one nonzero map;
- a central element with distinct scalars replaces the multiplicity
  bookkeeping.

The conclusion is the object-level equivalence of the statement.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980): 3.1
  (printed pp.180–181, PDF pp.17–18), 9.1 with (*) (printed p.197, PDF p.34),
  §2 (printed pp.176–180, PDF pp.13–17) and Proposition 1.11 (printed p.175,
  PDF p.12). Literature ID `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. No
  errata note for this source exists in the Library.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977): Lemma 2.12 and 2.13.
  Literature ID `bernstein-zelevinsky-1977-induced-i`.
