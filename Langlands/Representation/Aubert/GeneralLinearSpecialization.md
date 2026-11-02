# Actual general-to-GL Aubert specialization

This internal adapter specializes the existing general subgroup constructions in
`Aubert.General.Parabolic` and `Aubert.General.AlternatingOperator` to the actual
upper block parabolics of `GL_n`. It constructs natural comparisons of the full
smooth functors and equalities of their maps on the existing exact finite-length
Grothendieck groups. Its final equality specializes the general unadjusted
operator to the unchanged `Langlands.Aubert.alternatingOperator`.

The normalized comparisons are conditional on one explicitly named structural
input: the Haar conjugation modulus on the entire upper parabolic equals the
explicit block modulus after diagonal projection. The module does not prove
this Haar identity. In the p-adic specialization all finite-length and
short-exact-sequence preservation properties are derived from the existing GL
proofs; they are not additional assumptions on representations.

## Actual subgroups and projection

Fix an existing `GeneralLinear.BlockShape n`, denoted `B`. The ambient group is
`GeneralLinear n F`, the actual upper parabolic is `B.parabolic F`, the embedded
block-diagonal Levi is `B.leviSubgroup F`, and the radical in the ambient group is
`B.unipotentSubgroup F`. The latter is the image of the kernel
`B.unipotentRadical F` of the diagonal projection inside the parabolic. The
product Levi is `B.Levi F`; its actual embedding is `B.leviEquiv F` onto the
embedded subgroup. These constructions are reused from `Group.GL.Blocks`.

For every commutative ring `F`,
`BlockShape.parabolic_le_normalizer_unipotentSubgroup` follows from normality of
the kernel and its image under the parabolic inclusion.
`BlockShape.generalSemidirectDecomposition` uses the existing trivial
intersection and product decomposition to give the actual general predicate
`IsSemidirectDecomposition P M U`. No group decomposition is assumed as a data
field. `generalSemidirectDecomposition_projection` proves that the general
quotient/complement projection is exactly

    g ↦ B.leviEquiv F (B.leviProjection F g).

Its proof uses the existing section of diagonal projection: the residual factor
has projection one, hence belongs to the kernel radical. The actual quotient
and its continuous equivalences with the product and embedded Levi are reused
through `Parabolic.LeviModelTransport` and `Group.GL.ParabolicQuotientTopology`.

## Full modulus prerequisite and half conventions

The smooth comparisons assume a commutative topological ring `F : Type uF`,
`T2Space F`, local compactness and `NonarchimedeanGroup` for `GeneralLinear n F`.
The latter supplies its topological group structure. Coefficients are `ℂ` and
the representation-carrier universe `uV` is independent of `uF`.

For a supplied full character `δ : B.Levi F →* ℝ≥0ˣ`, the Prop-valued definition
`BlockShape.GeneralModulusCompatibility δ` is the equality

    HaarModulus.closedRestrictCharacter U hU P hPU
      = δ.comp (B.leviProjection F).

Here `P`, `M` and `U` are the actual subgroups above, and `hPU` is the proved
normalization. The equality is on every element of `P`, including its radical;
a comparison merely on `M` is insufficient for this hypothesis.

Given an open kernel of `δ`, `blockHalfCharacterOf` is the smooth complex
character obtained from its positive real square root. `generalHalfCharacter_eq`
identifies the general positive induction half on all of `P` with this block
half after projection. `generalLeviModulus_eq` restricts the full comparison to
the actual embedded Levi, using the inverse of `B.leviEquiv F`.
`generalInverseHalfCharacter_eq` then identifies the general Jacquet inverse
half with the inverse block half after that same inverse Levi equivalence.
Thus the existing positive induction half and inverse Jacquet half are retained.

The corrected `General.Parabolic` documentation identifies its generic induction
with BZ77 induction only under `IsUnimodularModulus`: the generic character is
evaluated on all of `P`, whereas the source character is inflated from the
Levi. Generic Jacquet restriction has the source identification without that
additional hypothesis. The comparison here uses the stronger, explicit full
character equality above; it never substitutes a Levi-only identity for it.
In particular, the equality forces triviality on the radical through the kernel
of the actual diagonal projection. This module does not prove the full equality
or discharge the general unimodularity obligation.

## Full smooth functor comparisons

`Parabolic.productToEmbeddedLevi B` pulls a product-Levi action back along
`(B.leviEquivContinuous F).symm`. It retains the vector space and every linear
intertwiner. `BlockShape.embeddedToProductLevi` is inverse change of acting
group, using `B.leviEquivContinuous F`.

For an arbitrary smooth product-Levi object `A`,
`generalInducingRepresentation_eq` identifies the actual general covariance
after this transport with the existing block covariance:

    δ(B.leviProjection F g)^(1/2) • A.representation (B.leviProjection F g).

`generalInducingEquiv` is the identity on vectors.
`generalInductionIso` induces it on full smooth covariant functions:

    productToEmbeddedLevi B ⋙ General.normalizedInductionFunctor h hU
      ≅ B.normalizedInductionFunctorOf (B.blockHalfCharacterOf δ hδ).

`generalInductionIso_hom_eval` states that this comparison retains every
function value at every ambient group element. The naturality proof uses the
unchanged pointwise postcomposition by each original intertwiner. On arbitrary
embedded-Levi objects, `generalEmbeddedInducingEquiv` and
`generalEmbeddedInductionIso` give the corresponding comparison

    General.normalizedInductionFunctor h hU
      ≅ B.embeddedToProductLevi ⋙ B.normalizedInductionFunctorOf (B.blockHalfCharacterOf δ hδ).

This second comparison covers the entire source category, which is needed to
transfer induction preservation.

`generalJacquetLinearEquiv` compares the two genuine quotient carriers using
the existing `B.jacquetModuleEquiv` and `Jacquet.Localization.trivialEquiv`.
`generalJacquetLinearEquiv_mk` sends the class of `v` to the class of `v`.
The inverse-half identity proves that it intertwines the embedded Levi actions,
giving `generalJacquetEquiv` and the natural isomorphism

    B.normalizedJacquetFunctorOf δ hδ ⋙ productToEmbeddedLevi B
      ≅ General.jacquetFunctor h hU.

`generalJacquetIso_hom_mk` gives its formula on every quotient representative.
Naturality is proved by reducing to these representatives, on which both maps
send `[v]` to `[f(v)]`. These comparisons apply to the full smooth categories;
they do not impose finite length or admissibility on the objects. Jacquet
retains carrier universe `uV`, while induction has carrier universe
`max uF uV`, as in the existing functors.

## Preservation and full exact K0

`generalParabolicFiniteLength_of_block` derives the general conjunction
`General.ParabolicFiniteLength` from the four preservation properties of the
actual block functors. Pullback along the continuous Levi equivalence preserves
finite group-algebra length and actual short exactness. The natural
isomorphisms transfer these properties using
`SmoothRep.PreservesFiniteLength.of_iso` and
`SmoothRep.PreservesFiniteLengthShortExact.of_iso`. The latter helpers are in
`Smooth.FiniteLengthGrothendieckIso` and use actual linear bijections and
naturality squares, rather than any classification result.

The p-adic section fixes `p` prime, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`. It installs `T.topology`, its topological ring proof,
`T.fieldT2`, `T.generalLinearLocallyCompactSpace n`, and
`T.generalLinearNonarchimedean n`. The Prop-valued target
`Parabolic.GeneralLinearModulusCompatibility F T B` is precisely the preceding
full modulus equality with `δ = T.leviModulus B` for this topology. Its positive
half `blockHalfCharacterOf δ (T.isOpen_ker_leviModulus B)` is definitionally the
existing `T.leviHalfCharacter B`.

`Parabolic.generalLinearParabolicFiniteLength` derives all four preservation
properties at the existing saturated carrier universe `max uF uV`. Its exact
inputs are the already proved declarations:

| Property of the existing block functor | Reused proof |
| --- | --- |
| Induction preserves finite length | `Parabolic.normalizedInductionK0_hasFiniteLength` |
| Induction preserves finite-length short exact sequences | `Parabolic.FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact` |
| Jacquet preserves finite length | `Parabolic.normalizedJacquetK0_hasFiniteLength` |
| Jacquet preserves finite-length short exact sequences | `Parabolic.FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact` |

Write `E = Parabolic.embeddedLeviK0Equiv B`. The following are equalities of
whole integer-linear maps, using the original exact finite-length K0 of actual
smooth representations modulo relations from all actual short exact sequences,
including nonsplit ones:

| Declaration in `Langlands.Parabolic` | Equality |
| --- | --- |
| `generalInductionK0_eq` | `General.inductionK0 = normalizedInductionK0 ∘ E.symm` |
| `generalJacquetK0_eq` | `General.jacquetK0 = E ∘ normalizedJacquetK0` |
| `generalInductionJacquetK0_eq` | The general and existing induction-after-Jacquet composites agree |

The first two proofs use `FiniteLengthGrothendieckGroup.map_eq_of_iso` and
`map_comp` for the actual natural isomorphisms. The third cancels the inverse
and forward linear equivalence on every exact class. No free label group,
restricted generator family or inference of module isomorphism from class
equality enters these proofs. Their only remaining input is the named full
modulus comparison.

## The existing unadjusted operator and rank zero

`Langlands.Aubert.generalAlternatingOperator_eq` takes the full modulus
comparison for every `B : BlockShape n`. It applies the existing general
operator directly to the families of actual parabolics, embedded Levis and
radicals indexed by `I : Finset (Fin (n - 1))`, with

    B(I) = (BlockShape.leviRootSubsetEquiv n).symm I.

The decomposition and closedness are proved above, and preservation is supplied
by `generalLinearParabolicFiniteLength`. The theorem proves equality to the
unchanged `Langlands.Aubert.alternatingOperator F T n`. Its proof rewrites the
existing `alternatingOperator_eq_rootSubset_sum` term by term with the full
composite equality. The existing root equivalence identifies
`I.card = n - B(I).length`, so the sign remains exactly `(-1)^(n - B.length)`.

Every construction permits `n = 0`. There is then one empty block shape and one
empty root subset, and the sign is `+1`. The theorem retains that term and the
existing rank-zero operator. It introduces no alternative operator or graded
ring; the graded unit and support-adjusted whole-ring comparisons have their
separate existing owners.

## Provenance and remaining boundaries

This is an internal comparison of existing constructions. Its algebraic inputs
are the actual block projection, section, radical and Levi equivalence. Its
functor inputs are the existing general subgroup functors, block functors,
induced-equivalence and coinvariant-equivalence constructions. The exact-K0
identities follow from the existing generic map and transport APIs. No new
literature theorem is asserted by the adapter, and the implemented proofs are
described above.

The existing p-adic preservation proofs retain their actual transitive
classification dependencies. In particular, the length branch uses
`Parabolic.normalizedParabolicFiniteLength` and
`Parabolic.FiniteLengthFunctorAssembly`, with the existing finite-length
admissibility, arbitrary-Levi factorization, normalized product induction and
refined Jacquet length proofs. The generic group-pullback helper in
`Smooth.FiniteLengthGrothendieckTransport` still imports
`Classification.FiniteLengthProof`, where the invoked
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` is proved through
invariant-subspace order equivalence and module length. The new
natural-isomorphism transfer helper itself adds no classification import. The
module also imports the existing general alternating-operator interface, whose
other constructions retain their own import closure. This adapter makes no
classification-independence claim; the host dependency ledger must include the
new general-interface and comparison roots as well as the older GL roots.

The full Haar-to-block modulus identity is still a named structural proof
obligation. The separately published
[`Group.GL.AlgebraicPointTopology`](../../Group/GL/AlgebraicPointTopology.md)
compares the actual algebraic GL rational points, dynamic subgroups, limit,
inclusion, conjugation and quotient with these matrix models, using the named
`rationalPointTopology`. It applies to all commutative topological rings and all
ranks, including zero. Consumers must use that named topology; the present
module does not import the bridge or deduce the Haar identity from it. Its
separate provenance and dependency inventory are in the
[topology supplement](../../../notes/aubert/gl-algebraic-point-specialization.md).
The remaining Chapter V structural comparisons retain their own exact targets.
The p-adic exact-K0 proofs retain the existing characteristic-zero local-field
model and saturated carrier restriction. The arbitrary topological-ring functor
comparisons do not supply preservation theorems over other local fields. The
module does not prove the general Aubert theorem, its support-sign adjustment,
the product-Levi tensor comparison or the full graded Zelevinsky comparison.

## Exact General-source reconciliation and dependency audit

This submission uses the `General.Parabolic` and `General.AlternatingOperator`
source pairs from Worker 23's published contribution
`434a4095-6e40-4821-becc-73e6edef6124`. It has machine validation and Reviewer
9160's independent approval, review `03c6a487-2c16-4853-9dcd-baf9210bb440`,
and was published at Library commit
`7a2e42fd31831029d34cafb155ffad911920df25`, integration
`db08bd0035d74c9ca9ec89bb53e67ece`. Its predecessor
`214d3c61-c6e3-4576-b94e-57c72d2e7e55` was rejected for an unqualified BZ77
induction identification in `Parabolic.md`. Native comparison of all six frozen
files confirms that the three Lean files and `DynamicParabolic.md` are
byte-identical to that predecessor; only `Parabolic.md` and
`AlternatingOperator.md` changed. The corrected documentation restricts the
induction identification to unimodular radicals as described above. The exact
two corrected Markdown files are used unchanged here.

The existing exported interfaces, full-smooth exactness lemmas and compact-open
cofinality proof are retained. This adapter's Lean source is unchanged from its
previous submission. This module imports no `General.DynamicParabolic`
declaration. The General files are borrowed prerequisites, not submitted paths
of this adapter; their actual author, Worker 23, retains coauthor credit for the
reused draft interface. The corrected General prerequisite is now public.
Approval of the previous adapter does not approve these
replacement bytes; this reconciliation requires ordinary independent review.

| Imported pair | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `General.Parabolic` | `de8d3a66aebb7f4e0a705235ac079138231664aca089b67e2ccf82f4cf048d30` | `f7a599323957721ffb29fb5fe79e054fe0d7cef162aa11b80f3ee9b77bbf488f` |
| `General.AlternatingOperator` | `de28a2470cf971ce83fe3e203118bf6154d4f2a96857412c4dbe6dc0cb4a093c` | `eaf84fd0c93b660a0ac2843be520b42667192bb87e280e3938d42f21e039e25f` |

The [specialization addendum](../../../notes/aubert/gl-general-specialization.md)
records a separately pinned earlier draft audit: 17 roots, their 67 distinct
Classification-origin constants and all root memberships, plus paired source
fingerprints and a separate source-import graph. That historical snapshot is
preserved. A fresh checked-type/body traversal, diagnostic
`2364f782-042f-4dda-98ba-8f4d37b089b8`, against the corrected prerequisite and
Library base `df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e` gives exactly the same
17 root records as the preceding reconciliation: declaration counts, defining
module sets and Classification-origin constant lists are all unchanged. Its
union contains 465 defining project modules and the same 67
Classification-origin constants in 10 defining Classification modules; all 67
occur in the earlier 420-constant host inventory. A paired-source inventory at
the published Library commit `7a2e42fd31831029d34cafb155ffad911920df25`
resolves the 465 defining modules to 464 byte-identical Library pairs and one
additional pair, this adapter.

The separate source-import closure is also unchanged from the preceding
reconciliation: 624 project pairs, 159 import-only modules and 14 imported
Classification modules. Of these, 623 are byte-identical Library pairs and
this adapter is the sole additional pair. Relative to the earlier 621-module
addendum, `Jacquet.LocalizationExactnessStatement`,
`Jacquet.LocalizationExactnessProof` and `Group.LeftQuotient` remain the three
additions. Compared with the preceding reconciliation, only the two General
Markdown files and this adapter's Markdown have changed paired fingerprints;
every Lean fingerprint is unchanged. All Classification-module pairs agree
with that reconciliation. Neither inventory is a classification-independence
certificate.

The reproducible native fingerprint script is
`.private/notes/gl_general_434a4095_source_audit.py`; it resolves the current
workspace, then this named Library base, with no private source overlay. Full
paired hashes, source resolutions and import edges are saved in
`.private/notes/gl-general-specialization-434a4095-source-hashes.json`, and the
17 checked root records in
`.private/notes/gl-general-specialization-434a4095-dependencies.json`.
The checked traversal was run at the earlier base named above; the final
fingerprint comparison confirms that every imported Lean file is unchanged,
including the two newly published General pairs. Restoration compilation
`31ee7858-2489-423e-afaf-fcd7ddada99e` also checks this adapter and the
separate topology bridge with no errors or warnings.
The source-pair normalization remains sorted UTF-8 lines
`module<TAB>Lean-SHA256<TAB>Markdown-SHA256<LF>`, including the final newline.

The focused submission exports only this Lean/Markdown pair. The imported
`Parabolic.LeviModelTransport`, `Group.GL.ParabolicQuotientTopology`,
`Parabolic.QuotientJacquetComparison`, `Parabolic.QuotientInductionComparison`
and `Smooth.FiniteLengthGrothendieckIso` pairs match the independently accepted
and published Library sources. Their former pending status is historical.
Neither development compilation nor source reconciliation establishes
publication or mathematical acceptance of this adapter. The full Haar-to-block
modulus comparison remains in-book proof work, separate from the allowed
external Chapter V inputs and from the published algebraic rational-point and
point-topology comparisons.
