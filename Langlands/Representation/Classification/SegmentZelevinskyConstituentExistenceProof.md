# Strong socle and reverse head of an individual segment

Author: Worker 699. Coauthor: Worker 502, who supplied the generic common-image
proof and the quotient-admissibility helper application reused in this assembly.

The theorem `Langlands.Classification.segmentZelevinskyConstituentExistence`
proves exactly the published proposition
`SegmentZelevinskyConstituentExistence.{uF,uV} F T`. For every segment it
constructs an actual smooth irreducible representation that is the strong
socle of the increasing normalized product and the strong head of the
decreasing normalized product for every actual representative of the base.
Strong socle means equality of the images of all irreducible embeddings;
strong head means equality of the kernels of all irreducible quotient maps.
The theorem has no additional theorem-valued premise.

The field universe `uF` and supercuspidal carrier universe `uV` are independent.
The constructed carrier is in `max uF uV`, as required by the statement.
The result covers every prime, supplied p-adic field and compatible topology,
and every positive rank and length. Both products are the actual upper
normalized parabolic inductions with right translation from `Segments`.

## Implemented proof

Fix an actual supercuspidal representation `A` of rank `r > 0` and a length
`m > 0`. Write `σ` for the increasing external tensor, `τ` for the decreasing
external tensor, `Iu` for the increasing induction, and `Id` for the decreasing
induction. Let `J` be the actual upper normalized Jacquet functor for the
uniform block shape with `m` blocks of size `r`.

The published `segmentJacquetMultiplicityReduction`, supplied with the
unconditional theorem `glCuspidalJacquetMultiplicityPrerequisites`, gives
upper `σ`-multiplicity one in `Iu` and opposite `τ`-multiplicity one in `Id`.
The published `segment_upper_opposite_multiplicity_iff` changes the latter
into upper `σ`-multiplicity one in `Id`. These multiplicities are defined
using actual finite composition series.

Every nonzero smooth quotient of `Id` has positive opposite `τ`-multiplicity
by `oppositeJacquetQuotientDetection`; reversal changes this into positive
upper `σ`-multiplicity. Its admissibility hypothesis is proved for the
actual quotient: `segmentInductionAdmissibility` supplies admissibility of
`Id`, and the private helper `segmentQuotient_admissible` applies
`Unramified.SphericalExistence.isAdmissible_of_surjective`.
The helper chooses a compact open subgroup inside each open subgroup using
`T.generalLinearCompactOpen`, then transfers finite generation of fixed
vectors through the actual surjective intertwiner. No finite length of the
induced representations is assumed.

Every nonzero smooth subrepresentation of `Iu` has positive upper
`σ`-multiplicity by `upperJacquetSubrepresentationDetection`. Tensor
irreducibility and Levi cuspidality in both orders are supplied by the
published segment tensor lemmas.

The association between the two tensors is
`segmentFactors_associated_segmentFactorsDown`, used in the reverse direction.
The unconditional `CuspidalSupport.associatedCuspidalInductionHomTheorem`,
specialized at independent universes `{uF,uV,uV}`, therefore supplies an actual
nonzero intertwiner `Id → Iu`.

Apply the published `commonImageMultiplicityOne` to this map and the additive
upper Jacquet functor, which preserves injective and surjective maps. The
count-one and positive-detection hypotheses just established imply that the
actual image is irreducible, is the strong head of `Id`, and is the strong
socle of `Iu`. In particular the conclusion includes equal kernels for all
irreducible quotient maps and equal images for all irreducible embeddings;
it is stronger than uniqueness of an isomorphism class.

The private pointwise-to-segment helper chooses an actual representative of
the segment's base using `Quotient.exists_rep` and applies this construction
at its positive rank and length. The increasing socle supplies
`IsSegmentSocle`. For every other actual representative of the same base,
`segmentInducedDownIsoOfRepresented` gives an actual equivalence of decreasing
inductions. `IsIrreducibleHead.of_equiv` transports the strong head relation
along this equivalence, proving the universal reverse-head clause.

## Source and provenance

The target is Zelevinsky, *Induced representations of reductive p-adic
groups II. Irreducible representations of GL(n)* (1980), Proposition 2.10,
printed p.180, and §3.1, printed pp.180–181 (PDF pp.17–18).
The registered original is `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
These passages, and the preceding lower arguments on printed pp.174–180,
were read from the original.

The implemented proof is an internal derivation using Jacquet multiplicity
and an actual common image. It does not formalize the graph classification
proof of Proposition 2.10. In particular it needs neither the graph theorem
nor the two-element reducibility argument whose source gap is recorded in
the published statement explanation. The generic common-image theorem,
the two detectors, reversal, the full cuspidal counts and the associated
induction Hom theorem are proved Library results rather than assumed
proposition definitions. Their use here is explained above.

## Dependency audit

The recursive project import closure has 649 modules including this proof,
checked against Library commit
`a9fae2951e0ea3e71a3319caba67d2b93350b350`. All 648 imported Lean/Markdown pairs
match that Library byte for byte; the only new pair is this proof.
The proof and its recursive imports contain no use of socle exhaustion,
segment analytic classification, special-head multisegment exhaustion,
ordered special-head existence, quotient coverage, tempered block uniqueness,
square-integrable classification or exhaustion, or regular exhaustion.
The audit includes their mathematical conclusions and transitive proof
dependencies, rather than only searches for task identifiers.

The generic common-image theorem uses actual smooth images, finite-series
multiplicity and algebraic strong constituent criteria. The upper detector
uses evaluation and first adjointness. The opposite quotient detector uses
the unconditional `Parabolic.normalizedSecondAdjointness`, coinvariant-map
surjectivity and an actual-series quotient detector. Second adjointness is
assembled from induction duality, first adjointness, natural upper/opposite
Jacquet duality and admissible Hom duality. Its lower constructions use the
compact-picture scalar integral, stable pairings and canonical lifts.
No duality or adjointness premise remains.

That adjointness closure imports
`Exponents.UnitaryDualJacquetSupportAdapters` for compact-open cofinality on
the full Levi, derived from `T.leviCompactOpen`. It also contains the
proposition definitions `TemperedSupportStatement` and
`TemperedInductionStatement`, the predicates `Tempered` and `Essential`,
and general support and exponent transport adapters. These do not prove an
excluded tempered classification conclusion.

The spherical module is used for its generic quotient-admissibility lemma.
Its other construction obtains a spherical irreducible quotient of a cyclic
subrepresentation of an unramified principal series. Its lower inputs are
induction admissibility, compact-open and Iwasawa constructions, and the
elementary quasicuspidal-embedding result. None is an excluded classification
conclusion.

The full cuspidal count theorem derives both actual normalized Jacquet
lengths and every multiplicity, with three independent universes and no
premises. Its upper branch uses the actual associated filtration; its
opposite branch constructs the reversed filtration. Finite-family counting
turns these filtrations into composition series, counts matching indices
including repetitions, and applies Jordan–Hölder independence. The
associated-filtration proof discharges its geometric and deletion premises
using published lower proofs, with a direct rank-zero construction.

The associated-induction Hom theorem uses a minimal associating permutation,
that same associated filtration, admissibility of the filtration by extension,
an actual cuspidal quotient, and backward normalized Frobenius reciprocity.
Its extension helper requires only inclusion of the kernel in the first
map's range; its use on filtration steps supplies actual short exact
sequences. The lower cuspidal constituent theorem uses compact coefficient
projectors, determinant-unit restriction, fixed-vector dimension induction,
Cartan decomposition and Schur arguments. The closure's
`SupercuspidalSupport` module contains definitions, conditional support choice
and transport, with no classification existence or uniqueness proof.

The remaining classification imports are constituent relations, segment and
supercuspidal definitions and representative transport, tensor irreducibility
and association, integral twist freeness, segment admissibility, upper
Jacquet exactness and detection, reversal, and count reduction. Elementary
orbit-span, orbit-mean translation, character-twist coinvariant equivalences,
subquotient transport and finite block-shape lemmas introduce no
classification conclusion. Thus the proof uses only independent lower
results and leaves the target statement pair and its imports unchanged.
