# The special strong head and reverse socle of a segment

Worker 502, with Worker 699 as coauthor for the adapted pointwise assembly,
proves the published proposition
`Langlands.Classification.SegmentSpecialConstituentExistence.{uF,uV} F T`.
The closing theorem is
`Langlands.Classification.segmentSpecialConstituentExistence`.
Its only outer parameters are an arbitrary prime, its primality instance,
an actual `PadicField.{uF}` and the supplied compatible topological data `T`.
There are no additional theorem assumptions. The independent universes `uF`
and `uV` are retained, and the constructed smooth complex representation has
carrier in `Type (max uF uV)`.

For every segment, the theorem constructs one actual irreducible representation
which is the strong head of the increasing product and the strong socle of the
decreasing product for every actual representative of the base class.
The head includes equality of kernels of all irreducible quotient maps;
the socle includes equality of images of all irreducible embeddings, in the
carrier universe prescribed by the statement.

## Implemented proof

Fix an actual irreducible supercuspidal representation `A` of positive rank
`r` and a positive length `m`. Write `B` for the uniform block shape, `sigma`
for the increasing tensor, `tau` for the decreasing tensor, and `Iu`, `Id`
for their upper normalized inductions. All constructions use `T`. The
published segment tensor results give irreducibility and Levi cuspidality of
both tensors. The functor `J` is the actual opposite normalized Jacquet
functor for `B`; its additive and mono/epi preservation instances come from
`CuspidalJacquetFunctorExactnessProof`.

The published unconditional theorem
`glCuspidalJacquetMultiplicityPrerequisites.{uF,uV,uV}`, specialized through
`segmentJacquetMultiplicityReduction`, supplies actual finite composition
series and multiplicity one for `sigma` in `J(Iu)`. It also supplies
multiplicity one for `tau` in the upper Jacquet module of `Id`.
`segment_opposite_upper_multiplicity_iff` transports this latter statement to
multiplicity one for `sigma` in `J(Id)`. This is actual block reversal,
including the tensor tests and normalization.

Every nonzero smooth quotient of `Iu` has a positive `sigma` multiplicity
under `J`, by `oppositeJacquetQuotientDetection`. To apply that theorem, the
private helper `specialSegmentQuotient_admissible` proves admissibility of
the arbitrary quotient: compact open subgroups of the actual general linear
group are cofinal, so the published
`Unramified.SphericalExistence.isAdmissible_of_surjective` applies to its
surjective intertwiner and to published segment induction admissibility.
No irreducibility is required of this quotient. Every nonzero smooth
subobject of `Id` has a positive upper `tau` multiplicity by
`upperJacquetSubrepresentationDetection`; block reversal changes this to a
positive opposite `sigma` multiplicity. No irreducibility is required of
this subobject either.

`segmentFactors_associated_segmentFactorsDown` proves association of the two
actual inducing tensors. The published unconditional theorem
`associatedCuspidalInductionHomTheorem.{uF,uV,uV}` therefore gives an actual
nonzero intertwiner `Iu -> Id`. Applying the published
`commonImageMultiplicityOne` to this map, the two multiplicity-one series,
and the quotient/subobject detectors constructs its actual smooth image
object. That criterion proves irreducibility of the image and both strong
endpoint properties. In particular, its conclusions retain equality of all
competing quotient kernels and embedding images; the argument does not stop
at uniqueness up to isomorphism.

The private pointwise helper chooses an actual representative of a segment's
base using `Quotient.exists_rep`. The strong head for that representative
supplies `IsSegmentHead`. For each other actual representative of the same
base, `segmentInducedDownIsoOfRepresented` gives an actual equivalence of the
decreasing products. `IsIrreducibleSocle.of_equiv` transports the strong
socle along it. Thus the same constructed representation satisfies the
universal representative clause of the exact target.

The induction is the existing upper normalized induction with positive
half-modulus covariance and right translation. The special head uses the
increasing product; the reverse socle uses the decreasing product. Endpoint
direction is obtained by the actual map, detectors and block reversal.

## Provenance and dependency audit

The statement's original source is Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), section 9.1, printed page 197 / PDF page
34, referring to Proposition 2.10, printed page 180 / PDF page 17. The
registered literature ID is `zelevinsky-1980-induced-ii`, with PDF SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original support and orientation argument in sections 2.1-2.10 motivates
the statement. The implemented proof instead assembles the independently
proved common-image criterion, actual Jacquet counts, detectors, and
associated-induction map described above. It does not claim to formalize
the printed graph-orientation proof.

The recursive project import audit against Library base
`a9fae2951e0ea3e71a3319caba67d2b93350b350` contains 649 project modules,
including this proof. All 648 imported project Lean/Markdown pairs match
that base, including the unchanged target statement and every pair it
imports. The audit traverses imports and checks module names and declaration
text for the excluded conclusions. The imported proof routes are lower-level
smooth category, finite filtration, tensor, twist, actual induction, Jacquet,
second adjointness, cuspidal support and compact-coefficient constructions.
The Hom proof adds associated Jacquet filtration, block Weyl transport and
cuspidal constituent results; its import closure is independent of segment
constituent existence. The full count proof uses the geometric lemma and
finite-family counting to supply actual series, rather than assuming them.

The second-adjointness closure also imports the general analytic predicates
and transport adapters in `Essential`, `Tempered`,
`OppositeSupportJacquetAdapter` and
`Exponents.UnitaryDualJacquetSupportAdapters`, and the proposition definitions
`TemperedSupportStatement` and `TemperedInductionStatement`. No conclusion of
those statement definitions is used as an assumption or proved input here.
There is no use of segment analytic classification, multisegment special-head
exhaustion, ordered special-head existence, quotient coverage, tempered block
uniqueness, square-integrable classification or exhaustion, regular exhaustion,
or a proof successor or transitive proof dependency of those conclusions.
The downstream full segment Jacquet equivalence is also excluded. Ordinary
contragredient compatibility is not used to identify the endpoints.
