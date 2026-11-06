# Full local-domain intersections inside a special subset

`Langlands.Analytic.IndexedAffinoidAtlas.specialSetIntersection` proves the exact
published `SpecialSetIntersectionStatement`, with independent coefficient,
ambient-point and original-index universes `u`, `v` and `w`. Its type has no
additional ideal-effectiveness or intersection-existence premise.

The Lean proof applies the published
`specialSetIntersection_of_idealEffectiveness` to the proved general theorem
`PresentedAffinoidAlgebra.Domain.FiniteCover.idealEffectiveness`. The latter
establishes closed-ideal effectiveness on arbitrary finite full-domain covers
by rational refinement and scalar descent from strict rational ideal
effectiveness. Thus the only extra premise of the intersection construction
is discharged.

The imported intersection construction extracts a finite special chart cover
of the given literal special subset and constructs subordinate finite covers
of the two given full local domains. It forms the actual closed quotient of
their affinoid coproduct by the explicit contracted ideal of local kernels.
Ideal effectiveness gives bounded local quotient equivalences with the
local intersections and exact equalities of both original algebra maps.
The finite recognition construction derives the union and saturation
properties, proves the full domain property, and produces a full local-domain
presentation whose ambient locus is the literal intersection.

Recognition identifies the two canonical bounded inclusion restrictions with
the retained coproduct legs. The bounded comparison from the genuine completed
tensor to the affinoid coproduct has a bounded right inverse. Its composition
with the admissible closed quotient proves admissibility of exactly the
completed-tensor lift in the target. This includes surjectivity and positive
two-sided comparison of the actual quotient seminorm with the target norm.

The proof retains trivial coefficient valuations, arbitrary positive radii,
nonreduced and zero algebras, and permitted empty domains and finite covers.
Only the special subset's subspace is required to be Hausdorff, as supplied
by specialness; no global ambient Hausdorffness is imposed. The output belongs
to the full local-domain enlargement; no original atlas index for the
intersection is required.

The source target is Berkovich, *Etale cohomology for non-Archimedean analytic
spaces* (1993), Lemma 1.2.12, printed page 20 / PDF page 17, registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The implemented proof uses the Library's explicit closed-ideal descent and
finite recognition constructions described above.
