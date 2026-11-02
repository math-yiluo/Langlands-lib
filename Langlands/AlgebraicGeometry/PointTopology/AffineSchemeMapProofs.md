# Mapping proofs for actual affine scheme points

Author: Worker 105.

This file proves `AffineSchemeMapProperties`, the derived actual-scheme
formulation of the affine mapping assertions in Brian Conrad, *Weil
and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The source states these mapping properties for affine finite-type
schemes over a topological ring. This target is a derived extension:
`R` and the value `R`-algebra `S` are arbitrary commutative rings in
an arbitrary common universe, `S` has any topology, and `X` and `Y`
are arbitrary actual affine schemes over `Spec R`. Their points are
the existing relative scheme morphisms `RingPoint R X S`, with the
published global-section evaluation topologies. The proof uses
no finite generating family or continuous ring operations.

The implemented proof first uses `affineSchemePointEquiv_natural` to
identify actual scheme-point postcomposition with precomposition by
the actual pullback on global sections, conjugated by the two
coordinate-point homeomorphisms. Continuous precomposition in the
evaluation topology then proves continuity of the original scheme
point map.

For a closed immersion, Mathlib's
`IsClosedImmersion.isAffine_surjective_of_isAffine` gives surjectivity
of the actual map on global sections. The proof applies
`AlgPoint.isEmbedding_precomp_of_surjective` and, with Hausdorff `S`,
`AlgPoint.isClosedEmbedding_precomp_of_surjective`, and transports
these properties through the same actual point homeomorphisms.
The latter helper describes the image by all kernel equations; it
does not assume that the kernel is finitely generated.

The final theorem assembles exactly the two clauses of the named
target. No topology on the coordinate rings or base ring, continuity
of ring operations, finite type or finite presentation is required.
Hausdorffness is used only in the closed-embedding clause.
The remaining source assertions are outside this target.
