# Monomorphism detection by analytification

For compatible supplied analytifications of separated algebraic spaces,
the comparison of the overlaps of two presented affine source tests is
an analytic isomorphism when the given analytic map is monic. The
comparison map of algebras is surjective because the source overlap is
closed in the affine product. Faithfulness of localized affine
analytification detects injectivity of this algebra map from the
analytic isomorphism. The resulting algebra equivalence preserves the
two projections. Transporting the target pullback along this
equivalence gives cancellation over the source for any scheme test
whose two maps factor through the presented affine source tests.

For a locally finite type source, take an étale scheme atlas and cover
its representing scheme by affine opens. These opens have finite type
coordinate algebras over `K`. The coproduct of the presheaves represented
by the affine opens maps locally surjectively to the source sheaf in
the fppf topology. Transport this coverage to their relative spectra.
Two sections with equal images in the target lift on the intersection
of their covering sieves. The affine cancellation result shows that
the sections agree on the sieve. The sheaf criterion for local
injectivity then gives monicity of the algebraic map on presheaves.

The field is complete, nontrivially normed and ultrametric. The field
and the algebraic test rings have the same arbitrary universe `u`,
with analytic objects in `LocalizedCategory.{u,u,u}`. Compatibility
means the equality `p' A P x ≫ F = p A P (RingPoints.map f x)` for every
presented affine test of the source.

The argument is derived from the Library's affine overlap comparison,
faithfulness, and fppf sheaf criteria. It applies to analytic
monomorphisms and is used in reflecting open and closed immersions.
