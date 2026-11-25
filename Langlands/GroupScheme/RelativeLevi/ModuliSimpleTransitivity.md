# Simple transitivity on actual relative Levi images

This internal helper applies the published theorem
`Langlands.GroupScheme.relativeLeviConjugacy` to the actual image-valued
moduli defined in `RelativeLevi.ModuliValue`. It introduces no independent
mathematical assumption and changes no existing predicate.

Over an arbitrary scheme in universe `u`, fix a relative parabolic in a
reductive group and a supplied relative unipotent radical. For any two
`LeviImage` values, `LeviImage.existsUnique_conjugate` produces the unique
point of the radical over the base that carries the first image to the second
by conjugation. The proof chooses actual Levi presentations from the two
values, applies the published conjugacy theorem, and rewrites its all-test
range equality using `conjugateImage_range`. Equality of moduli points
remains equality of their subgroup functors, independent of their sources.

Given a Levi image, `LeviImage.conjugationEquiv` identifies the radical's
base-valued points with all Levi images. Existence gives surjectivity and
uniqueness gives injectivity. Its multiplication formula follows from the
actual subgroup conjugation composition law. Its orientation is
`(g * h) L (g * h)⁻¹ = g (h L h⁻¹) g⁻¹`, as required by the torsor target.

These constructions concern points over a fixed base and require a supplied
image for the orbit equivalence. They do not assert a global Levi exists,
construct a representing scheme, or establish arbitrary-base restriction
stability. Their provenance is a direct composition of the published
image and conjugacy APIs; the geometric source underlying that conjugacy
theorem is documented in `RelativeLevi.ConjugacyProof`.
