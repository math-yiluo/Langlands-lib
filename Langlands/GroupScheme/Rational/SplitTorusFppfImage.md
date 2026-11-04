# Actual fppf images of split tori

Author: Worker 1375.

This internal construction strengthens the published split-image
factorization in `Rational.SplitTorusImage` by including flatness,
surjectivity and local finite presentation of the projection onto the
image. It works over every field `k : Type u`. The affine target group
scheme need not be smooth, connected, reductive or commutative.

`SplitTorusFppfImage φ` contains an actual commutative group scheme `E`,
an actual projection `π : D → E`, and an actual inclusion `j : E → H`.
It asserts that `j` is a closed split subtorus, that the underlying scheme
map of `π` is flat, surjective and locally of finite presentation, and that
`groupHom π ≫ j = φ`. All maps are actual scheme morphisms; surjectivity is
on underlying schemes, with no claim of surjectivity on field-valued
points.

`locallyOfFinitePresentation_of_splitTori` first proves that every actual
homomorphism between split tori over a field is locally of finite
presentation. Split tori are smooth over the field, hence locally of
finite type. The target is locally Noetherian. The source structure
morphism being locally of finite type implies the same property for the
given homomorphism, and over a locally Noetherian target this implies
local finite presentation.

`IsSplitTorus.nonempty_fppfImage` follows the existing image-lattice
construction of `IsSplitTorus.exists_factor_isSplitSubtorus` in
`Rational.SplitTorusImage` (Author: Worker 228). Present the source by
`D(ℤ^I)` and the affine target by its actual coordinate algebra. The
published `SplitTorusImage.lattice` is the subgroup of exponents whose
monomials lie in the image of the classifying coordinate map. Its group
algebra is precisely that coordinate-map image. The published
`imageTrans`, `isClosedImmersion_imageTrans` and `restrict_imageTrans`
therefore supply the closed inclusion and factorization.

The projection in these coordinates is
`D(ℤ^I) → D(L)` for the actual inclusion `L ↪ ℤ^I`. The published
`Diagonalizable.flat_and_surjective_restrictMap` proves flatness and
surjectivity, because the subgroup inclusion is injective. Its proof
makes the group algebra free over the subgroup algebra using cosets.
Transport through the source splitting isomorphisms preserves these
properties. The sublattice `L` is finite free by the published PID-basis
argument, so `E = D(L)` is split. The preceding local finite-presentation
lemma applies to the resulting actual projection.

`IsSplitTorus.fppfImage` chooses the constructed factorization together
with all these properties. The proof reuses the public coordinate-image
helpers rather than asserting image representability or faithful
flatness as a new hypothesis.

This module proves no maximality statement for the image. Applying it to
a central isogeny and a maximal split source torus still requires the
separate `CentralSurjectionMaximalSplitTorusImageStatement` proof to
conclude that the supplied image is maximal split.
