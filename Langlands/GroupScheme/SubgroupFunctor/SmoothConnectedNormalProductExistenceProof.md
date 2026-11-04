# Existence of smooth connected represented normal products

`Langlands.GroupScheme.smoothConnectedNormalFppfProductExistence.{u}` proves
the published `SmoothConnectedNormalFppfProductExistenceStatement.{u}` over
every field in the arbitrary universe `u`. It constructs an actual closed
subgroup representative and proves the existing fppf product membership
equivalence on every relative scheme test.

The supporting theorem `SubgroupFunctor.exists_smoothConnected_fppfProduct`
requires two smooth connected closed subgroups `i : H ⟶ G` and `j : N ⟶ G`
of an affine group locally of finite type over the field. It assumes that
the range of `j` normalizes the range of `i`. Closedness makes both factors
affine. The published normalized-conjugation action gives a semidirect
group whose underlying relative scheme is `H.X × N.X`; the published
`normalizedProductHom` is ordered multiplication into `G`.

The product scheme is smooth. The published
`smoothConnectedAffineGeometry.2` makes it affine and geometrically
integral; geometric irreducibility makes its underlying space irreducible,
hence connected. The image theorem `HomImage.exists_image` therefore
constructs an actual closed image inclusion `p : P ⟶ G` and a
homomorphism `q` from this semidirect group onto `P`. Its underlying map is
flat, surjective and locally of finite presentation, and `q ≫ p` is
the original ordered multiplication homomorphism.

The published `isFppfProduct_of_fppf_factorization` converts this
factorization into the full `IsFppfProduct` predicate, using pullback
covers and descent through the closed inclusion. The proof does not
replace fppf-local membership by pointwise surjectivity. Closedness makes
`P` affine and locally of finite type. The supporting
`IsFppfProduct.smooth` proves smoothness from the smooth affine factors
by descending geometric reducedness along the multiplication
epimorphism and applying Mathlib's group-scheme smoothness theorem.
The published `IsFppfProduct.connectedSpace` gives connectedness.

The final theorem obtains the required normalization from normality of
the first factor and applies this supporting result to every binder of
the exact published statement. The second factor's normality is a
stronger hypothesis of the target than this construction needs. There
is no additional theorem-valued premise.

The construction follows the semidirect-image proof of Milne,
*Algebraic Groups* (2017), Theorem 5.82, printed pp. 120–121, registered
source `milne-2017-algebraic-groups`. The all-test criterion and the
geometric conclusions are derived from the named Library interfaces.
Worker 133 authored the assembly; Worker 1484 authored the supporting
`FppfProductSmooth` pair.
