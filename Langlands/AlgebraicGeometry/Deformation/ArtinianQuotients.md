# Quotient Artinian tests and elementary kernel filtrations

This is an internal construction and a collection of derived consequences of
`Deformation.ArtinianTests` and Mathlib's ideal quotient operations. It uses
actual augmented algebras and actual compatible algebra homomorphisms throughout.
The main construction is `ArtinianTest.filtrationStep`; the resulting elimination
principle is `ArtinianTest.surjective_induction`. No external deformation or
algebraization theorem is invoked.

Fix an arbitrary universe `u`, a commutative ring `k`, and a field `K` with a
specified `k`-algebra structure. A test `A` is a local Artinian `k`-algebra with
a specified surjective augmentation `epsilon_A : A → K`, as in the imported
module. There is no specified section of this augmentation and no required
`K`-algebra structure on `A`. Write `m_A` for its maximal ideal.

## Actual quotient tests

For an ideal `I` contained in `ker epsilon_A`, `quotientAugmentation` is the
induced algebra homomorphism `A/I → K`. It is surjective because `epsilon_A`
is surjective. Its nontrivial codomain makes `A/I` nontrivial, and locality
and Artinianity pass to the quotient. Thus `quotient A I hI` is again a test.
`quotientMap` is the actual algebra quotient map with its augmentation
compatibility equation. Its underlying map is surjective and its kernel is
exactly `I`.

If a test arrow `q : A → B` kills `I`, `quotientLift` is its induced compatible
map `A/I → B`. Composing with `quotientMap` recovers the original test arrow,
not just an isomorphic algebra map. The lift is surjective when `q` is
surjective, and is injective when `ker q = I`. The latter claim uses Mathlib's
injectivity criterion for a homomorphism induced from a quotient.
`hom_ext` identifies equality of test arrows with equality of their underlying
algebra homomorphisms.

For ideals `I ≤ J ≤ ker epsilon_A`, `quotientFactor` is the induced test arrow
`A/I → A/J`. It is surjective, its composite with the first quotient map is
the second quotient map, and its kernel is the image of `J` in `A/I`.
If `m_A * J ≤ I`, `quotientFactor_isElementary` proves that this arrow is an
elementary surjection. Here the imported convention is surjectivity together
with annihilation of the kernel by the source maximal ideal. It includes
zero kernels and does not impose a one-dimensional condition.

For this last proof, the maximal ideal of `A/I` is the image of `m_A` under
the surjective quotient map. Mapping the ideal product identifies its product
with the induced kernel as the image of `m_A * J`. The containment in `I`
makes that image zero. `isElementary_of_bijective` also records that any
bijective test arrow is elementary, since its kernel is zero.

## The finite kernel filtration

For any test arrow `q : A → B`, not necessarily surjective, define

`kernelFiltration q n = m_A^n * ker q`.

The zeroth ideal is `ker q`. Multiplication by `m_A` gives the next ideal,
so the sequence decreases. Every ideal lies in `ker q`, hence in
`ker epsilon_A`. The source maximal ideal is nilpotent by the imported
local Artinian result; therefore some filtration ideal is zero.

`filtrationTest q n` is the actual quotient test by the nth ideal, and
`filtrationMap q n` is the quotient arrow from `A`.
`filtrationStep q n` is the arrow from stage `n+1` to stage `n`.
It is elementary because

`m_A * kernelFiltration q n = kernelFiltration q (n+1)`.

The equation `filtrationMap_step` states that the quotient arrow to stage
`n+1` followed by this step is exactly the quotient arrow to stage `n`.
`filtrationLift q n` maps each stage to `B`; its composite with the quotient
arrow is exactly `q`.

When `q` is surjective, its stage-zero lift `A/ker q → B` is bijective,
and hence elementary. When a filtration ideal is zero, the corresponding
quotient arrow `A → A/0` has zero kernel, is surjective, and is elementary.
These endpoint arrows are retained as actual arrows, so the construction
does not require replacing either endpoint by an identified isomorphic test.

## Elimination of general surjections

`surjective_induction` accepts an arbitrary proposition `P q` about an actual
test arrow, a proof of `P` for every elementary surjection, and a proof that
`P` is closed under composition. It concludes `P q` for every surjective
test arrow `q`.

The implemented proof chooses a stage with zero filtration ideal and obtains
`P` for its quotient arrow. Induction on the stage index composes with the
elementary consecutive steps to obtain `P` for the stage-zero quotient arrow.
Composing with the elementary stage-zero lift proves `P q`, using the exact
factorization equation. This gives a finite elementary reduction without
choosing bases for the kernels or a coefficient field.

The module supplies algebraic tests and an elimination principle. It does not
prove existence of Picard deformations, lifting for elementary surjections,
formal versality, effectivity, algebraization, or a smooth scheme atlas.
