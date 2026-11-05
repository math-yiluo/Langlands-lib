# Affine-line lifts through proper morphisms

This is an internal consequence of the Library's absolute proper affine-line
extension argument and its valuative criterion for rational maps. It supplies
an extension through a given proper morphism, retaining the prescribed target
curve. All fields and schemes have arbitrary universe `u`.

`AffineLine.exists_polynomial_lift_of_isProper` takes separated schemes `Y`,
`Z`, a proper morphism `q : Y → Z`, a curve `r : Spec k[X] → Z`, and a lift of
its restriction to `Spec k[X, X⁻¹]`. It constructs a curve in `Y` restricting
to that lift and composing with `q` to `r`. The punctured lift defines a
partial map on the dense open set where `X` is invertible. At each remaining
point the stalk of `Spec k[X]` is a valuation ring. The valuative criterion
for `q`, with the prescribed map `r` to the target, makes the rational-map
domain the entire affine line. The resulting morphism has the given
restriction. Scheme-theoretic density of the punctured line and separatedness
of `Z` identify its composite with `r`.

`AffineLine.exists_base_lift_of_isProper` transports this construction to
actual relative products `Spec k ×_k A¹_k` and `Spec k ×_k Gm_k` in the category
of schemes over `Spec k`, using the Library polynomial and Laurent point
isomorphisms. Compatibility with the structure map follows from the
prescribed composite with `q`. Both the punctured restriction and the composite
with `q` are retained as literal equalities of morphisms over `Spec k`.

`AffineLine.baseLiftOfIsProper` chooses one of these actual relative lifts.
Its restriction and composite lemmas retain the two equalities from the
existence theorem. No canonical choice or uniqueness of the chosen lift is
claimed.

These are lifting lemmas for field-valued test schemes. They assert no lifting
for arbitrary test schemes and no rational-point surjectivity of a proper map.
