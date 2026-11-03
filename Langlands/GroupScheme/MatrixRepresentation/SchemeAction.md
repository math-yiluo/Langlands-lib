# The actual affine-space action of a matrix representation

For an arbitrary commutative ring `R` in universe `u`, `coefficientSpace n R`
is actual affine space over `Spec R`, with index `ULift n` in the scheme universe.
Its points on any scheme `T` over the base are equivalent to vectors
`n → Γ(T, ⊤)`. The equivalence records the pullbacks of the coordinate functions;
its inverse is Mathlib's affine-space morphism associated to a vector. This
coordinate construction does not require finiteness of `n`.

For a finite index with decidable equality and an actual matrix representation
`ρ : G ⟶ GL_n`, `ρ.schemeAction` is a categorical scheme action of `G` on this
affine space. Its actual morphism on `G × coefficientSpace` is the affine-space
point whose coordinates are the product of the universal representation matrix
and the universal vector. Pullback naturality of `ρ.pointMatrix`, together with
preservation of matrix-vector products by ring homomorphisms, proves that its
action on every scheme test has precisely the original matrix-vector formula.
Coordinate injectivity then proves the identity and multiplication laws from
the representation's homomorphism laws. `schemeActionOfPointLaws` packages
these into the existing categorical module-object structure.

The point `constantCoefficientPoint v` associated to a base vector `v : n → R`
has coordinates given by the structure ring map `scalarMap`. Those coordinates
remain the scalar images of `v` after every test morphism to the base.
Consequently `isFixedVector_iff_isFixed` identifies the existing
`ρ.IsFixedVector v` condition with all-test fixedness of this actual point
under `ρ.schemeAction`, including the refinements in `SchemeAction.IsFixed`.

This is an internal construction derived from the published matrix
representation, fixed-vector and scheme-action interfaces and Mathlib's
affine-space point equivalence. It supplies a bridge for applying geometric
orbit arguments to coefficient vectors. It does not construct a Borel quotient,
establish its properness, or prove `BorelNormalizerStatement`.
