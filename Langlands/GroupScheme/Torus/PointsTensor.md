# Cocharacter evaluation and points of a split torus

This module is an internal construction derived from the actual commutative
group schemes, cocharacter lattices, and split-torus coordinates in
`Torus.Lattice`, `Torus.LatticeGalois`, and `Torus.SplitLatticeBaseChange`.
Its linear-algebra input is Mathlib's finite-product tensor equivalence.
It does not rely on an additional structural assertion about algebraic groups.
All fields, schemes, point carriers, and index types have arbitrary universe
`u`; the scalar ring is `ULift.{u} ℤ`, acting through the usual integral action.

For a commutative group scheme `T` over a scheme `S` and any relative test
scheme `U`, `evaluation T U` is the bilinear map

`(x, ν) ↦ Additive.ofMul (x ≫ ν)`

from additive multiplicative-group points and the actual cocharacter lattice
`Hom(𝔾_m, T)` to additive `T`-points. Linearity in the cocharacter is the
published `evalPoint` map. Additivity in the point is the group-homomorphism
law of a cocharacter. Integral linearity in the point follows by bundling
postcomposition with the cocharacter as a homomorphism of the direct point
groups. `tensorEvaluation` is the induced linear map on their tensor product;
`tensorEvaluation_tmul` states its actual evaluation formula.

`pointsCongr` identifies additive point modules along an actual isomorphism
of the underlying group schemes. `latticeCongr` identifies cocharacters by
postcomposition with the same isomorphism. `tensorEvaluation_congr` proves
that evaluation commutes with these identifications: on pure tensors this
is associativity of composition.

Over a field `L`, `latticeCoordinates L I` identifies the cocharacters of
the coordinate split torus with `I → ULift ℤ`. The equivalence
`splitPointCoordinates L I U` identifies additive points of that torus
with `I`-tuples of additive multiplicative-group points, using the published
units models for both groups. No affineness assumption on the test scheme
is required.

`splitPointCoordinates_evaluation` proves that the `i`th coordinate of
evaluation at `(x, ν)` is `latticeCoordinates ν i • x`. The proof uses the
published formula saying that an integral coordinate cocharacter sends a
unit to its corresponding powers, then transports back through the
multiplicative-group points equivalence.

`coordinateTensorEquiv` first applies the lattice-coordinate equivalence
inside the tensor product, then Mathlib's `TensorProduct.piScalarRight`.
Finiteness of `I` makes this a linear equivalence. The theorem
`split_tensorEvaluation_eq` proves equality of this coordinate equivalence
with actual evaluation followed by point coordinates, by checking pure
tensors. Therefore `split_tensorEvaluation_bijective` proves bijectivity
of actual evaluation for a coordinate split torus.

For an arbitrary commutative group scheme `T` over `L`,
`tensorEvaluation_bijective` assumes `IsSplitTorus T.toGrp`. It chooses the
actual finite-coordinate splitting supplied by that proposition, applies
the coordinate result, and transports injectivity and surjectivity through
`tensorEvaluation_congr`. The resulting `tensorPointEquiv L T hT U` is the
linear equivalence

`Additive (U → 𝔾_m) ⊗[ULift ℤ] X_*(T) ≃ Additive (U → T)`.

Its forward map is the canonical evaluation map, independent of the
splitting chosen in the bijectivity proof. `tensorPointEquiv_tmul` gives its
pure-tensor formula. The current module establishes the point and tensor
comparison under an actual split-torus hypothesis. It does not assert a
Galois-equivariant comparison, cocycle vanishing, or Steinberg quasi-splitness.
