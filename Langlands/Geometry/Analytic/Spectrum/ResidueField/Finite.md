# Finite completed residue-field extensions

`BanachSpectrum.IsFiniteCompletedResidueComap K f y` means that the actual
completed residue field at `y` is finite as a module over that at
`comap f.toBoundedRingHom y`. The scalar action is induced by the published
canonical map `completedResidueComap K f y`; the predicate does not quantify
over a choice of field embedding.

The ground field `K : Type u` is normed and ultrametric. The algebras `A : Type v`
and `B : Type w` are commutative normed rings with normed `K`-algebra structures.
The three universes are independent. No affinoid presentation, completeness of
`K`, or nontrivial valuation is required.

`finite_completedResidueComap K f hf y` establishes this predicate when the
underlying ring homomorphism of the bounded algebra map `f` is finite.
`algebraic_completedResidueComap` gives the resulting algebraicity with the
same canonical scalar action.

## Implemented proof

Write `E = H(comap f y)` and `F = H(y)` for the published completed residue
fields. Their canonical connecting map is isometric. It gives `F` a normed
`E`-algebra structure. The canonical residue maps give compatible `A`-algebra
structures, so the residue map `B → F` extends to an `E`-algebra map
`E ⊗[A] B → F`. Its image `S` is a finite-dimensional `E`-subalgebra, since
`B` is finite over `A`. It contains the residue image of every element of `B`.

The helper `isClosed_finite_subalgebra` proves that a finite-dimensional
subalgebra of an ultrametric normed field is closed over a complete normed
scalar field. If that scalar field is nontrivially normed, this is the standard
finite-dimensional closed-subspace theorem. Otherwise every nonzero scalar
has norm one. The existing `absoluteValue_eq_one_of_trivial`, applied to the
norm absolute value and an algebraic element of the subalgebra, shows that
every nonzero element of the subalgebra also has norm one. Distinct elements
therefore have distance one, and the metric spaced-out closed-set theorem
applies. This second case retains trivially valued fields.

The helper `finite_subalgebra_eq_top_of_residueMap` proves that a closed finite
subalgebra containing the residue image contains the whole completion.
Elements of its subalgebra are algebraic, so inverses remain in it by
`Subalgebra.inv_mem_of_algebraic`. Every element of the normed residue field
is a quotient of two residue images: this follows from the fraction-field
construction of the quotient by the point kernel. These quotients lie in `S`.
The completion induction principle, using closedness of `S`, then gives
`S = ⊤`.

Applying these helpers to the tensor image shows that it is all of `F`.
The inclusion of `S` into `F` is therefore surjective and transfers module
finiteness. The final corollary uses the standard fact that a finite algebra
over a field is algebraic.

## Provenance and scope

This is an internal algebraic and topological construction from the Library's
actual residue quotient, fraction field, completion, canonical residue maps
and their isometric functoriality. It uses the existing finite-module, tensor
product, algebraicity and metric completion APIs. It is not presented as a
transcription of a numbered result in the literature.

The unit supplies the affine finiteness input for extending a prescribed
embedding into an algebraically closed field. It does not assert the
geometric-point axioms of the analytic étale site or construct an all-chart
field-valued lift on its own.
