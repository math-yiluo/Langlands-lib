# Integral Deligne stalks in the actual rational sheaf

This derived module proves injectivity of the existing integral-to-rational
maps for the actual flat lattice sheaf and its homogeneous components.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), item 1 for the
flat coefficient sheaf, item 4 for the rational frame, and condition (c)
for the determinant lattices. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The injectivity arguments here are derived infrastructure rather than
separately quoted theorems.

## General injectivity

Let `O` be a commutative ring, `F` an `O`-algebra field, and suppose
the actual coefficient map `O → F` is injective. Carriers, spaces and
module carriers have the common universe `u`.

`tensorUnit_injective_of_flat` proves that `m ↦ 1 tensor m` is injective
for any flat `O`-module. The proof tensors the injective linear
coefficient map with that module and composes with the inverse of the
left tensor unitor.

`integralRationalStalkMap_injective` applies this argument to any
`O`-module sheaf at a point whose actual stalk is flat. The already
constructed `rationalTensorStalkIso` identifies this tensor unit with
the existing integral-to-rational stalk map.

## Flatness of the actual lattice stalk

For nonzero `d` and `pi : O`, `PiAlgebra d pi` is the actual quotient
`O[Pi]/(Pi^d-pi)`. Its published power basis makes it free, hence flat,
over `O`.

`latticeScalarStalkIso` constructs the coefficient-restriction
comparison by preservation of the actual neighborhood colimit.
For an actual `LatticePiSheaf`, the stalk is already flat over
`PiAlgebra d pi` by its definition. `scalarStalk_flat` combines these
two flatness facts in the coefficient tower and transports the result
through the constructed comparison. No extra stalk flatness witness
is required of the lattice.

`integralStalk_injective` therefore proves injectivity for the total
integral lattice stalk with only the injectivity of `O → F`.
`componentRationalStalkMap_injective` uses the actual homogeneous
sheaf inclusion, preservation of monomorphisms by the stalk functor,
and total-lattice injectivity. Thus the existing image
`componentStalkLattice` really contains an injective image of the
integral component stalk.

## Scope

The coefficient-map injectivity hypothesis applies in particular to
the ring of integers included in its fraction field; no valuation,
fraction-field or nilpotence assumption is used in this argument.
This module establishes the integral embeddings into the actual
rational stalk. It does not identify the existing all-integer
stalkwise determinant predicate with an independently constructed
exterior-subsheaf equality, construct the normalized projective
linear action, identify the full source moduli problem, or prove
representability.
