# Tensor powers of line bundles glued from unit cocycles

This internal unit constructs the actual tensor-power comparison for a
line glued from a unit cocycle. For any covering family of opens `T i`
on an arbitrary scheme `X` and any unit cocycle `g` on their overlaps,
`powerIso g hg hT n` is an isomorphism of actual module sheaves

`tensorPow (glued g) n ≅ glued (g ^ n)`.

The assertion includes order zero. The definition `oneIso` identifies
the line glued from the constant unit cocycle with the actual structure
module, using its section one on each chart as an actual frame. The
frame reconstruction isomorphism supplies this comparison.

The lemma `IsCocycle.pow` follows by taking powers of the cocycle
identity and using multiplicativity of powers over the commutative
section rings. The recursive construction of `powerIso` starts with
`oneIso`; at the successor step it tensors the previous comparison with
the original glued line and applies the existing multiplication
isomorphism for two cocycle lines. The power identity identifies the
resulting product cocycle with the next power.

The provenance is internal: this extends the existing actual cocycle
tensor-product comparison to iterated tensor powers. It asserts an
isomorphism of module sheaves and makes no ampleness claim.
