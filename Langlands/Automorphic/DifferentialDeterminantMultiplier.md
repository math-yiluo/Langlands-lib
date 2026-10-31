# Determinant multiplication and genuine adelic differential operators

Author: Worker 2. This internal construction specializes the generic
archimedean locally constant multiplier to each actual infinite slice of a
finite-order Hecke determinant multiplier. It uses every number field in
an arbitrary universe and every natural rank, including zero. Coefficients
are complex, and smoothness is the existing real smoothness in mixed
completion coordinates.

`determinantSliceScalar` is precisely the complex value of the actual
Hecke character on the determinant of `pair(a,b)`. Its local constancy is
the published finite-order local-constancy theorem pulled back along the
actual continuous infinite-slice inclusion. `finiteSmoothSlice_determinantMultiplier`
identifies the slice of the actual adelic multiplication automorphism with
the generic archimedean scalar multiplier on the original smooth slice.

The generic genuine enveloping commutation theorem applies to every slice.
Faithfulness of `finiteSmoothSlice` then proves
`finiteSmoothEnvelopingAction_determinantMultiplier` on the existing
finite-smooth adelic functions. Restriction to the actual algebra center
gives the center identity, and
`finiteSmoothDeterminantCenterIntertwiner` packages actual multiplication
as an intertwiner of the existing center representation.

The published injective slice-family criterion and finite-vector image
theorem give preservation of simultaneous center finiteness. This is one
finite center orbit of the complete family of slices. More strongly,
`centerFamilyAnnihilator_determinantMultiplier` proves equality of the
single annihilator ideal before and after multiplication. Slice
injectivity identifies annihilation of every slice with vanishing of the
actual central action on the adelic function; commutation and injectivity
of the multiplication automorphism give equivalence of these zero
conditions. Thus every specified common ideal is retained exactly.

Multiplication by the inverse character gives an actual center-finite
preimage for every center-finite function. The resulting submodule image
equality defines
`CenterFiniteFiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier`
by restricting the existing continuous linear equivalence. It keeps the
inherited subtype topology from continuous rational-invariant functions.
Its forward and inverse values are multiplication by the determinant
character and its inverse. It commutes with the genuine center-finite
enveloping action and satisfies the same finite right-translation formula
`R(d) Mχ = χ(det(ofFinite d)) Mχ R(d)`.

The provenance is a direct internal specialization and restriction of
`SmoothDeterminantMultiplier`, `FiniteDifferential`,
`DifferentialCenterFinite`, and `ArchimedeanLocallyConstantMultiplier`.
All preservation and commutation obligations above are proved from the
actual operators; none is a supplied assumption. Growth, compact-type
finiteness, cuspidality on this carrier, and total twists of full
automorphic operator realizations remain separate.
