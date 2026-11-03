# Finite rational inverse norm bounds over every complete coefficient field

Let `K` be any complete ultrametric normed field, `A` an actual presented
affinoid algebra over `K`, and `D : I → RationalChart K A` a family indexed by a
finite type with a chosen `Fintype`. Assume its actual rational loci cover the
whole Banach spectrum of `A`. This internal construction gives a positive real
constant `C` such that

`‖a‖ ≤ C * ‖fun i => (D i).baseMap a‖`

for every element of the original algebra `A`. It retains arbitrary positive
presentation and chart radii, trivially valued coefficient fields, nonreduced
algebras, zero quotients, and empty finite covers. In particular, no auxiliary
scalar action is an input to the final bound.

## Transfer through an isometric coefficient map

`exists_norm_bound_of_isometric_baseMap` first treats an actual bounded
`K`-algebra homomorphism `φ : A → B` preserving the norm of every original
element. Here `B` is another actual presented affinoid algebra over `K`. For this
intermediate result only, a nontrivially normed field `L` with a
`NormedAlgebra L B` structure is supplied. The scalar field may be in an
independent universe, and no map from `K` to `L` or scalar tower is assumed.

Pull back every rational chart along `φ`. The existing exact `pullback_locus`
identity proves that these charts cover the spectrum of `B`. Apply
`AuxiliaryScalar.exists_norm_bound` to that family and its induced `L`-actions.
Each original rational quotient maps to its pullback quotient by the actual
bounded `pullbackMap`. Choose a positive bound `M i` for each of these finitely
many maps. The sum of the `M i`, plus one, is positive and bounds every `M i`,
including when the index type is empty. The finite product norm inequality and
the commuting identity `pullbackMap_baseMap` therefore bound the enlarged
restriction family by this common constant times the original restriction
family. Combining this inequality with the estimate on `B` and the norm equality
for `φ` proves the intermediate result on `A`.

This argument uses the explicit boundedness of the quotient transport maps. It
does not use a continuous-linear operator norm over a trivially valued original
field. Auxiliary scalar actions are needed only on `B` and its chart quotients,
not on the original chart algebras or their overlap algebras.

## Removing the auxiliary input

`exists_finiteRestrictionBound` splits according to whether the original norm
attains a value greater than one.

If it does, the existing normed-field structure on `K`, with that witness, is a
nontrivially normed field structure. Apply the auxiliary-scalar estimate directly
with `L = K` and the original normed action on `A`.

Otherwise every element of `K` has norm at most one. Applying this to a nonzero
element and its inverse, and using multiplicativity of the norm, proves that its
norm equals one. It follows that no norm from `K` is a nonzero integer power of
two: a zero element has norm zero, whereas all such powers are positive; a
nonzero element has norm one, and `2 ^ n = 1` forces `n = 0`.

Consequently the existing independent-radius field construction applies to the
actual completed Gauss Laurent ring `CompletedGaussLaurent K 2`. Its normed-field
structure has an element of norm two, namely the completed Laurent variable, so
it is nontrivially normed. The existing completed-scalar map gives an actual
normed action of this field on the relative Laurent annulus
`RelativeLaurentAnnulus.algebra K A 2`. This annulus remains an actual presented
affinoid algebra over the original `K`. The constructed original coefficient map
into it is bounded and preserves norms by `RelativeLaurentAnnulus.norm_baseMap`.
The intermediate transfer theorem therefore gives the desired estimate in the
original algebra. Neither a value-group countability hypothesis nor an
assumption of strictness or of reducedness is introduced.

## Chosen bound and provenance

`finiteRestrictionBound D hcover` chooses a constant from the proved existence
theorem. `finiteRestrictionBound_pos` proves its strict positivity, and
`norm_le_finiteRestrictionBound` states its estimate using the original
`finiteRestriction` map. These are constants and bounds for the actual quotient
norms; no replacement algebra or assumed analytic output appears in their input.

This is an internal consequence of the constructed finite rational restriction
estimate, exact rational base change, the completed Laurent field and its actual
scalar action, and the arbitrary-radius coefficient retraction and isometry.
The proof is given above and makes no new original-literature attribution. It
does not yet construct finite-cover descent of bounded algebra homomorphisms,
full-domain intersections, unrestricted analytic atlas restrictions, or analytic
and equivariant sites. Those remain further construction steps.
