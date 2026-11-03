# Coordinate lines in representations of unipotent groups

This is an internal consequence of the published matrix representation,
multiplicative group, Yoneda, and `Torus.UnipotentHom` constructions. Worker 362
authored the new constructions and proofs.

`MatrixRepresentation.PreservesCoordinateLine` asks that every matrix of the
representation, on every scheme test, send the chosen standard basis vector to
a global unit times that vector. It retains arbitrary commutative coefficient
rings, finite coordinate index types, and universe `u`.

`coordinateLineScalar` chooses that unit. Its value equals the corresponding
diagonal matrix entry, so it is independent of the existential choice.
Matrix multiplication and the line equation prove multiplicativity, and
naturality of the original matrices proves compatibility with pullback of
global sections. `coordinateLineCharacter` is the actual group-scheme
homomorphism to the multiplicative group obtained by the fully faithful
group-valued Yoneda construction. `coordinateLineCharacter_scalar` identifies
its value with the chosen unit on every scheme test.

Over an arbitrary field, `fixed_coordinateLine_of_isUnipotent` applies the
published triviality of homomorphisms from a unipotent group to split tori to
this actual character. The multiplicative group is the split torus of rank
one. Every line scalar is therefore one, so every test matrix fixes the basis
vector. Smoothness, affineness, connectedness, and reducedness are not premises.

This unit supplies a step from a Chevalley line stabilizer to a vector
stabilizer for a subgroup that is already known to be unipotent. It does not
construct a subgroup quotient or prove its affineness.

`range_iff_fixes_coordinateLine_of_isUnipotent` records that step exactly.
Its inputs are a homomorphism `z : H ⟶ G` with unipotent source and a
representation of `G` for which the range of `z`, on every scheme test,
is exactly the points preserving the chosen coordinate line up to a global
unit. Its conclusion identifies that same range with the points fixing the
basis vector itself. Restricting the representation along `z` supplies
the preserved line, so the preceding theorem proves the forward implication.
For the reverse implication, scalar one witnesses line preservation.
No monomorphism, smoothness, connectedness, or affineness premise is used.
