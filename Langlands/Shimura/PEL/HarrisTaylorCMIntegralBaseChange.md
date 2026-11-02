# Normalized CM classes and transported integral witnesses

These internal comparisons concern the existing actual pointed Harris pullback
`levelDataBaseChange`, with the normalized imaginary-quadratic CM section and
conjugated reflex scalar map. They retain the original positive auxiliary left
involution, opposite right-action level convention and all displayed tensor,
Picard, chosen dual geometry, polarization, Weil, torsion and adelic inputs.
The source and target points are related by composition with the given base
map. Integral actions on the original abelian schemes remain supplied.

`levelDataBaseChange_determinantDimensionCondition` proves the full joint
normalized determinant-and-dimension condition for the same actual changed
representative. Its proof applies the existing normalized joint-condition
base-change theorem to the original action. The actual action of the changed
Harris representative is exactly the action obtained by that theorem. The
original Lie base-change naturality hypothesis remains explicit.

`classOf_eq_iff_exists_mappedIntegralPolarizedMultiple` characterizes equality
of the original normalized polarized CM classes by an orbit equation after
pointed base change. The right side still quantifies over rational action
isomorphisms of the original representatives, the original rational unit
multiplier, and exact integral polarization witnesses for the supplied original
order actions. It transports those actions and witnesses and checks the orbit
equation for the image of that same isomorphism and multiplier. The proof
rewrites the original equality by the existing integral class criterion, then
applies the fixed-isomorphism orbit equivalence in each direction.

`mappedIntegralPolarizedWitnessOfClassEquality` constructs actual witness
data from a proof of original normalized class equality: a rational unit,
an isomorphism of the original actions, its integral-multiple proof and the
target orbit equation. It applies classical choice to the existential in the
proved criterion. The chosen original isomorphism is mapped to the target
only when forming that equation; the output retains the original isomorphism
and multiplier as data. No canonicity of the selected witness is asserted.

The second theorem does not assume Lie naturality: its source joint conditions
already supply the normalized source classes, and it checks an actual target
orbit equation. The first theorem separately shows that, when Lie naturality
is available, these are also representatives satisfying the target joint test.
The criterion does not quantify over arbitrary target isomorphisms and does
not imply injectivity of the whole class pullback. It proves no existence of
integral actions, no comparison of independently chosen geometric points, and
no representing scheme, admissibility or projectivity. Its provenance is the
internal combination of the imported normalized class criterion, actual
joint-condition pullback, integral witness transport and fixed-orbit comparison.
