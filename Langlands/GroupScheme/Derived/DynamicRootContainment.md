# Dynamic and relative root subgroups in the actual derived subgroup

This internal unit is derived from the Library definitions of the dynamic
identity-limit subgroup, relative root subgroup functors and the
scheme-theoretic derived subgroup. Its purpose is to supply the first factor
in lifting actual root subgroups through a simply connected derived cover.
The factor through the simply connected covering map remains a separate
obligation.

For any base scheme and any cocharacter of a group scheme, the dynamic
identity-limit subgroup lies in every closed subgroup containing all
commutators on every test scheme. The proof starts from an affine-line
extension `e` of the conjugation orbit of `g`, with `e(0) = 1`. The morphism
`e` multiplied by the inverse of the constant morphism `g` restricts on the
unit locus to a commutator. It therefore factors through the given closed
subgroup by `AffineLine.exists_lift_of_unitInclusion`. Evaluation at zero
puts `g⁻¹`, and hence `g`, in that subgroup. This requires neither normality
as a separate premise nor representability of the derived intersection.

The definition of the scheme-theoretic derived subgroup as the intersection
of these closed subgroups gives `Dynamic.unipotent_le_derivedSubgroup`.
Over a field, a nonzero character of a split torus pairs positively with
some cocharacter. The published positive-pairing contraction lemma then
puts its full relative root subgroup functor in the derived subgroup,
on every test scheme.

If `d : D ⟶ G` is the supplied actual derived inclusion and `j : U ⟶ G`
represents that root subgroup functor, `RelativeRoot.derivedLift` is the
resulting morphism `U ⟶ D`. Its composite with `d` is exactly `j`.
Monicity of the actual derived inclusion proves uniqueness of this factor.
The nonzero-character premise is essential; this unit makes no assertion
for the zero character.
