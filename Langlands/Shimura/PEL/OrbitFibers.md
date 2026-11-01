# Right translation inside a coarse orbit fiber

This is an internal deduction from `InvariantOrbits`, used to compare fine
Weil level structures after their coarse levels agree.

Let a group `G` act on the right of `X`, and let a commuting group `Γ` act
on the left. For subgroups `V ≤ U`, assume conjugation by each element of
`U` preserves `V` in the direction needed to define right translation.
If two `V`-orbits have equal images among `U`-orbits, then some actual
element `u ∈ U` translates the first fine orbit to the second.

`RightOrbit.exists_translate_of_forget_eq` chooses representatives of the
two fine orbits. Equality of their coarse orbits is, by the existing orbit
setoid, precisely the existence of `u ∈ U` relating those representatives.
The induced fine-orbit translation therefore has the required equality.
`InvariantOrbit.exists_translate_of_forget_eq` applies that result to the
underlying right orbits and uses subtype equality. The existing translation
construction already preserves monodromy invariance.

The result does not assume transitivity or freeness of the action on `X`.
It proves existence inside a coarse fiber; it asserts no uniqueness of
the translating element or of its residue class.
