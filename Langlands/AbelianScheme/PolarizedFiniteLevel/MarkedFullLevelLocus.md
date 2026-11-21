# The closed locus of all full-level marks

Fix an abelian scheme over `S`, positive `n` invertible on `S`, and an actual
section for every level coefficient tuple. The theorem
`exists_closed_markedFullLevelLocus` gives a closed immersion into `S`.
A test scheme over `S` factors through it exactly when there is an ordered
full level on the pulled-back abelian scheme whose coefficient sections are
the pullbacks of all the given marks.

The proof starts with the finite étale scheme of ordered full levels.
`FullLevel.label` sends a coefficient tuple to the actual point in the
original abelian scheme. On the parameter scheme, `markedFullLevelIdeal`
is the sum of the kernels of the relative equalizers comparing the decoded
label maps to the original marks. Testing the ideal against a morphism's
kernel imposes the equalities after arbitrary base change. The resulting
closed subscheme of the parameter is finite over `S`. Its map to `S` is
monomorphic because the labels at the unit coefficient tuples determine each
entry of the full level. A finite monomorphism is a closed immersion.

This implements the torsion and fullness conditions of Mumford, Fogarty and
Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 7.3, steps
(III) and (IV), for a given abelian scheme over a base with invertible level.
The relative frame Hilbert problem supplies every coefficient mark, so the
proof imposes all their equations in the same closed subscheme. The registered
source is `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
printed p. 133 (PDF p. 146).
