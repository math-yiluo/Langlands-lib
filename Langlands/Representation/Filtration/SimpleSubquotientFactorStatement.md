# A simple actual subquotient is a factor of every composition series

`Langlands.SimpleSubquotientFactorTheorem` is an internal algebraic statement.
It says that every irreducible smooth subquotient of a smooth representation is
equivalent to a graded quotient of each composition series of that
representation. It is a prerequisite for the association theorem for cuspidal
induction: after a simple constituent is extracted from a Jacquet module, this
statement matches it to a factor of any composition series that is supplied.

## Data and hypotheses

The statement quantifies over the following:

- a field `k` and a group `G` with an arbitrary topology;
- a smooth representation `A : SmoothRep k G`;
- a length `r : ℕ`, which may be zero;
- a supplied filtration `s : ObjectRepFiltration (Rep.of A.representation) r`
  of the underlying actual representation, together with evidence
  `s.HasSimpleFactors` that every graded quotient `s.gradedRepresentation j` is
  irreducible;
- a smooth representation `D : SmoothRep k G` with `D.IsIrreducible`;
- an actual invariant submodule `S` of `A`, and an actual invariant submodule
  `U` of the smooth subrepresentation `SmoothRep.subrepresentation A S`;
- an equivariant linear equivalence, given as
  `Nonempty (D.representation.Equiv (SmoothRep.subquotient A S U).representation)`,
  from `D` to the actual subquotient `S/U`.

The universes of `k`, of `G`, of the carrier of `A`, and of the carrier of `D`
are independent (`uK`, `uG`, `uV`, `uW`). The existing relation
`SmoothRep.IsSubquotient` requires both carriers to lie in the same universe.
For this reason the statement does not use it. Instead it states the premise
with the actual submodules `S` and `U` and an equivalence from `D`. The
statement makes no assumption of finite dimension, admissibility,
Noetherianness, or a separate finite length. The only finiteness is that the
filtration `s` is finite.

## Conclusion

There is an index `j : Fin r` and an equivariant linear equivalence
`Nonempty (D.representation.Equiv (s.gradedRepresentation j).ρ)`.
The conclusion holds for the given filtration `s` itself. The statement does not
say only that some other composition series exists. When `r = 0`, the conclusion
is false, so the statement says that the premises cannot all hold. Indeed, a
filtration of length zero forces `A = 0`, so `S/U` is zero, and so it is not
equivalent to the irreducible `D`.

## Provenance

This is the standard Jordan–Hölder fact that each simple subquotient of a
module of finite length is one of its composition factors. The formulation here
is internal. It uses the existing definitions `ObjectRepFiltration`,
`ObjectRepFiltration.HasSimpleFactors`,
`ObjectRepFiltration.gradedRepresentation` (from
`Langlands.Representation.Filtration.ObjectDefinitions`),
`SmoothRep.subrepresentation`, `SmoothRep.subquotient` (from
`Langlands.Representation.Category.Subquotients`), and `SmoothRep.IsIrreducible`
(from `Langlands.Representation.Category.Basic`) without change.

The intended proof route is as follows. Write `A_j` for the steps of `s`. Map
`S ∩ A_j` into `S/U` and take the least `j` for which the image of
`S ∩ A_(j+1)` is nonzero. Irreducibility of `D ≅ S/U` makes this image all of
`S/U`, and the image of `S ∩ A_j` is zero. This gives a nonzero intertwiner
from a subrepresentation of `gr_j` onto `S/U`. Since `gr_j` is simple, that
subrepresentation is all of `gr_j`. Since `S/U` is simple, the kernel is zero.
So the intertwiner is an equivalence.

This file states the proposition only. It does not contain a proof, and it
assumes no analytic result about parabolic induction or association.
