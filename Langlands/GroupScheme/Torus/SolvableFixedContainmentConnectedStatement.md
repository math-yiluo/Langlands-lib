# Connected invariant subgroups containing a torus fixed subgroup

`Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedStatement`
is a general geometric prerequisite for the solvable alternative of the
semigroup intersection comparison. It is a proposition definition, not a proof.

Let \(H\) be a smooth connected affine group scheme over any field \(k\),
with `RelativeRoot.IsSolvableScheme H`: one derived-series bound works for the
point groups on every test scheme over \(k\). Let a split torus \(S\) act on
\(H\) by the actual automorphic action \(c\). If an invariant subgroup functor
\(F\) contains the all-refinement fixed subgroup `c.fixedSubgroup` and is
represented by a smooth closed inclusion \(q:C\to H\), then \(C\) is connected.
The assertion quantifies over every such representative at arbitrary universe
`u`. Neither the torus action nor the subgroup is replaced by field points.

This is a derived statement from Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), Proposition 2.1.12(2),(3), printed pp.59–60
(PDF pp.85–86), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`, content SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Part (3) gives connectedness of the torus fixed subgroup of a connected
solvable ambient group. After choosing a generic cocharacter with the same
fixed subgroup, containment identifies the fixed subgroup of \(C\) with the
ambient fixed subgroup. Part (2) then implies that \(C\) is connected. The
all-test derived-series hypothesis implies the geometric solvability premise
used there; establishing that bridge is part of proving this statement.

CGP applies this argument to a semigroup intersection in Proposition 3.3.10(b),
printed p.114 (PDF p.140). The statement here contains no semigroup, realization
or intersection-comparison premise, so it is an independent geometric
prerequisite. Its proof and the full comparison theorem remain outstanding.
