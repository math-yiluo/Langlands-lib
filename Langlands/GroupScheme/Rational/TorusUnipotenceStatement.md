# Structural targets for torus actions without zero Lie weights

This unit states two structural prerequisites for the unipotence and splitness
clause of semigroup realization. Both are proposition definitions with proofs
remaining to be supplied. They use the existing actual `GroupScheme`,
`AutomorphicAction`, `actionWeightSpace`, `IsUnipotent`, and
`IsSplitUnipotent` definitions.

The source is Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second
edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The relevant passages are the proof of Proposition 2.3.11, printed p.82
(PDF p.108), and Lemma 3.3.8 and its proof, printed pp.111–112
(PDF pp.137–138). The splitness proof invokes Theorem B.3.4, printed
pp.573–574 (PDF pp.599–600), and Proposition B.4.4, printed pp.577–578
(PDF pp.603–604).

`TorusActionUnipotenceStatement` asserts that a smooth connected affine group
over any field, equipped with an action of a split torus, is unipotent if its
zero Lie weight space is zero. CGP explicitly states this general observation
inside the proof of Proposition 2.3.11. Its argument uses a maximal torus in
the semidirect product: a nonunipotent group would give a nontrivial torus
centralized by the acting torus and hence a nonzero fixed Lie vector.
The formal target uses `actionWeightSpace b 0 = ⊥` for the published intrinsic
weight space, whose defining eigencondition retains every coefficient algebra
and every torus point over it. The conclusion `IsUnipotent H` has the
published representation-theoretic meaning: every nonzero finite-dimensional
coefficient representation has a nonzero vector fixed on every scheme test.

`TorusActionSplitUnipotenceStatement` assumes unipotence as well as the same
smoothness, connectedness, affineness and zero-weight condition, and asserts
`IsSplitUnipotent H`. This is the general consequence of the splitness argument
in Lemma 3.3.8. That lemma is phrased for the semigroup subgroup, but the proof
of its first assertion only uses these properties: the maximal split normal
subgroup is stable under the torus action; its wound quotient has trivial
torus action; complete reducibility makes its Lie algebra zero; and a smooth
connected group with zero Lie algebra is trivial. Thus the maximal split
subgroup is the whole group. The target imposes no additional semigroup,
root, reductivity, or characteristic restriction.

Here `IsSplitUnipotent` means a finite normal Ga-series using actual closed
subgroups and represented fppf quotients with their kernel equality on every
test scheme. A proof must supply that published series, including its
smooth connected intermediate subgroups and one-dimensional natural vector
coordinates. An abstract group series on rational points is insufficient.

`TorusActionUnipotenceStructureStatement` is the conjunction of these two
proof obligations. The separate splitness target retains unipotence as an
explicit hypothesis so its proof can be developed independently of the first
target. All three targets are polymorphic in the field universe. They make
no representability, unipotence or split-series assumption on the original
semigroup construction, and no proof of semigroup realization is asserted
by this statement unit.
