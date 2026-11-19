# Existence of split reductive root data via rank-one central covers

`Langlands.GroupScheme.rootDatumExistenceIndependent` proves
`Langlands.GroupScheme.RootDatumExistenceStatement.{u}` for every universe `u`.
For every field `k : Type u`, connected reductive group over `Spec k`, and split
maximal torus `i : T.toGrp ⟶ G`, it supplies a finite `J : Type u` and a reduced
Mathlib root datum on the character and cocharacter lattices of `T`. The
condition `IsRootDatumOf i P` gives the actual adjoint roots, their lattice
pairing, and the reflection action of rational normalizer points.
[Published statement](RootDatumStatement.md)

The proof composes three published results at the same universe.

1. `rankOneCentralCover` gives the compatible group and torus isogenies from
   `SL₂ × C` and its split torus over algebraically closed fields in the
   nonempty rank-one case. [Rank-one central cover](RankOneCentralCoverProof.md)
2. `rankOneRootReducedness_of_centralCover` compares two actual roots after
   pulling them back to that cover, where the two standard `SL₂` root
   characters are opposite. The first root supplies nonemptiness. Descent
   to any field uses base change of actual root support and injective
   pullback on the split character lattice. [Reducedness from a cover](RankOneRootReducednessFromCentralCover.md)
3. `rootDatumExistence_of_rankOneReducedness` applies the resulting
   rank-one reducedness to the dynamic centralizer of a cocharacter
   annihilating a chosen root. Generation by the torus and root subgroups
   makes that centralizer centralize the full character kernel. Rational
   normalizer representatives in the centralizer give integral coroots
   from the full-kernel reflection formula. The finite Weyl-image
   construction assembles the datum indexed by the actual roots, with
   reducedness from the corresponding rank-one reduction.
   [Reflections and root-datum assembly](RootDatumFromRankOneReducedness.md)

## Independence

The central cover uses the proper quotient \(G/B\) by an ordinary Borel.
Białynicki-Birula limits, the classification of torus-fixed points, and
Hartogs extension at the point outside the open cell give \(\dim G/B \le 1\).
The cover proof supplies this bound and \(U_G(\nu) \nleq B\) to the general
curve lemmas `HomogeneousQuotient.curveUnipotentDataOfPseudoReductive` and
`HomogeneousQuotient.unipotent_dimension_le_one`.

For the kernel step, the cocharacter factors through \(B\). The smooth
connected group \(U_B(\nu)\) represents \(U_G(\nu) \cap B\) on every test
scheme. The dimension bound puts \(U_B(\nu)\) in codimension at most one
in \(U_G(\nu)\), so it is normal there by the unipotent normality theorem.
It fixes the identity coset, and the dominant orbit puts its image in the
full action kernel. The smooth connected normal closure lies in the solvable
stabilizer, and pseudo-reductivity forces the image to be trivial.
[Ordinary flag variety and kernel argument](RankOneCentralCoverProof.md#the-kernel-step-and-the-general-curve-lemmas)

The complete declaration dependency check and the inventory of reached
Library constants accompany this proof.
[Dependency audit](RootDatumExistenceIndependentDependencies.md)
