# The split solvable envelope inside pseudo-parabolic subgroups

Workers 1405 and 846 wrote this proof.
`Langlands.GroupScheme.pseudoParabolicSplitSolvableEnvelope` proves the exact target
`Langlands.GroupScheme.PseudoParabolicSplitSolvableEnvelopeStatement.{u}` in every universe.
That statement records the split solvable subgroup `S ⋉ R_us,k(P)` from the start of the proof of
Theorem C.2.5 in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), printed
p. 595 (PDF p. 621, registered source `conrad-gabber-prasad-2015-pseudo-reductive`).

## Construction

Take the data of the statement: a pseudo-parabolic `i : P ⟶ G`, a maximal split torus
`s : S.toGrp ⟶ P` and a split unipotent radical `j : U ⟶ P`. Normality of the radical makes
`S` normalize the image of `U`. The witness is:

* `H` is the semidirect product `U ⋊ S` of the Library's conjugation action
  `AutomorphicAction.ofNormalizedConjugation j s hn`;
* `h` is the Library's `SubgroupFunctor.normalizedProductHom j s hn`, which is `(u, t) ↦ j(u) s(t)`.

## Proof

The proof applies
`SplitSolvableEnvelope.exists_envelope_of_isSplitSolvable` from
`Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProduct`. Its inputs are:

* `hi.isClosedSubgroup`: a pseudo-parabolic subgroup is closed;
* `hs.1`: a maximal split torus is a split subtorus;
* `hj`: the split unipotent radical.

That theorem proves the product half: `h` is a closed subgroup and represents the fppf-local
product `IsFppfProduct (range s) (range j) h`. Its remaining hypothesis is split solvability of
every semidirect product of `S` acting on a smooth connected affine `U`. The proof supplies it with
`AutomorphicAction.isSplitSolvableGroupScheme_semidirectProduct` from
`Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeSeries`, using that `S` is a
split torus (`hs.1.1`) and `U` is split unipotent (`hj.isSplitUnipotent`).

The supporting modules are:

* `Langlands.GroupScheme.Unipotent.SplitTorusSubgroupHom` (Worker 1405): a split torus and a
  unipotent closed subgroup meet trivially. This gives the trivial kernel of `h`.
* `Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProduct` (Worker 1405):
  closedness and the fppf product, and the assembly theorem.
* `Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeSeries` (Worker 846):
  split solvability of `U ⋊ S`.

Each module's Markdown describes its proof.
