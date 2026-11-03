# Reduction of maximal-torus conjugacy to Borel subgroups

Workers 1357 and 1354.

This module supplies derived internal infrastructure for the existing
`MaximalTorusConjugacyStatement`. Its conclusions are conditional on the
structural inputs stated in their hypotheses. It proves none of those inputs.
The published target and its imports are unchanged.

`subgroupConjugate_iff_exists_commGroupSchemeIso` applies over an arbitrary
base scheme. For two commutative source group schemes, it identifies the
published `SubgroupConjugate` relation with the same rational point and a
source isomorphism in `CommGroupScheme`. Homomorphisms in that category
are the additive notation for homomorphisms of the underlying group schemes.
The proof wraps or unwraps both maps of the source isomorphism and their
inverse identities; the conjugacy equation is preserved.

The remaining definitions and intermediate lemmas work over an arbitrary
field `k : Type u`. `MaximalToriLieInBorels G` is the property that every
given maximal torus of `G` belongs to an actual Borel pair. In particular,
there is a Borel embedding `i : B ⟶ G` and a factor map `f` with `f ≫ i = j`
for that given torus embedding `j`. Defining this property does not assert
that any group satisfies it. It differs from existence of some ambient
maximal torus in each given Borel.

`SubgroupConjugate.of_maximalTorus_overgroups` takes two closed overgroups
`B` and `B'`, maximal ambient tori factoring through them, and a rational
conjugacy square between the overgroups. It also assumes
`MaximalToriAreConjugate B'`. Restricting ambient maximality through the
closed embeddings gives maximal tori in the overgroups. Transporting the
first through the supplied overgroup isomorphism gives two maximal tori
in `B'`. Their assumed conjugacy, together with the published
`SubgroupConjugate.of_overgroups`, gives the ambient conjugacy.
Neither overgroup is required to be a Borel in this lemma.

`MaximalToriAreConjugate.of_borel_inputs` applies that lemma to the Borel
pairs supplied by `MaximalToriLieInBorels G`. It explicitly assumes
conjugacy of Borel embeddings and conjugacy of maximal tori in each Borel.

Finally, `maximalTorusConjugacyStatement_of_borel_inputs` assembles the
unchanged target from three universal hypotheses: `BorelConjugacyStatement`,
containment of every maximal torus in a Borel, and conjugacy of maximal
tori in smooth affine connected solvable groups over algebraically closed
fields. A Borel supplies smoothness, connectedness and solvability by its
definition. Its closed immersion into the affine ambient group supplies
affineness. The previous lemmas give rational subgroup conjugacy, and
the first lemma yields the exact commutative source isomorphism required
by the target. All fields and schemes retain universe `u`, with no
characteristic or reductivity restriction.

The ordering of this conditional assembly follows the proof of Milne,
*Algebraic Groups* (2017), Theorem 17.10, printed pp.354–355: place the
tori in Borels, apply Theorem 17.9 to the Borels, and use Theorem 16.33(d)
inside the solvable Borel. The latter is stated and proved on printed
pp.335–336. These passages motivate the interface; no theorem asserting
their structural conclusions is introduced here. The implementation is
derived from the published subgroup-conjugacy and maximality definitions
and transport lemmas. The registered 2017 errata have no correction to
these passages.

This contribution does not complete the host task. Borel conjugacy, the
stated containment property, and solvable-group conjugacy remain proof
obligations. In particular, assuming these propositions is not a proof of
the unconditional target, and no parabolic maximal-torus result is used
to discharge them.
