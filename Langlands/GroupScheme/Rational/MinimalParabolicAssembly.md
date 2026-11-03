# Conditional assembly of maximal split-torus conjugacy

This internal supporting unit derives the exact ambient statement from
explicit geometric premises. It imports the published minimal-parabolic
interfaces and the split-rank reduction, without changing their definitions.
It does not prove any of the geometric premises.

`MaximalSplitTorusMinimalParabolicContainmentStatement.{u}` is the
Prop-valued containment interface: for every field `k`, connected reductive
group scheme `G`, and actual maximal split torus `i : T.toGrp ⟶ G`, there
are an actual minimal parabolic `j : P ⟶ G` and a group-scheme morphism
`f : T.toGrp ⟶ P` with `f ≫ j = i`. The field, group, torus and parabolic
range over arbitrary universe `u`. This assertion is defined here and
remains unproved.

The containment interface is derived from the opening step of the proof
of Borel–Tits, *Groupes réductifs* (1965), Theorem 4.21, printed p.93
(one-based PDF page 40). That step invokes 4.15 and 4.16 to choose
minimal parabolics whose Levi subgroups are the centralizers of the two
maximal split tori. The interface retains only the resulting torus
factorization into the containing parabolic, so it claims less than that
source step. The file does not implement the source's construction of
these parabolics.

`maximalSplitTorus_subgroupConjugate_of_minimalParabolics` assumes rational
conjugacy of minimal parabolics, rational conjugacy inside a minimal
parabolic of ambient maximal split tori that factor through it, and
containment of every ambient maximal split torus in an actual minimal
parabolic. These hypotheses concern actual group schemes and morphisms
over an arbitrary field, in arbitrary universe `u`.

Choose minimal parabolics containing the two given tori. Conjugating the
first parabolic to the second transports the first torus's factorization
to the second parabolic. Its ambient conjugate remains a maximal split
torus by invariance under the inner isomorphism. The inside-parabolic
conjugacy premise therefore applies. `SubgroupConjugate.of_overgroups`
combines the two conjugacies and produces an actual ambient base section
and an actual isomorphism between the torus sources.

`maximalSplitTorusConjugacyStatement_of_minimalParabolics_extension` adds
maximal extension of every closed finite split torus. It applies the first
lemma to supply the ambient conjugacy premise of the rank-supremum
reduction. The result is the exact existing universe-general
`MaximalSplitTorusConjugacyStatement`, including both rational conjugacy
and equality of the finite splitting cardinal with the existing
`splitRank` supremum. All four geometric premises remain explicit.

The proofs are internal categorical compositions of the imported
interfaces. The containment bridge from a generic cocharacter to a
minimal parabolic is a separate result, and is not used to discharge
containment here. Generic-cocharacter existence, generic minimality,
minimal-parabolic conjugacy, inside-parabolic torus conjugacy, and maximal
extension remain separate obligations toward an unconditional proof of
the host target.
