# Non-supercuspidal Jacquet subquotients from geometric pieces

Author: Worker 1781. This supporting conditional deduction implements
Renard VI.5.3(ii), printed p.173 / PDF p.179, from the exact represented
geometric lemma and the exact assertion of VI.5.2. It does not supply
an unconditional proof of any of these three results. The Prop-valued
`LeviJacquetInductionNoSupercuspidalReductionStatement` names the
implication; `leviJacquetInductionNoSupercuspidal_of_geometricLemma`
implements its deduction.

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, VI.5.1–VI.5.3,
printed pp.161–173 / PDF pp.167–179, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The cited original passages were read directly.

Evaluate the actual finite functor filtration at the supercuspidal
representation of `M(k)`. The published
`ObjectRepFiltration.exists_smoothGradedObject_subquotient` places an
irreducible actual smooth subquotient in one actual smooth graded
quotient. The natural geometric-lemma isomorphism identifies that
quotient with normalized induction in `L(k)` of the transported
source intersection Jacquet module.

If the target intersection parabolic is proper in `L`, VI.5.2 says
that this induced representation has no supercuspidal irreducible
subquotient. If the target intersection parabolic is full, the source
intersection parabolic must be proper: two full intersection parabolics
would give an actual isomorphism `M ≅ L` and the forbidden ambient
conjugacy equation. The published
`rationalLeviConjugacyOfFullParabolics` constructs that isomorphism,
with inverse conjugating point in the equation. Source supercuspidality
therefore makes the Jacquet module zero. Pullback and induction
preserve its zero carrier. An actual subquotient of this zero object
cannot be irreducible, as follows directly from its injective and
surjective presentation.

All field and carrier universes, actual parabolics and Levi/radical data,
canonical topologies and supercuspidality/conjugacy conditions are the
ones in the original target. The only premises of this supporting
implication are the full `RepresentedGeometricLemmaStatement` and
`LeviInductionNoSupercuspidalSubquotientStatement`. Neither their
proofs nor their geometric and representation-theoretic inputs are
claimed here.
