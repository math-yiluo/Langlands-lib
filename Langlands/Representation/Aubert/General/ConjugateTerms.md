# Conjugate normalized induction-Jacquet terms

This internal module combines the published actual conjugation comparisons
from `General.Conjugation`. For a locally compact nonarchimedean group `G`,
suppose `P = M ⋉ U` and `P' = M' ⋉ U'` are actual semidirect decompositions
and all three subgroups correspond under conjugation by the same element
`g`. The membership convention is `x ∈ P' ↔ g⁻¹ x g ∈ P`, and likewise for
the two other pairs. Both unipotent subgroups are assumed closed.

`inductionJacquetConjugationIso` is a natural isomorphism between the
actual normalized endofunctors `i_P r_P` and `i_P' r_P'`. It works on the
full category of smooth complex representations with carriers in
`Type (max uG uV)`. The group universe `uG` and the additional carrier
universe `uV` remain independent. There is no reductivity, admissibility,
finite-length or parabolic-opposition hypothesis for this isomorphism.

The construction first applies `inductionConjugationIso` to the inducing
Jacquet object. This changes the induction to `P'` and pulls that Jacquet
object back along the actual conjugation equivalence of the Levi groups.
It then applies `jacquetConjugationIso` inside the induction functor.
Functor whiskering and the functor associator assemble these two natural
isomorphisms. The normalization characters already correspond by the
published Haar-modulus conjugation identities used in those comparisons.

`inductionJacquetConjugationIso_hom_eval` records the actual composite
map on induced sections: evaluate the original section at `g⁻¹ y`, then
apply `coinvariantsTranslate g` to its value. On a coinvariant generator,
the latter sends `[v]` to `[g v]`. The evaluation formula is definitional
for the assembled isomorphism.

`inductionJacquet_class_eq_of_conjugation` applies
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso` to its component.
It requires only finite length of the two objects, with arbitrary proofs
of those facts. `inductionJacquetK0_eq_of_conjugation` compares the two
composite maps on the whole exact finite-length Grothendieck group under
their displayed `ParabolicFiniteLength` premises. It rewrites both
composites with `inductionK0_comp_jacquetK0` and uses
`FiniteLengthGrothendieckGroup.map_eq_of_iso`.

The provenance is internal composition of the named published maps and
exact-K0 laws. These proof bodies do not use Langlands classification,
character independence, the geometric lemma, adjointness or a
cuspidal-support theorem. The upstream conjugation comparisons are the
explicit maps on coinvariants and induced functions, with Haar-modulus
transport; they are not representation-theoretic class-invariance
assumptions.

This result does not construct a Weyl representative conjugating an
opposite standard parabolic to an associated standard parabolic. It does
not prove equality of normalized inductions from opposite parabolics
with the same Levi and inducing object. Those are distinct obligations
in the rational contragredient commutation argument. It also supplies
no induction-duality or opposite-Jacquet-duality theorem.
