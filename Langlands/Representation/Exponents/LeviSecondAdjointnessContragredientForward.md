# The represented-Levi contragredient formula from second adjointness

Author: Worker 138.

This derived module proves the forward implication in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
VI.9.6, printed pp.201–202 / PDF pp.207–208: (VI.9.6.1) implies (VI.9.6.2), using the
Hom chain (VI.9.6.3). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Work over a nonarchimedean local field `k : Type u`, with a connected reductive `G`
and its canonical rational-point topology, assumed locally compact and
nonarchimedean. Let `P = MN` and `Pbar = M Nbar` be represented rational parabolics
with the indicated rational Levi embeddings and geometric unipotent radicals.
Their subgroup multiplication maps are isomorphisms. Both normalized Jacquet
functors take values in smooth complex representations of the actual rational
points `M(k)` with their canonical topology. All representation carriers are in
`max u v`, where `u` and `v` remain independent.

`leviContragredientIsoOfSecondAdjunction` takes an adjunction `i_P ⊣ r_Pbar`
and constructs a natural isomorphism `D_G ⋙ r_Pbar ≅ r_P.op ⋙ D_M`.
`nonempty_leviContragredientIso_of_secondAdjunction` is its existential version.
No admissibility or finiteness condition is imposed.
The direction proved here does not need equality of the two Levi images or the
opposition intersection condition; those hypotheses belong to the full target
equivalence.

The construction chooses the natural induction-duality isomorphism from
`nonempty_leviInductionContragredientIso` and first adjointness from
`leviFirstAdjointnessAdjunction`. It feeds them into the abstract
`SmoothRep.contragredientIsoOfSecondAdjunction`, which compares two
right adjoints of a common left functor. This implements Renard's Yoneda argument
without assuming that all smooth representations are reflexive. The existential
version maps the construction over `Nonempty`.

The reverse implication and the exact theorem of
`LeviSecondAdjointnessContragredientEquivalenceStatement` remain separate
obligations.
