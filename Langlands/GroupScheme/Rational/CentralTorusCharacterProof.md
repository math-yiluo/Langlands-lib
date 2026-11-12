# Central tori detect nonzero rational characters of connected reductive groups

Authors: Worker 3925 and Worker 3873, with credit to Worker 1338. Worker 1338,
an identity of the previous project instance that does not exist in this one,
wrote the conditional assembly in this task's shared draft
(`CentralTorusCharacterReduction`, carried over from that instance), which took
the structural statement as a hypothesis. Worker 3873 wrote the same
assembly, applied to the published structure proofs, inside the consumer proof
of `CentralSplitTorusCharacterStatement`; this module's proof and docstrings
adapt that text. Worker 3925 packaged the unconditional theorem and wrote this
Markdown.

`Langlands.GroupScheme.centralTorusCharacter` proves exactly the published
proposition `Langlands.GroupScheme.CentralTorusCharacterStatement.{u}` (module
[`CentralTorusCharacterStatement`](CentralTorusCharacterStatement.md)) at every
universe `u`, with no hypotheses. It belongs to task
`542b0a39-f8f7-4dcb-aceb-6f050e7c331a`.

For every field `k : Type u`, every connected reductive group scheme `G` over
`Spec k` and every nonzero rational character `χ` of `G`, it gives a
commutative group scheme `Z` over `Spec k` and a homomorphism
`i : Z.toGrp ⟶ G` such that the structure morphism of `Z` is affine and
locally of finite type, `Z` is a torus, `i` is a closed central subgroup
inclusion, and `characterRestrict i χ ≠ 0`. The field is arbitrary: the
theorem covers imperfect fields and every characteristic, and the torus need
not be split. The torus may depend on `χ` as the statement allows, although
the proof does not use `χ` to choose it.

## Implemented proof

The proof introduces `k`, `G`, `hG : IsConnectedReductive G`, `χ` and
`hχ : χ ≠ 0`.

1. The Library proof `reductiveCentralTorusSurjectivity` (module
   `Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof`) proves
   `ReductiveCentralTorusSurjectivityStatement.{u}`. The Library declaration
   `reductiveCentralDerivedProduct_of_torusSurjectivity` (module
   `Langlands.GroupScheme.Reductive.CentralDerivedProductReduction`) has type
   `ReductiveCentralTorusSurjectivityStatement.{u} →
   ReductiveCentralDerivedProductStatement.{u}`. It is a proof-producing
   `def` with `linter.defProp` disabled. Applying it to the first proof and
   then to `k`, `G` and `hG` gives a commutative group scheme `Z`, a group
   scheme `D`, homomorphisms `i : Z.toGrp ⟶ G` and `d : D ⟶ G`, and seven
   facts. The first five are the affine, locally finite type, torus, closed
   subgroup and central properties of `i`. The sixth is
   `hd : IsDerivedSubgroup d`, and the seventh is
   `Epi (subgroupProductMap i d)` in schemes over `Spec k`.
2. The first five facts are returned unchanged as the first five conjuncts of
   the target.
3. The epimorphism fact is installed as a local instance. Then
   `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
   (module `Langlands.GroupScheme.Rational.ProductDetection`) applied to `hd`,
   `i`, `χ` and `hχ` gives `characterRestrict i χ ≠ 0`. That lemma uses
   `IsDerivedSubgroup.characterRestrict_eq_zero` (module
   `Langlands.GroupScheme.Derived.KernelAnnihilation`) to make `χ` vanish on
   `d`. If `χ` also vanished on `i`, cancelling the epimorphic multiplication
   map would make `χ` zero.

The annihilation lemma is stated over the same base as `G`, so the proof
needs no transport along base change by the identity.

## Library structure results used

Every reductive structure input is an accepted and published Library theorem.
None is a hypothesis of `centralTorusCharacter` or abstract data.

- Central torus, derived subgroup and epimorphic generation:
  `reductiveCentralDerivedProduct_of_torusSurjectivity`
  (`Langlands.GroupScheme.Reductive.CentralDerivedProductReduction`). It
  combines `derivedSubgroupRepresentability`
  (`Langlands.GroupScheme.Derived.RepresentabilityProof`), which supplies the
  actual derived inclusion `d`, with the surjectivity proof below. It then
  applies `IsConnectedReductive.epi_subgroupProductMap_of_surjective`
  (`Langlands.AlgebraicGeometry.SurjectiveReducedEpi`): `G` is smooth, hence
  reduced, so a morphism surjective onto it is an epimorphism.
- Surjectivity of the multiplication map from the torus and the derived
  subgroup: `reductiveCentralTorusSurjectivity`
  (`Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof`). It
  applies `reductiveCentralTorusSurjectivity_of_semisimpleQuotient`
  (`Langlands.GroupScheme.Reductive.CentralTorusSurjectivityReduction`) to
  `reductiveCentralTorusSemisimpleQuotient`
  (`Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientProof`) and
  `semisimplePerfect` (`Langlands.GroupScheme.Derived.SemisimplePerfectProof`).
  The first supplies the closed central torus, constructed from the solvable
  radical, with semisimple quotients. The second makes semisimple field groups
  perfect.
- Annihilation of rational characters on the derived subgroup and the
  detection step: `IsDerivedSubgroup.characterRestrict_eq_zero`
  (`Langlands.GroupScheme.Derived.KernelAnnihilation`) and
  `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
  (`Langlands.GroupScheme.Rational.ProductDetection`).

The proof does not use `CentralSplitTorusCharacterStatement`,
`CharacterRestrictionStatement` or any other consumer target.

## Relation to the literature

The statement is derived; no source states it verbatim. The route follows
J. S. Milne, *Algebraic Groups* (2017), Proposition 21.61(b)⇒(c) (printed
p.443), which repeats the argument of Proposition 21.60(b)⇒(c) (printed
p.442). There the radical `R(G)` is a central torus with semisimple quotient.
That quotient is perfect (Corollary 21.50, printed p.440), so the map
`R(G) × DG → G` is surjective (Proposition 12.46(b), printed p.245). Every
homomorphism to a commutative group is trivial on `DG` (Corollary 6.19(d),
printed p.129). The Lean route uses that `G` is reduced, so surjectivity alone
gives an epimorphism of schemes, where Milne uses a faithfully flat quotient
map. The upstream proofs record their own routes in their Markdown.

## Axioms

`lean_check` reports only `propext`, `Classical.choice` and `Quot.sound`.
