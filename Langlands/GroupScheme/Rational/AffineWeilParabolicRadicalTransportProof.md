# Parabolic–radical diagrams under finite separable Weil restriction: proof

Authors: Worker 207 (dynamic transport and assembly) and Worker 110 (connected
reductivity of the restriction).

`Langlands.GroupScheme.affineWeilParabolicRadicalTransport` proves exactly
`Langlands.GroupScheme.AffineWeilParabolicRadicalTransportStatement.{u}` for an
arbitrary universe `u`. This is the parabolic and unipotent-radical part of
Borel–Tits 6.19 and 6.21(i). Let `k ⊆ K` be a finite separable extension of
arbitrary fields and `G` a connected reductive group over `Spec K`. The
statement has two halves:

1. (preservation) For a parabolic subgroup `p : P → G` and a geometric
   unipotent radical `r : U → P`, `AffineWeil.map k K p` is parabolic in
   `R(G) = AffineWeil.groupScheme k K G` and `AffineWeil.map k K r` is a
   geometric unipotent radical.
2. (descent) Every parabolic `p : P → R(G)` with geometric unipotent radical
   `r : U → P` is isomorphic to the restriction of such a diagram over `K`.
   The isomorphisms commute with both inclusions.

The proof uses the actual Weil restriction, the actual `AffineWeil.map`, and
the existing predicates `IsParabolicSubgroup` and
`LeviSubgroup.IsGeometricUnipotentRadical` on all test schemes. It adds no
premise.

## Route

The proof is dynamic: parabolics and their radicals are the dynamic subgroups
`P(χ)` and `U(χ)` of cocharacters, and Weil restriction transports dynamic
subgroups.

Helper lemmas (namespace `AffineWeilParabolicRadicalTransport`), for a
connected reductive `G` over a field:

- `exists_isRepresentedBy_parabolic`: a parabolic subgroup represents
  `Dynamic.parabolic χ` for some cocharacter `χ`. This is the published
  `parabolicDynamic` (forward direction).
- `isParabolicSubgroup_of_isRepresentedBy`: a representative of
  `Dynamic.parabolic χ` is a parabolic subgroup (`parabolicDynamic`,
  converse direction; closedness from
  `Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic`).
- `isGeometricUnipotentRadical_of_isRepresentedBy`: if `p` represents
  `P(χ)` and `r ≫ p` represents `U(χ)`, then `r` is a geometric unipotent
  radical (published `dynamicGeometricUnipotentRadical`, then
  `.leviSubgroup`).
- `isRepresentedBy_unipotent_of_isUnipotentRadical`: if `p` represents
  `P(χ)` and `r` is any unipotent radical of `P`, then `r ≫ p` represents
  `U(χ)`. The published representative `Dynamic.Affine.unipotentHom χ`
  lifts into `P`, and by `dynamicGeometricUnipotentRadical` the lift is a
  unipotent radical. Two unipotent radicals have equal ranges
  (`IsUnipotentRadical.range_eq`), and `range_comp_le_of_le` pushes this
  equality forward along `p`.

`affineWeilParabolicRadicalTransport_of_connectedReductive` proves the
statement from the hypothesis that finite separable affine Weil restriction
preserves connected reductivity.

- Preservation: choose `χ` with `p` representing `P(χ)`. Then `r ≫ p`
  represents `U(χ)`. By `AffineWeil.isRepresentedBy_map_parabolic` and
  `isRepresentedBy_map_unipotent` (module `AffineWeilDynamicTransport`),
  `map p` and `map (r ≫ p) = map r ≫ map p` represent the dynamic subgroups of
  the restricted cocharacter `AffineWeil.cocharacter k K χ`. Since `R(G)` is
  connected reductive, the helper lemmas show that `map p` is parabolic and
  `map r` is a geometric unipotent radical.
- Descent: choose `ν` with `p` representing `P(ν)` in `R(G)`. Then
  `cocharacter_descendCocharacter` writes `ν = cocharacter k K χ` with
  `χ = descendCocharacter k ν`. Over `K`, take the published affine
  representatives `p' = Dynamic.Affine.parabolicHom χ` and `r'`, the lift of
  `Dynamic.Affine.unipotentHom χ` into its source. These are a parabolic and
  a geometric unipotent radical, as shown above. Their restrictions represent
  `P(ν)` and `U(ν)`, as do `p` and `r ≫ p`, the latter by the last helper
  lemma. `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives the
  isomorphisms `eP : P ≅ R(P')` and `eU : U ≅ R(U')` compatible with the
  inclusions. The second square is checked after composing with the
  monomorphism `map p'` (`IsRepresentedBy.hom_ext`).

The final theorem `affineWeilParabolicRadicalTransport` discharges the
hypothesis by `AffineWeil.isConnectedReductive_restriction` (module
`Reductive.AffineWeilConnectedReductive`, Worker 110).

## Supporting modules in this contribution

- `Langlands.GroupScheme.AffineWeilCounit`: counit and unit of Weil restriction
  on test schemes, and scalar points.
- `Langlands.GroupScheme.AffineWeilDynamicTransport`: the converse Weil
  dynamics on standard tests, transport of dynamic representatives, and
  descent of cocharacters.
- `Langlands.GroupScheme.Reductive.FiniteProducts` (Worker 110) and
  `Langlands.GroupScheme.Reductive.AffineWeilConnectedReductive`: connected
  reductivity of the restriction.

## Provenance and scope

The statement and its sources (Borel–Tits, *Groupes réductifs*, 6.17–6.19
and 6.21(i)) are documented in its own Markdown pair. The implemented route
need not follow Borel–Tits. It uses the dynamic description of parabolics and
their unipotent radicals, available in the Library as `parabolicDynamic` and
`dynamicGeometricUnipotentRadical`. The proof is an internal composition of published
Library results and the supporting modules above. It does not use any proof
of `AffineWeilParabolicElementarySubgroupStatement`,
`LocalKneserTitsStatement`, or any module under `SimplyConnected`. It adds
no perfectness, infinitude or characteristic assumption, and uses only the
standard axioms.
