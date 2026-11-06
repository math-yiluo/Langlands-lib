# Full self-intersections in the geometric lemma

Worker 1717. This internal development treats the self-intersection data of the
geometric lemma (Renard VI.5.1) in the degenerate case where the parabolic
`P' = M ∩ zPz⁻¹` of `M` is all of `M`. It is support for the proof of the
endomorphism dichotomy of Renard VI.5.3, where such a double coset `P z P`
contributes a twist of the inducing representation by conjugation by `z`.

Throughout, `GeometricLemmaIntersectionDatum` is the project's bundle of
intersection data for one double coset `P z Q`
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`):
`p' : P' ⟶ M` is the parabolic `M ∩ zQz⁻¹` of `M` with Levi `l' : M' ⟶ P'`
(`M' = M ∩ zLz⁻¹`); `q' : Q' ⟶ L` is the parabolic `L ∩ z⁻¹Pz` of `L` with Levi
`lQ' : L' ⟶ Q'` (`L' = L ∩ z⁻¹Mz`); and `φ : L' ≅ M'` is conjugation by `z`, with
`φ.hom ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ (G.innerIso z).hom`. A
*self-intersection datum* is one whose second parabolic `Q = LU` is the first
one, `P = MN` (same `p`, `l`, `r` and proofs), so `L = M`.

## Declarations

- `Langlands.GroupScheme.IsClosedSubgroup.isIso_of_isIso_comp`: for group-scheme
  homomorphisms `i : A ⟶ B` and `j : B ⟶ C` over a scheme `S`, if `j` is a closed
  subgroup and `i ≫ j` is an isomorphism, then `j` is an isomorphism. A closed
  subgroup is a monomorphism of schemes, hence of group schemes, and
  `inv (i ≫ j) ≫ i` is a section of `j`.
- `GeometricLemmaIntersectionDatum.isIso_l'_of_isIso_p'` (any datum at `P z Q`):
  if `p'` is an isomorphism, so is `l'`. This is
  `IsRationalLeviSubgroup.isIso_of_isIso_parabolic` applied to the Levi `l'` of the
  parabolic `p'` of the connected reductive group `M`.

The remaining declarations concern a self-intersection datum `D` at `P z P` with
`p'` an isomorphism.

- `isIso_lQ'_comp_q'_of_isIso_p'`: the closed embedding `lQ' ≫ q' : L' ⟶ M` of
  `M ∩ z⁻¹Mz` into `M` is an isomorphism. Since `p'` and `l'` are isomorphisms,
  so is `φ.hom ≫ l' ≫ p' : L' ⟶ M`, and the endomorphism
  `f = inv (φ.hom ≫ l' ≫ p') ≫ lQ' ≫ q'` of `M` is a closed subgroup (a composite
  of an isomorphism and two closed subgroups). A closed-subgroup endomorphism of
  the connected reductive group `M` is an isomorphism
  (`Langlands.GroupScheme.IsConnectedReductive.isIso_of_isClosedSubgroup`, in
  `Langlands/GroupScheme/Rational/ClosedSelfEmbedding.lean`), and
  `lQ' ≫ q' = (φ.hom ≫ l' ≫ p') ≫ f`.
- `isIso_q'_of_isIso_p'`: `q'` is an isomorphism, i.e. `Q' = M ∩ z⁻¹Pz` is all of
  `M`; by the previous item and `IsClosedSubgroup.isIso_of_isIso_comp`.
- `isIso_lQ'_of_isIso_p'`: `lQ'` is an isomorphism, i.e. `L' = M ∩ z⁻¹Mz` is all
  of `Q'`; from the two previous items.
- `selfConjugation : M ≅ M` (definition): the automorphism of `M` given by the
  composite of the inverse of `lQ' ≫ q' : L' ≅ M`, the isomorphism `φ : L' ≅ M'`,
  and `l' ≫ p' : M' ≅ M`. Its underlying morphism is recorded in
  `selfConjugation_hom` as `inv (lQ' ≫ q') ≫ φ.hom ≫ l' ≫ p'`.
- `selfConjugation_comp`: `selfConjugation` is conjugation by `z` inside `G`:
  `D.selfConjugation.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom`. This follows from
  `selfConjugation_hom` and the datum's identity `φ_comp`.
- `selfConjugation_map_rationalPoints`: on rational points, for `a ∈ L'(F)`,
  `selfConjugation` sends the image of `a` under `lQ' ≫ q'` to the image of
  `φ(a) ∈ M'(F)` under `l' ≫ p'`.

None of these results uses maximality of `P` or properness of the parabolics.

## Provenance

Internal. The datum and its meaning are those of the project's formalization of
Renard VI.5.1 (`GeometricLemmaIntersectionDatum`); this module adds only formal
consequences of its fields in the case `Q = P`, `P' = M`, together with the
closed-self-embedding lemma for connected reductive groups. In Renard's proof of
VI.5.3 the corresponding step is the observation that a double coset whose
intersection `M ∩ zPz⁻¹` is all of `M` normalizes `M`; no source statement is
formalized here.
