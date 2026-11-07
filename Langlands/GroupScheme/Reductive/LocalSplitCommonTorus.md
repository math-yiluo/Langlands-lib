# Moving a fibrewise root datum to a common coordinate torus

Module `Langlands.GroupScheme.Reductive.LocalSplitCommonTorus`. Declarations in
`Langlands.GroupScheme.splitTorus` and `Langlands.GroupScheme.LocalSplitCell`.

## Setting

`S` is a scheme, and `I`, `I'` are finite types with decidable equality.
`commGroupScheme S I` is the coordinate split torus `T_I` over `S` as a commutative group
scheme, and `splitTorus S I` is the same torus as a group scheme. `exponentCharacter S I m` is the
character `t ↦ ∏ⱼ tⱼ^{mⱼ}`. `exponentHom S I J f` is the torus homomorphism `T_I ⟶ T_J` whose
character pullback is the integral map `f : (J → ℤ) → (I → ℤ)` (Library
`Torus/ExponentHomomorphisms.lean`). `IsFibrewiseMaximalTorus` and `IsFibrewiseRootDatumOf` are
the Library predicates of `Torus/FieldPointMaximality.lean` and
`Reductive/FibrewiseRootDatum.lean`.

## Definitions

- `splitTorus.exponentEquivIso S e : T_I ≅ T_{I'}` for a lattice isomorphism
  `e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)`. Its forward map is `exponentHom S I I' e.symm` and its inverse
  is `exponentHom S I' I e`.
- `LocalSplitCell.precompTorus e i'`: for `i' : T_{I'} ⟶ H` over `Spec R`, the composite
  `T_I ≅ T_{I'} ⟶ H`.
- `LocalSplitCell.exponentEquivGroupIso S e`: the underlying isomorphism of group schemes
  `splitTorus S I ≅ splitTorus S I'`.

## Results

- `splitTorus.congr_exponentEquivIso`: under `characterLattice.congr` of the isomorphism, the
  character with exponent `m` goes to the character with exponent `e m`.
- `splitTorus.baseChange_groupHom_exponentEquivIso`: base change along any `b : S' ⟶ S` turns
  the isomorphism over `S` into the isomorphism over `S'`, up to the canonical identifications
  `splitTorus.baseChangeIso` of the base-changed coordinate tori.
- `baseChangeHom_precompTorus`: for a commutative `R`-algebra `K`, the field-fibre torus map
  `splitTorus.baseChangeHom` of `precompTorus e i'` is the isomorphism over `K` followed by the
  field-fibre torus map of `i'`.
- `isClosedSubgroup_precompTorus`: if `i'` is a closed subgroup, so is `precompTorus e i'`.
- `isFibrewiseMaximalTorus_precompTorus`: if `i'` is maximal on every residue fibre, so is
  `precompTorus e i'`.
- `isFibrewiseRootDatumOf_precompTorus`: let `P` and `Q` be coordinate root data on `I` and `I'`.
  Let `P` be a fibrewise root datum of a torus `i : T_I ⟶ G` of some group `G`, and `Q` a
  fibrewise root datum of `i'`. If `e : P ≃ Q` is a root-datum equivalence, then `P` is a
  fibrewise root datum of `precompTorus e.weightEquiv i'`.

## Proof

`exponentEquivIso` is an isomorphism because `exponentHom` turns composition of integral maps
into composition of torus maps (`exponentHom_comp`, `exponentHom_id`). `congr_exponentEquivIso`
is `exponentHom_comp_exponentCharacter`. `baseChange_groupHom_exponentEquivIso` is the Library's
`exponentHom_baseChange` passed through `CommGroupScheme.groupHom`. `baseChangeHom_precompTorus`
then follows from the definition `baseChangeHom = (baseChangeIso).inv ≫ (base change of the map)`.

Closedness: an isomorphism is a closed subgroup (`IsClosedSubgroup.of_iso`), and closed
subgroups compose. Fibrewise maximality: on each residue fibre, the base change of
`precompTorus e i'` is the base change of `i'` precomposed with a torus isomorphism. The Library's
`IsMaximalTorus.precomp_torusIso` applies.

Root datum: the first two conditions of `IsFibrewiseRootDatumOf` (finiteness, reducedness)
come from the hypothesis on `P`. For each field `K` over `R` we apply the Library's
`IsRootDatumOf.precomp_torusIso` to the torus isomorphism over `K`. Its inputs are four:
- `IsRootDatumOf` of the fibre of `i'` for `fieldRealization K Q`, from the hypothesis on `Q`;
- that the pairing of `fieldRealization K P` is the lattice pairing, from the hypothesis on `P`;
- the equivalence `fieldRealization K P ≃ fieldRealization K Q`, which is
  `fieldRealizationEquiv` composed with `e`;
- the agreement of its weight map with `characterLattice.congr` of the torus isomorphism.
The last one is checked on characters `exponentCharacter m`, which exhaust the character lattice.
Both sides send `exponentCharacter m` to `exponentCharacter (e m)`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. They reduce the
theorem to the case of a common coordinate torus and a common root datum. This is the standard
first step of an Isomorphism Theorem: identify the tori through the given isomorphism of root
data. The proofs combine the Library results named above and follow no particular printed source.
