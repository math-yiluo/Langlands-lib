# Actual lower semistandard geometry for the weighted weak expansion

This module implements the lower groups of Waldspurger V.1 in the actual group
scheme `M' = Standard.leviScheme i ν I'`. All declarations are in
`Langlands.HarishChandraSchwartz.WeakExpansion`. They use the lower subgroup
functors from `RationalWeakExpansionWeyl`, rather than replace the parabolic
by standard data in `M'`.

## Source and scope

The source is Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
V.1, printed pp.288–289, places the lower coefficient space on `M'` with
parabolic “M′∩s·P” and inducing representation `sω`. The weak packet step of
VI.3.1, printed p.304, uses precisely this lower coefficient space and calls
`sO` “l'orbite de sω”. Thus its ambient group is `M'`, while its inducing
Levi is the forward conjugate `sM`; the parabolic is in general semistandard.
These formulas motivate the new constructions below. The cocharacter
implementation and its topology adapters are derived from published Library
constructions, rather than additional analytic assertions from the source.

This module concerns geometry only. It defines no representations, characters,
orbit measures, densities or c-families. In particular it states or proves
neither V.1.1, V.2.3 nor VI.3.1. Their regularity, expansion and finite
decomposition targets are stated in `RationalWeakExpansionTargets`.

## Cocharacters and actual subgroup functors

Fix a field `F`, an affine group scheme `G`, a maximal split torus `i : T → G`,
a generic cocharacter `ν`, and standard root index sets `I,I'`. For dynamic
agreement, the hypotheses are connected reductivity of `G`, maximal splitness,
genericity of `ν` and `I ⊆ simpleRelativeRoots i ν`.
Choose `ζ` with `hζ : IsStandardCocharacter i ν I ζ`, and an actual rational
normalizer point `n`.

- `conjugatedCocharacter i ζ n` is the action of `normalizingAut i n` on `ζ`.
- `lowerCocharacter i ν I' ζ n` composes this cocharacter with
  `Standard.leviTorusHom i ν I'`.
- `lowerCocharacter_comp` identifies its ambient composite with
  `(groupHom ζ ≫ i) ≫ Int(n).hom`. This fixes the forward conjugation direction.
- `conjugatedCocharacter_dynamic` identifies its ambient dynamic parabolic,
  centralizer and unipotent functors with `nPn⁻¹`, `nMn⁻¹` and `nUn⁻¹`.
- `lowerCocharacter_dynamic` identifies the lower dynamic triple with
  `lowerParabolic`, `lowerLevi` and `lowerUnipotent`, on every test scheme.
  These are the pullbacks of the conjugated functors along the closed embedding
  `j' : M' → G`, hence the actual intersections inside `M'`.
- `lowerCocharacter_points` specializes the parabolic and Levi equalities to
  the literal rational-point subgroups of
  `DynamicOppositeStandardIntertwining`, the groups used by the dynamic
  coefficient and wave packet constructions.

The ambient dynamic agreement applies the published standard-cocharacter
theorem and dynamic functoriality for the inverse inner isomorphism. The lower
agreement then applies dynamic functoriality for the closed subgroup `j'`.
The morphism equality uses the published `groupHom_cocharacterAut_comp` and
`Standard.leviTorusHom_comp`. No extra agreement premise is assumed.

`lowerDecompositionModel` reindexes `Dynamic.affineDecompositionModel` by these
three proved equalities. It gives closed affine representatives, compatible
inclusions and a Levi decomposition for the actual intersection functors.
`lowerSemistandardIndex` additionally requires `I' ⊆ simpleRelativeRoots i ν`
and packages the same triple as a `SemistandardSpectralIndex` of the fixed
torus in `M'`. The torus containment is proved through its torus centralizer;
the structural parabolic, connected reductive Levi and geometric radical
clauses come from the published `SemistandardSpectralIndex.ofCocharacter` and
connected reductivity of the actual standard Levi scheme.

These constructions retain the explicit choices `ζ,n`. Their dynamic
equalities show that, for a fixed `n`, the resulting subgroup functors do not
depend on which standard cocharacter `ζ` realizes `I`. Admissibility of `n`
is needed for the next identification with the whole conjugated inducing Levi.

## Conjugation on canonical rational-point groups

Assume `F` is a topological field whose ring operations are continuous, and
`G` is locally of finite type. The rational-point topologies are the canonical
evaluation topologies; subgroup types carry their inherited topologies.
Let
`hn : conjugatedLevi i ν I n ≤ standardLevi i ν I'`
be the all-test inclusion supplied, for example, by `Representatives.levi_le`.
Then

```text
lowerLeviConjugation i ν I I' hG hi hν hI ζ hζ n hn :
  standardLeviPoints i ν I ≃ₜ*
    (Dynamic.centralizer (lowerCocharacter i ν I' ζ n)).rationalPoints
```

is a topological group isomorphism. Its target is definitionally the literal
`DynamicOppositeStandardIntertwining.levi` of the lower cocharacter.
If `e` denotes this map, `map_lowerLeviConjugation` proves

```text
j'(e(m)) = n * m * n⁻¹.
```

`lowerLeviConjugation_symm_coe` proves the inverse formula

```text
e⁻¹(m') = n⁻¹ * j'(m') * n
```

in `G(F)`. Thus a later definition of `sπ` can pull the original smooth
representation back along `e⁻¹` on the actual lower inducing group.

The construction uses the published `standardLeviRationalPointsHomeomorph`
for `M'` and `rationalPointsConjHomeomorph` in `G(F)`. The inclusion `hn`
puts the conjugated source points in `M'`; the proved dynamic equality
identifies its target subgroup. The inverse and multiplication laws follow
by the injectivity of the represented Levi point map and the conjugation
identities. Both continuity statements follow by restricting these existing
homeomorphisms to the indicated subgroups.

No transport to a standard parabolic of `M'` occurs. In particular the
normalized c-operator of V.3.1 is not used here, and no character or measure
compatibility is inferred from this group homeomorphism. Such compatibility
must be supplied by the later orbit and source-measure constructions and
agreement targets. The field characteristic is unrestricted. This module has
no representation-carrier parameter and makes no identification of field and
representation universes.
