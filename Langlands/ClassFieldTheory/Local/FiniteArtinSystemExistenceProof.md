# Existence and uniqueness of coherent geometric finite Artin systems

Author: Worker 4966.

The theorem `Langlands.LocalClassField.geometricFiniteArtinSystemExistenceUniqueness`
proves the published proposition
`Langlands.LocalClassField.GeometricFiniteArtinSystemExistenceUniqueness.{u}`
(module `Langlands.ClassFieldTheory.Local.FiniteArtinSystemStatement`). The theorem
keeps every prime `p`, every `F : PadicField.{u} p` in an arbitrary universe, and
every supplied `T : F.TopologicalData` with its topology `T.topology`, and adds no
hypothesis. Existence uses an explicit family; uniqueness is the published
theorem `geometricFiniteArtinSystemUniqueness`. The helper module
`Langlands.ClassFieldTheory.Local.FiniteArtinSymbol` constructs the finite Artin
symbols. Its Markdown describes that construction, a derived formalization of
Serre, *Local Fields*, XI.3, Proposition 2. The helpers below are in the namespace
`Langlands.LocalClassField.FiniteArtinSystemExistence`.

## Unramified bridge

These two lemmas connect the supplied topological data of the target to the
canonical data used by the published arithmetic-coordinate theorems.

- `ramificationIndex_eq_canonical`: the absolute ramification index
  `T.ramificationIndex` of any supplied datum equals the canonical one. Both are the
  order of `p`, and orders agree along the identity by `NYLL.ord_eq_of_algEquiv`.
- `canonical_ramificationIndex_eq`: let `TF` and `TD` be supplied data for `F` and
  an extension `D`, and suppose the maximal ideal of `TD.Integers` has ramification
  index one over `TF.Integers`. Then `F` and `D` have the same canonical absolute
  ramification index. Let `A` be the valuation ring of `Padic p`. The integer rings
  form a tower `A → TF.Integers → TD.Integers`. The extension of integer rings is
  free, as the integral closure of a discrete valuation ring in a finite separable
  extension (`IsIntegralClosure.module_free`; separability comes from
  characteristic zero). It lies over the maximal ideal because the map is local
  (`relativeIntegerMap_isLocalHom`). `Ideal.ramificationIdx_tower` then multiplies
  the indices. The published `ramificationIdx_eq` identifies the absolute indices
  over `A` with `T.ramificationIndex`.
- `supplied_congruence_of_arithmetic`: let
  `χ : Gal(D/F) ≃* Multiplicative (ZMod n)` be an arithmetic unramified coordinate.
  Then for every supplied `TF` and `TD` and every `x` with
  `TD.discreteValuation x ≤ 1`,
  `TD.discreteValuation (χ.symm (ofAdd 1) x - x ^ TF.residueCardinality) < 1`.
  The spectral extension integers equal `TD.Integers`; both are cut out by the
  canonical norm (`ArithmeticCoordinate.spectralNorm_eq_canonicalNorm`,
  `canonicalNorm_le_one_iff_mem_integers`). The residue power law in the definition of an
  arithmetic coordinate is transported along this equality of rings.
  `TF.residueCardinality` is identified with the spectral base residue cardinality
  (`FiniteArtinSystemUniqueness.residueCardinality_eq_canonical`,
  `ArithmeticCoordinate.baseResidueEquiv`). Finally `NYLL.suppliedResidueCongruence`
  converts the residue equality into the valuation inequality.

## The geometric symbol

For a finite abelian extension `D/F.Carrier`, `geometricSymbol F D` is
`(artinSymbol F D).comp invMonoidHom`, so `geometricSymbol F D a = artinSymbol F D a⁻¹`
(`geometricSymbol_apply`). The target's geometric convention inverts arithmetic
reciprocity values, and this definition implements that convention.
`geometricSymbol_symm` states that the inverse automorphism
`(geometricSymbol F D a).symm` is the arithmetic symbol `artinSymbol F D a`.
From `FiniteArtinSymbol` it follows that:

- `ker_geometricSymbol`: the kernel is exactly `normSubgroup F.Carrier D`, because
  the norm subgroup is closed under inverses;
- `geometricSymbol_surjective`: the map is surjective;
- `restrictNormalHom_geometricSymbol`: in a tower `F ⊆ E ⊆ D` of finite abelian
  extensions, restriction to `E` sends `geometricSymbol F D a` to
  `geometricSymbol F E a`.

## Normalization

`geometricArtin F D TD` is `geometricSymbol F D.Carrier` for a p-adic field `D`. It has
exactly the shape of the `Artin` argument of the published
`NYLL.RamifiedGeometricNormalizationTransferStatement`, and the supplied datum `TD`
is not used.

- `unramified_normalization`: suppose `TD.Integers` has relative ramification
  index one over `TF.Integers`. Then the geometric residue congruence holds for every
  `a` with `TF.ord a = 1`. By `canonical_ramificationIndex_eq`, the published
  `ArithmeticCoordinate.coordinate_exists` supplies an arithmetic unramified
  coordinate `χ`. The order of `a` is one also for the canonical datum
  (`NYLL.ord_eq_of_algEquiv`). So `artinSymbol_eq_of_arithmeticCoordinate` makes
  `(geometricArtin F D TD a).symm = artinSymbol F D a` the arithmetic generator
  `χ.symm (ofAdd 1)`. `supplied_congruence_of_arithmetic` concludes.
- `ramified_normalization`: the same congruence holds on every finite abelian
  extension `E` with every supplied `TE`. Apply the published
  `NYLL.ramifiedGeometricNormalizationTransfer` to `geometricArtin F`, with the
  canonical datum on the finite inertia fixed field. Its first hypothesis is
  `unramified_normalization`. Its second hypothesis, restriction from `E` to the
  inertia fixed field, is `restrictNormalHom_geometricSymbol`.

## Continuity

`continuous_geometricArtin`: with `T.topology`, every `geometricArtin F D TD` is
continuous. Its kernel is the norm subgroup. That subgroup is closed by the
published `isClosed_normSubgroup` and has finite index by
`finiteIndex_normSubgroup`, so it is open
(`Subgroup.isOpen_of_isClosed_of_finiteIndex`). A homomorphism into the discrete
finite Galois group with open kernel is continuous at `1`, hence continuous
(`continuous_of_continuousAt_one`).

## The family and the relation

For `L : FiniteAbelianExtension F.Carrier`, `isAbelianGalois_field` records that
`L.field` is abelian over `F.Carrier`. `fieldAlgebra`, `fieldTower` and `fieldAbelian`
transport the algebra, scalar-tower and abelian structures of `L.field` to
`L.asPadicField`, which has the same carrier. `continuous_geometricSymbol_field` is
`continuous_geometricArtin` for this p-adic field.

`geometricFamily F T` is the finite Artin family

```lean
fun L => { toMonoidHom := geometricSymbol F L.field, continuous_toFun := ... }
```

with `geometricFamily_apply` as its defining equation.

`geometricFamily_relation` proves `GeometricFiniteArtinSystemRelation F T
(geometricFamily F T)`:

- the finite norm-residue relation at each `L` is `ker_geometricSymbol` together with
  `geometricSymbol_surjective`;
- compatibility with `L.restrictionOfLE M h` is `restrictNormalHom_geometricSymbol`,
  with the same algebra structure `(Subsemiring.inclusion h).toAlgebra` that
  `restrictionOfLE` uses;
- the geometric normalization for every `L`, every supplied
  `S : (L.asPadicField (p := p)).TopologicalData`, every `b` with `T.ord b = 1`, and
  every `x : L.field` with `S.discreteValuation x ≤ 1` is `ramified_normalization`
  for `E = L.asPadicField`.

## Final theorem

`geometricFiniteArtinSystemExistenceUniqueness` gives `geometricFamily F T` as the
witness, with `geometricFamily_relation`. Any other family `a` that satisfies the
relation equals it by the published `geometricFiniteArtinSystemUniqueness`.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
