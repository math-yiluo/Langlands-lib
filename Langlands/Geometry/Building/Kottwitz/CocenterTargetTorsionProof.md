# Torsion kernel of the cocenter inertia map: proof

Authors: Worker 5310, Worker 5168.

This module proves `CocenterTargetTorsionStatement` with no hypotheses, as the
theorem `cocenterTargetTorsion_proof : CocenterTargetTorsionStatement.{u}`.
This is the torsion-kernel input from the proof of Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023), Lemma 11.5.2, printed p. 431, PDF p. 462. Let
`F` be a nonarchimedean local field, `G` a connected reductive `F`-group and
`c` an actual `Cocenter F G`. Then every element of the kernel of the
constructed map `cocenterTargetMap F F G hG c` lies in the full torsion
subgroup of the multiplicative form of `FundamentalInertia`.

## Route

The module follows the conditional reduction `cocenterTargetTorsion_of_statements`
of `CocenterTargetTorsionReduction`. That theorem assumes
`AlgebraicFundamentalGroupComparisonStatement` and
`AlgebraicFundamentalGroupMapStatement`, but uses them only for morphisms into a
torus, namely into the cocenter torus `D = c.torus`. The module
`TorusTargetFundamentalMap` proves those torus-target cases outright, in the
namespace `Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice`:

- `comparison_self_of_isTorus`: `b.comparison E b = LinearMap.id` for every
  choice `b` of a torus;
- `isInducedMap_mapTo_of_isTorus`: the selected map `a.mapTo E c f` satisfies
  the induced-map law `IsInducedMap` for every morphism `f` into a torus;
- `mapTo_galois_of_isTorus`: that selected map is Galois equivariant.

This module restates the lemmas of the reduction that used the two hypotheses,
with the suffix `_of_isTorus` and without hypotheses. Their proofs are the same
except that the torus-target lemmas replace the hypotheses. The other lemmas of
the reduction module and of `CocenterCocharacterKernel` are used unchanged:
`coinvariants_exists_nsmul_eq_zero`, `torusInertiaComparison_spec`,
`Cocenter.fundamentalCocharacterMap`, `Cocenter.torusCocharacterMap`,
`Cocenter.torusCocharacterMap_surjective` and
`Cocenter.exists_pos_smul_mem_corootImage`.

## Lemmas

- `fundamentalInertiaMap_spec_of_isTorus` proves that for a connected reductive
  `G`, a torus `T` and `f : G ⟶ T`, the selected `fundamentalInertiaMap`
  satisfies its defining law `IsFundamentalInertiaMap`. By
  `mapTo_galois_of_isTorus` for the chosen presentations,
  `fundamentalGroupMap` intertwines the Galois actions. Its map on coinvariants
  (`Representation.Coinvariants.map`) therefore witnesses the law, and
  `Classical.epsilon_spec` transfers it to the selected map.
- `Cocenter.fundamentalCocharacterMap_projection_of_isTorus` proves that on the
  class of a cocharacter `ν` of the chosen maximal torus `T` of `G`, the
  fundamental cocharacter map equals `Cocenter.torusCocharacterMap`, that is,
  `ν` followed by `T → G → D`. Let `b` be the chosen presentation of `D`. Its
  maximal-torus inclusion is an isomorphism by `isIso_of_torus`, so `T → D`
  factors through the torus of `b` over `k`. The base change of this
  factorization is an `IsTorusFactorization`. The induced-map law for it and
  `comparison_self_of_isTorus` compute `mapTo` on the class of `ν`.
  `torusFundamentalComparison_spec` then gives the cocharacter. The field `E`
  here is any extension of `k`.
- `Cocenter.fundamentalCocharacterMap_galois_of_isTorus` proves Galois
  equivariance from `mapTo_galois_of_isTorus` and the published
  `torusFundamentalComparison_galois`.
- `Cocenter.fundamentalCocharacterMap_surjective_of_isTorus` and
  `Cocenter.fundamentalCocharacterMap_torsion_of_isTorus` treat
  `E = SeparableClosure k`. The first proves surjectivity from
  `Cocenter.torusCocharacterMap_surjective` and the projection formula. The
  second proves that every element of the kernel has a positive multiple equal
  to zero. Write the element as the class of `ν`. By the projection formula `ν`
  is killed by the torus cocharacter map, so
  `Cocenter.exists_pos_smul_mem_corootImage` gives `n > 0` with `n • ν` in the
  coroot image, whose class is zero.

## The theorem

`cocenterTargetTorsion_proof` takes `K = UnramifiedClosure F`,
`E = SeparableClosure F` and `y` in the kernel of `cocenterTargetMap F F G hG c`.
That map is `torusInertiaComparison` composed with `fundamentalInertiaMap` for
the cocenter quotient. By `fundamentalInertiaMap_spec_of_isTorus` and
`torusInertiaComparison_spec`, it sends the inertia class of `x ∈ π₁(G)` to the
inertia class of `Cocenter.fundamentalCocharacterMap hG c E x`. The fundamental
cocharacter map is surjective, equivariant for the inertia action and has
torsion kernel. So `coinvariants_exists_nsmul_eq_zero` gives `n > 0` with
`n • y = 0` in additive notation. Hence `y` has finite order in the
multiplicative form, so it lies in the full torsion subgroup.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The lemmas are internal. They follow the cited argument: the surjection with
finite kernel `X_*(T)/X_*(T_sc) → X_*(T)/X_*(T_der) = X_*(G_ab)` stays a
surjection with finite kernel on inertia coinvariants. The theorem proves only
the torsion consequence for the kernel, which is what the statement asks. The
assembly was first written by Worker 5168 as a test against the staged modules
and is used here with new documentation.
