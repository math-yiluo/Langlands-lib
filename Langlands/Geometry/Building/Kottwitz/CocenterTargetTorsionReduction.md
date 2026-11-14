# Torsion kernel of the cocenter inertia map, from the fundamental-group statements

This module is an internal reduction for `CocenterTargetTorsionStatement`, the
torsion-kernel input from the proof of Kaletha–Prasad, *Bruhat–Tits theory: a
new approach* (2023), Lemma 11.5.2, printed p. 431, PDF p. 462. Its final theorem
`cocenterTargetTorsion_of_statements` proves that statement from two
published propositions about algebraic fundamental groups, which it takes as
hypotheses:

- `hcmp : AlgebraicFundamentalGroupComparisonStatement`, of which only the
  identity law `a.comparison E a = LinearMap.id` is used;
- `hfund : AlgebraicFundamentalGroupMapStatement`, of which only two clauses
  are used. The selected map `a.mapTo E c f` satisfies the induced-map law
  `IsInducedMap`, and it is Galois equivariant.

Thus this module does not prove `CocenterTargetTorsionStatement`
unconditionally. Once proofs of the two statements are in the Library, applying
`cocenterTargetTorsion_of_statements` to them proves the target. Neither
hypothesis is weakened or replaced by a property of the selected inertia maps.
The defining laws of `fundamentalInertiaMap` and `torusInertiaComparison` are
derived here rather than assumed.

## Coinvariants

For an integral linear map `ψ : V → W` between `ℤ`-representations of a monoid
`Γ` that intertwines the actions:

- `coinvariantsKer_le_map` proves that if `ψ` is surjective, the coinvariant
  kernel of `W`, spanned by the elements `g • w - w`, is the image under `ψ` of a
  submodule of the coinvariant kernel of `V`. Each generator `g • ψ v - ψ v` is
  the image of `g • v - v`.
- `coinvariants_exists_nsmul_eq_zero` proves that if `ψ` is in addition such
  that every element of its kernel has a positive multiple equal to zero, then
  every linear map `φ` on coinvariants with `φ [v] = [ψ v]` has the same
  property. If `φ [x] = 0`, then `ψ x = ψ w` for some `w` in the coinvariant
  kernel of `V`. So `n • (x - w) = 0` for some `n > 0`, and `n • [x] = n • [w] = 0`.

## The selected inertia maps

`fundamentalInertiaMap_spec_of_statement` proves, from `hfund`, that
`fundamentalInertiaMap` satisfies its defining law `IsFundamentalInertiaMap` for
every morphism `f` of connected reductive groups. The equivariance clause of
`hfund` for the chosen presentations makes `fundamentalGroupMap k E H G hH hG f`
an intertwining map. Its map on coinvariants (`Representation.Coinvariants.map`)
is then a witness of the law, so `Classical.epsilon_spec` shows that the
selected map satisfies it. `torusInertiaComparison_spec` proves the law
`IsTorusInertiaComparison` for the torus inertia comparison in the same way. It
uses the Galois equivariance clause of the published
`torusFundamentalComparison_proof` and needs no hypothesis.

## The fundamental cocharacter map

For a connected reductive `G`, an actual `Cocenter k G` with torus `D` and
quotient `q`, and a field extension `E/k`, the definition
`Cocenter.fundamentalCocharacterMap hG c E` is the composite
`π₁(G) → π₁(D) → X_*(D)`. Its first map is `fundamentalGroupMap` for `q`, and its
second is the selected comparison `torusFundamentalComparison`. For `E` a
separable closure, the following hold.

- `Cocenter.fundamentalCocharacterMap_projection` (from `hcmp` and `hfund`)
  proves that on the class of a cocharacter `ν` of the chosen maximal torus `T`
  of `G`, the map equals `Cocenter.torusCocharacterMap c a E ν`, that is, `ν`
  followed by `T → G → D`. The chosen presentation `b` of `D` has an isomorphism
  `T_b → D` as its maximal-torus inclusion, by `isIso_of_torus`. So `T → D`
  factors through `T_b` over `k`, and the base change of that factorization is
  an `IsTorusFactorization`. The induced-map law of `hfund` for this
  factorization, the identity law `b.comparison E b = id` of `hcmp`, and the
  cocharacter law of `torusFundamentalComparison_proof` give the formula.
- `Cocenter.fundamentalCocharacterMap_galois` (from `hfund`) proves Galois
  equivariance from the equivariance clauses of `hfund` and of
  `torusFundamentalComparison_proof`.

For `E = SeparableClosure k`, the following hold.

- `Cocenter.fundamentalCocharacterMap_surjective` proves surjectivity from
  `Cocenter.torusCocharacterMap_surjective` (module
  `CocenterCocharacterKernel`) and the projection formula.
- `Cocenter.fundamentalCocharacterMap_torsion` proves that every element of the
  kernel has a positive multiple equal to zero. Write the element as the class
  of `ν`. By the projection formula `ν` is killed by the torus cocharacter map,
  so `Cocenter.exists_pos_smul_mem_corootImage` gives `n > 0` with
  `n • ν` in the coroot image, whose class is zero.

## The torsion kernel

`cocenterTargetTorsion_of_statements hcmp hfund` proves
`CocenterTargetTorsionStatement`. Let `F` be a nonarchimedean local field, with
`K = UnramifiedClosure F` and `E = SeparableClosure F`, and let `y` be in the
kernel of `cocenterTargetMap F F G hG c`. That map is
`torusInertiaComparison` composed with `fundamentalInertiaMap` for `q`. By the
two selection laws above, it sends the inertia class of `x ∈ π₁(G)` to the
inertia class of `Cocenter.fundamentalCocharacterMap hG c E x`. The coinvariant
lemma applies to the surjective, equivariant fundamental cocharacter map with
torsion kernel, for the action of the inertia subgroup, and gives `n > 0` with
`n • y = 0`. Thus `y` lies in `fundamentalInertiaTorsion`, the full torsion
subgroup of the multiplicative form of `FundamentalInertia`.

## Provenance

`Cocenter.fundamentalCocharacterMap` is an internal definition, the composite of
the published `fundamentalGroupMap` and `torusFundamentalComparison`. It models
the map `X_*(T)/X_*(T_sc) → X_*(G_ab)` of the cited proof on the presentation-free
algebraic fundamental group. The lemmas follow the cited argument, a surjection
with finite kernel that remains so on inertia coinvariants. Only its torsion
consequence is proved: the kernel is shown to be torsion, not finite, and no
surjectivity on coinvariants is stated.
