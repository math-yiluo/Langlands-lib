# Coinvariants, inflation and invariants for a normal subgroup

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.InvariantRestriction`
(`homCoinvariantsEquiv`, `invariantsToCoinvariants`, `invariantsRestriction`,
`invariantsRestrictionEquiv`,
`bijective_invariantsToCoinvariants_compactInduced`) and, through it, on
`Langlands.Representation.Induction.Definitions` (`compactInduced`). From
Mathlib it uses the category `Rep k G` of representations with morphisms
given by intertwining maps (`Rep.ofHom`, `Rep.hom_ext`, `Rep.homLinearEquiv`,
`Rep.mkIso`), the functors `Rep.quotientToCoinvariantsFunctor k S` and
`Rep.quotientToInvariantsFunctor k S` to representations of `G ⧸ S`,
restriction `Rep.resFunctor`, the inclusion
`Representation.quotientToInvariants_lift`, and
`Representation.IntertwiningMap.ofBijective`.

All new names are in the namespace `Langlands.Induction`. `k : Type u` is a
commutative ring, `G : Type v` a group and `S` a normal subgroup of `G`. All
representations have carriers in one universe `w` (`Rep.{w}`).

## Conventions

For a representation `W` of `G ⧸ S`, its inflation is
`(Rep.resFunctor (QuotientGroup.mk' S)).obj W`, the same module with `g ∈ G`
acting as the class of `g`. For a representation `A` of `G`,
`(Rep.quotientToCoinvariantsFunctor k S).obj A` and
`(Rep.quotientToInvariantsFunctor k S).obj A` are Mathlib's representations
of `G ⧸ S` on the `S`-coinvariants and on the `S`-invariants of `A`; their
underlying representations are `Representation.quotientToCoinvariants` and
`Representation.quotientToInvariants` of `A.ρ`, the representations used in
`InvariantRestriction`.

## Adjunctions

- `coinvariantsInflationUnit k S`: the natural transformation from the
  identity to coinvariants followed by inflation whose component at `A` is the
  projection `A ⟶ Inf(A_S)` to the `S`-coinvariants. It is
  `(homCoinvariantsEquiv A.ρ S _).symm` of the identity of the coinvariants.
- `coinvariantsInflationCounit k S`: the natural transformation from
  inflation followed by coinvariants to the identity whose component at `W`
  is the map `(Inf W)_S ⟶ W` induced by the identity of `W`. It is
  `homCoinvariantsEquiv` of the identity of `Inf W`.
- `coinvariantsInflationAdjunction k S`: these are the unit and counit of an
  adjunction `Rep.quotientToCoinvariantsFunctor k S ⊣ Rep.resFunctor
  (QuotientGroup.mk' S)`. Both triangle identities hold on classes of
  vectors and on vectors, respectively, by definition.
- `inflationInvariantsUnit k S`: the natural transformation whose component
  at a representation `W` of `G ⧸ S` is the inclusion of `W` into the
  `S`-invariants of `Inf W`. Every vector of `Inf W` is `S`-invariant, since
  `s ∈ S` acts as the class of `s`, which is `1`.
- `Langlands.Cohomology.quotientInvariantsInclusion k S`: the natural transformation whose component
  at `A` is the inclusion of the `S`-invariants of `A`, inflated to `G`
  (Mathlib's `Representation.quotientToInvariants_lift`). This existing declaration
  is defined here with its original name and generated simp lemmas; the
  cohomological invariants module imports it.
- `inflationInvariantsAdjunction k S`: these are the unit and counit of an
  adjunction `Rep.resFunctor (QuotientGroup.mk' S) ⊣
  Rep.quotientToInvariantsFunctor k S`.
- `invariantsToCoinvariantsNatTrans k S`: the natural transformation
  `Rep.quotientToInvariantsFunctor k S ⟶ Rep.quotientToCoinvariantsFunctor k S`
  whose component at `A` is the published `invariantsToCoinvariants A.ρ S`,
  the inclusion of the invariants followed by the projection to the
  coinvariants.
- `isIso_invariantsToCoinvariantsNatTrans_app A h`: if
  `invariantsToCoinvariants A.ρ S` is bijective (`h`), the component at `A`
  is an isomorphism; its inverse comes from `Rep.mkIso` of
  `Representation.IntertwiningMap.ofBijective`.

Mathlib has the analogous adjunctions `Rep.coinvariantsAdjunction` and
`Rep.invariantsAdjunction` between `Rep k G` and `ModuleCat k`, through the
trivial-representation functor (the analogue of `S = G`). It does not have
them for representations of `G ⧸ S`.

## Restriction of morphisms to invariants

`A` is a representation of `G` and `W` a representation of `G ⧸ S`.

- `homInvariantsRestriction A W`: the `k`-linear map sending a morphism
  `f : A ⟶ Inf W` to its restriction to the `S`-invariants of `A`, a morphism
  `(Rep.quotientToInvariantsFunctor k S).obj A ⟶ W`. It is the published
  `invariantsRestriction A.ρ S W.ρ` transported along `Rep.homLinearEquiv`.
  `homInvariantsRestriction_apply` states its values.
- `homInvariantsRestriction_eq f`: the restriction of `f` is the component of
  `invariantsToCoinvariantsNatTrans k S` at `A` followed by
  `((coinvariantsInflationAdjunction k S).homEquiv A W).symm f`, the morphism
  on coinvariants corresponding to `f`.
- `homInvariantsRestriction_comp_left g f`: for `g : A' ⟶ A`, restricting
  `g ≫ f` is the map induced by `g` on `S`-invariants followed by the
  restriction of `f`.
- `homInvariantsRestriction_comp_right f h`: for `h : W ⟶ W'`, restricting
  `f` followed by the inflation of `h` is the restriction of `f` followed by
  `h`.
- `homInvariantsRestrictionEquiv A W h`: if `invariantsToCoinvariants A.ρ S`
  is bijective (`h`), restriction to the `S`-invariants is a `k`-linear
  equivalence `(A ⟶ Inf W) ≃ₗ[k] ((Rep.quotientToInvariantsFunctor k S).obj
  A ⟶ W)`: the published `invariantsRestrictionEquiv` transported along
  `Rep.homLinearEquiv`. `homInvariantsRestrictionEquiv_apply` states that
  its underlying map is `homInvariantsRestriction`.

## Compact induction of trivial representations

`G` is a topological group, `M : Type uM` a `k`-module, `H` an open subgroup
(`hH`) with `H ≤ S` (`hHS`) and `H` of finite index in `S`.

- `isIso_invariantsToCoinvariantsNatTrans_app_compactInduced hH hHS h`: if
  the index of `H` in `S`, cast to `k`, is a unit (`h`), the component of
  `invariantsToCoinvariantsNatTrans k S` at
  `Rep.of (compactInduced H (Representation.trivial k H M))` is an
  isomorphism, by the published
  `bijective_invariantsToCoinvariants_compactInduced`.

For `S` compact with `p`-group quotients by its open normal subgroups and `p`
a unit of `k`, the published `isUnit_index_subgroupOf` (in
`InvariantRestriction`) provides `h`, and the published
`finiteIndex_subgroupOf_of_isCompact` (in `PermutationInvariants`) the finite
index.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned page): "We may
replace `C^j_m(ẽ)` by `C^j_m(ẽ)^{H_p}` in (4.10.2). Write
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.
To check the Mittag-Leffler condition, we first need to study the maps
(4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)` as `m` varies."

The published `InvariantRestriction` proves the algebra behind the
replacement for spaces of intertwining maps, with the interpretation recorded
there (`G`, `S`, `k` corresponding to `S(ẽ)`, `H_p ∩ S(ẽ)`, `𝒪/ℓ^m𝒪`; this
correspondence is ours). Harris then studies the maps (4.10.3) between the
modules `T_m(j, ẽ)` for different `m`. In our reading these maps are induced
by maps between the modules `C^j_m(ẽ)` and between the coefficients, so
comparing them before and after the replacement needs the replacement to be
natural in both arguments. This module states the replacement for morphisms
in `Rep` together with that naturality. Its application to the maps (4.10.3)
is not carried out here.

The module is derived: the adjunctions between coinvariants, inflation and
invariants are standard, and all definitions and proofs are ours.

## Scope

The module does not construct Harris's modules `C^j_m(ẽ)` or `T_m(j, ẽ)`,
and does not identify the inverse system of the `T_m(j, ẽ)` with an inverse
system of the published `HomSystem`. It works with representations of
abstract groups in `Rep`; smoothness and the categories of smooth
representations are not considered. In general, bijectivity of
`invariantsToCoinvariants` is a hypothesis; it is verified only for compact
inductions of trivial representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
