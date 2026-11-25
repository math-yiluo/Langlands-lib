# Universality of Weyl conjugation from partner uniqueness and inverse rescaling

This module imports `LocalSplitWeylChains`. It states two rank-one properties of reductive
groups over local rings as propositions. It proves that together they imply the published
`LocalSplitWeylConjugationStatement` (module `LocalSplitWeylConjugationStatement`).

## Statements

Setting of both statements: a commutative local ring `R`, a reductive group scheme `G` over
`Spec R` with affine structure morphism, a closed coordinate split torus
`i : T_I → G` that is maximal on every residue-field fibre, and a fibrewise root datum
`P : RootDatum J (I → ℤ) (I → ℤ)` of `(G, i)`.

- `LocalSplitPartnerUniqueStatement.{u}`: in this setting `PartnerUnique P G i` holds. That
  is, for every root `a`, every parametrization `xp` of `a`, and parametrizations `xm`, `xm'` of
  `-a` such that `weylPoint xp xm` and `weylPoint xp xm'` are both Weyl points acting by `s_a`,
  we have `xm' = xm`.
- `LocalSplitPartnerRescalesStatement.{u}`: in this setting `PartnerRescales P G i` holds. That
  is, for every root `a`, parametrizations `xp` of `a` and `xm` of `-a` with `weylPoint xp xm` a
  Weyl point acting by `s_a`, and every unit `κ` of `R`, the point
  `weylPoint (κ ≫ xp) (κ⁻¹ ≫ xm)` is again a Weyl point acting by `s_a`. Here
  `κ ≫ xp = scaleHom κ ≫ xp`.
- `LocalSplitWeylConjugationReductionStatement.{u}` is the implication
  `LocalSplitPartnerUniqueStatement.{u} → LocalSplitPartnerRescalesStatement.{u} →
  LocalSplitWeylConjugationStatement.{u}`.

## Results

- `localSplitWeylConjugation_of_partner` proves the implication. It assembles the hypotheses
  of `LocalSplitWeylConjugationStatement` for `G` and for `H` into `IsNormalSimpleData` (module
  `LocalSplitWeylCommutatorReduction`) and applies `weylConjugationRelations_of_partner`.
- `localSplitWeylConjugationReduction : LocalSplitWeylConjugationReductionStatement.{u}` is the
  same proof.

The two assumed statements are not proved here. Their content matches the theorems
`rootPartner_unique` and `isWeylPoint_rescale` of the modules
`LocalSplitRootPairUniqueness` and `LocalSplitRootPairRescaling`. Those modules are not
imported here, and the Isomorphism Theorem is not proved in this module.

## Provenance

`LocalSplitWeylConjugationStatement` is the universality of the action of the simple Weyl
points on root groups. It replaces, for two groups without a homomorphism between them, the
compatibility of an isomorphism with Weyl conjugation in SGA 3, Exp. XXIII, §2 (proof of the
Isomorphism Theorem). The two rank-one inputs are rank-one facts in the spirit of SGA 3, Exp. XX (groups of
semisimple rank one: the Weyl element built from opposite root parameters and its behaviour
under the torus). The derivation of universality from them is
internal; see `LocalSplitWeylBraid` and `LocalSplitWeylChains`.
