# Transport of the Tits obstruction along pinned isomorphisms and conjugations

This module proves three invariance properties of the Tits obstruction of a simply connected
group (Task 7603, clause 1, last sentence):

1. it is transported along actual isomorphisms of groups with compatible pinnings;
2. it does not depend on the choice of Galois pinning data of a fixed group, up to the
   identification of weights induced by conjugating one split torus onto the other;
3. combining both, it is invariant under every isomorphism of groups over `k`, for arbitrary
   Galois pinning data on source and target.

## Pinned isomorphisms: setting

Fields `k`, `K` with `Algebra k K`. Affine group schemes `G`, `G'` over `Spec k`, locally of
finite type. Galois pinning data `d : GaloisPinningData k K G` and
`d' : GaloisPinningData k K G'`. `f : d.Iso d'` is a pinned isomorphism
(`Reductive/GaloisPinningIso`): a `k`-isomorphism `G ≅ G'` and a `k`-isomorphism of the tori,
compatible with the inclusions, together with a base-preserving equivalence of the root data
over `K` whose weight map `f.weightMap` is the character map of the torus isomorphism. For a
group scheme over `k`, `_K` denotes the actual base change along `Spec K → Spec k`. The
module declares a local instance that this base change of an affine group scheme is affine.

Convention. Throughout, "`ρ` has highest weight `λ` for `d`" means the Library predicate
`d.toSplitPinning.IsHighestWeight ρ λ` (`Rational/FundamentalRepresentations`). It has four
parts: `ρ` is irreducible, the weight spaces of the split torus span the whole space, the
`λ`-weight space has dimension one, and `λ - μ` lies in the positive root monoid for every
weight `μ` with nonzero weight space. Irreducibility is part of the hypothesis. A
representation whose weights merely lie below a multiplicity-one weight `λ` does not satisfy
it.

## Pinned isomorphisms: star-fixed weights

* `Iso.weightMap_mem_starFixedWeights_iff`: `f.weightMap λ ∈ d'.starFixedWeights ↔
  λ ∈ d.starFixedWeights`. This is `Iso.isStarFixedWeight_weightMap_iff` read through
  `mem_starFixedWeights`.
* `Iso.starFixedWeightsEquiv f : d.starFixedWeights ≃+ d'.starFixedWeights` is the restriction
  of `f.weightMap`. `coe_starFixedWeightsEquiv` states that its underlying weight is
  `f.weightMap λ`.

## Pinned isomorphisms: the obstruction

Assume in addition that `K/k` is Galois (`IsGalois k K`), as the obstruction requires.

* `Iso.titsCSAOf_restrict_isBrauerEquivalent`: let `ρ` be an actual matrix representation of
  `G'_K` of size `n` with highest weight `f.weightMap λ` for `d'` (in the sense of
  `IsHighestWeight`, so `ρ` is irreducible), where `λ` is star-fixed for `d` and
  `f.weightMap λ` is star-fixed for `d'`. Its restriction
  `ρ.restrict (baseChangeGroupIso f).hom` to `G_K` has highest weight `λ` for `d`. Then the
  Tits central simple algebras `d.titsCSAOf` of the restriction and `d'.titsCSAOf` of `ρ` are
  Brauer equivalent. Both are subalgebras of `Matrix (Fin n) (Fin n) K` over `k`. The
  restriction is along the base change of the `k`-isomorphism `f.groupIso`, so the two
  subalgebras are equal (`MatrixRepresentation.titsAlgebra_restrict_iso`, applied with the
  Galois intertwiners of `ρ` chosen in `exists_intertwiner_galoisTwist`). The equality gives
  an algebra isomorphism (`Subalgebra.equivOfEq`), hence Brauer equivalence with matrix
  size `1` on both sides.
* `Iso.dominantTitsClass_weightMap`: for a dominant star-fixed weight `λ` of `d`,
  `d'.dominantTitsClass (f.weightMap λ) = d.dominantTitsClass λ`. Proof: choose `ρ` of highest
  weight `f.weightMap λ` for `d'` (`splitHighestWeightClassification`). Its restriction has
  highest weight `λ` for `d` (`Iso.isHighestWeight_restrict_iff`). Then
  `dominantTitsClass_eq` and the previous lemma give the equality.
* `Iso.titsObstruction_starFixedWeightsEquiv`: for `IsSimplyConnected G`,
  `IsSimplyConnected G'` and `λ ∈ d.starFixedWeights`,

  `d'.titsObstruction hG' (f.starFixedWeightsEquiv λ) = d.titsObstruction hG λ`.

  Proof: write `λ = a - (a - λ)` with `a = d.dominantPart λ`. Both `a` and `a - λ` are
  dominant and star-fixed for `d`. Their images under `f.weightMap` are dominant and
  star-fixed for `d'` (`Iso.isDominantWeight_weightMap_iff`,
  `Iso.isStarFixedWeight_weightMap_iff`), and `f.weightMap λ` is the difference of the images.
  `titsObstruction_eq_sub` for `d` and for `d'` expresses both sides as differences of
  dominant Tits classes, and `Iso.dominantTitsClass_weightMap` identifies them term by term.
* `Iso.titsObstruction_comp_starFixedWeightsEquiv`: the same identity of additive maps,
  `(d'.titsObstruction hG').comp f.starFixedWeightsEquiv = d.titsObstruction hG`.

The obstruction `titsObstruction`, `dominantTitsClass`, `titsCSAOf`, `dominantPart` and
`titsObstruction_eq_sub` are the Library's constructions from Worker 90's part of the same
task (`Reductive/TitsObstructionSimplyConnected`, `Reductive/TitsObstruction`,
`Reductive/TitsDominantClass`); `titsAlgebra_restrict_iso` is in
`Reductive/TitsAlgebraTransport`.

## Matrix lemma (namespace `MatrixRepresentation`)

* `intertwines_restrict_innerIso`: for a field `F`, an affine group scheme `H` over `Spec F`,
  an actual matrix representation `ρ` of `H` and an `F`-point `g` of `H`, the matrix
  `ρ.rationalMatrix g` of `g` intertwines `ρ` with its restriction
  `ρ.restrict (H.innerIso g).hom` along the inner automorphism by `g`. This is the identity
  `ρ(g) ρ(x) = ρ(g x g⁻¹) ρ(g)`. It is checked at the universal point
  (`intertwines_iff_universal_pointMatrix`), using the Library's `comp_innerIso_hom`
  (the inner automorphism is `x ↦ c x c⁻¹` for the constant point `c` of `g`) and
  `pointMatrix_constantPoint`.

## Independence of the Galois pinning data (namespace `GaloisPinningData`)

Now `G` is a single affine group scheme over `Spec k`, and `d`, `d'` are two Galois pinning
data of `G` with the same field `K`.

`GaloisPinningData.Conj d d'` (a pinned conjugation) is a structure with fields:

* `point`, a `K`-point `g` of `G_K`;
* `torusIso : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus`, an isomorphism of the split
  tori over `K`;
* `square`: the inner automorphism by `g` carries the inclusion of the torus of `d` to that of
  `d'` through `torusIso`;
* `rootDatumEquiv`, an equivalence of the root data;
* `weightMap_eq`: its weight map is `characterLattice.congr torusIso`;
* `base_iff`: its index bijection maps the simple indices of `d` exactly onto those of `d'`.

Results, for `f : d.Conj d'`:

* `Conj.nonempty`: for `G` locally of finite type, any two Galois pinning data of `G` admit a
  pinned conjugation. This is the Library's `StarActionIndependence.starActionIndependence`
  (rational conjugacy of split maximal tori over `K` followed by a Weyl correction of the
  base).
* `Conj.weightMap f : X^*(T_K) ≃ₗ[ℤ] X^*(T'_K)`, with `weightMap_apply`.
* `Conj.isDominantWeight_weightMap_iff` and `Conj.isHighestWeight_restrict_iff`: dominance
  corresponds, and `ρ.restrict (innerIso f.point).hom` has highest weight `λ` for `d` exactly
  when `ρ` has highest weight `f.weightMap λ` for `d'`. Both come from the generic
  `SplitPinning` lemmas of `Reductive/GaloisPinningIso` with the group isomorphism
  `innerIso f.point`.
* `Conj.rootDatumEquiv_comp_starAction`, `Conj.starAction_weightMap`: `f.weightMap` intertwines
  the star actions of `d` and `d'`. This is the Library's
  `StarActionIndependence.starAction_intertwine`.
* `Conj.isStarFixedWeight_weightMap_iff`, `Conj.weightMap_mem_starFixedWeights_iff`,
  `Conj.starFixedWeightsEquiv f : d.starFixedWeights ≃+ d'.starFixedWeights` and
  `Conj.coe_starFixedWeightsEquiv`, as for pinned isomorphisms.

With `K/k` Galois:

* `Conj.titsCSAOf_restrict_isBrauerEquivalent`: for `ρ` of highest weight `f.weightMap λ` for
  `d'` (`IsHighestWeight`, including irreducibility) and its restriction along `innerIso f.point` (highest weight `λ` for `d`), the Tits
  central simple algebras are Brauer equivalent. The invertible matrix `C = ρ(g)` intertwines
  the two representations (`intertwines_restrict_innerIso`). Conjugation by `C` is then an
  isomorphism of `k`-algebras between their Tits algebras (Worker 90's
  `titsAlgebraEquivOfIntertwines`). This gives Brauer equivalence with matrix size `1` on
  both sides.
* `Conj.dominantTitsClass_weightMap`: `d'.dominantTitsClass (f.weightMap λ) =
  d.dominantTitsClass λ` for dominant star-fixed `λ`, by the same argument as for pinned
  isomorphisms.
* `Conj.titsObstruction_starFixedWeightsEquiv`: for `IsSimplyConnected G` and
  `λ ∈ d.starFixedWeights`,
  `d'.titsObstruction hG (f.starFixedWeightsEquiv λ) = d.titsObstruction hG λ`. The proof is
  the same decomposition `λ = dominantPart λ - (dominantPart λ - λ)` as above.
  `Conj.titsObstruction_comp_starFixedWeightsEquiv` is the same identity of additive maps.
* `exists_starFixedWeightsEquiv_titsObstruction`: for `G` locally of finite type and simply
  connected, and any two Galois pinning data `d`, `d'`, there is a pinned conjugation `f`
  with `(d'.titsObstruction hG).comp f.starFixedWeightsEquiv = d.titsObstruction hG`.

## Isomorphism invariance

Let `e : G ≅ G'` be an isomorphism over `k` of affine group schemes locally of finite type, both
simply connected, and let `K/k` be Galois. `Reductive/GaloisPinningTransport` provides the
transported data `d.transport e` of `G'` and the pinned isomorphism `d.transportIso e`.

* `titsObstruction_transport_conj`: for Galois pinning data `d` of `G` and `d'` of `G'`, a
  pinned conjugation `f : (d.transport e).Conj d'` and `λ ∈ d.starFixedWeights`,
  `d'.titsObstruction hG' (f.starFixedWeightsEquiv ((d.transportIso e).starFixedWeightsEquiv λ))
  = d.titsObstruction hG λ`. Proof: `Conj.titsObstruction_starFixedWeightsEquiv` followed by
  `Iso.titsObstruction_starFixedWeightsEquiv`.
* `exists_starFixedWeightsEquiv_titsObstruction_of_iso`: for any `d` of `G` and `d'` of `G'`
  there is an isomorphism `φ : d.starFixedWeights ≃+ d'.starFixedWeights` with
  `(d'.titsObstruction hG').comp φ = d.titsObstruction hG`. Here `φ` is the composite above,
  with `f` given by `Conj.nonempty`.

## Provenance

Internal. Clause 1 of Task 7603 requires independence of auxiliary choices and transport of
the obstruction along actual group isomorphisms and compatible pinning isomorphisms. The
pinned conjugations cover the choice of Galois pinning data for a fixed group, and together
with the transported pinning data they give invariance under every `k`-isomorphism. The proofs
combine the transport lemmas for pinned isomorphisms, the Library's star-action independence
and the independence of the decomposition into dominant weights. No literature statement is
formalized here.
