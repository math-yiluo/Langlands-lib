# Weak Néron models from smoothenings

The module `Langlands.AbelianScheme.WeakNeronModelExistenceReduction` states and proves
that the existence of smoothenings over discrete valuation rings gives weak Néron models
of abelian varieties.

## `WeakNeronModelExistenceReductionStatement`

The proposition is the implication

`DvrSmootheningStatement.{u} → WeakNeronModelExistenceStatement.{u}`.

- `Langlands.AlgebraicGeometry.DvrSmootheningStatement` asserts that every scheme of
  finite type over a discrete valuation ring `R` with smooth generic fibre has a proper
  morphism `g : X' ⟶ X`, an isomorphism on generic fibres, through which every point
  with values in an extension of ramification index one lifts to a point of an open of
  `X'` smooth over `R`.
- `Langlands.AbelianScheme.WeakNeronModelExistenceStatement` asserts that every abelian
  variety `B` over the fraction field `K` of a discrete valuation ring `V` has a smooth,
  separated `V`-scheme `W` of finite type, with generic fibre isomorphic to `B` over `K`,
  that has the weak Néron mapping property
  `Langlands.AbelianScheme.WeakNeronMappingProperty`.

## Source and provenance

Bosch, Lütkebohmert and Raynaud, *Néron Models* (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`):

- §1.3, proof of Corollary 2 (printed pp. 16–17): take a proper flat model of the abelian
  variety, apply the smoothening process, and take the smooth locus;
- §3.1, Corollary 4 and the remark after it (printed pp. 61–62): removing the non-smooth
  locus of a smoothening of `X` gives a smooth `R`-scheme of finite type with the same
  `R^sh`-valued points as `X`; for the schematic closure of a projective abelian variety
  this is a smooth model of it;
- §3.5, the paragraph before Definition 1 and Theorem 2 (printed p. 74): applied to a
  separated model whose `R^sh`-points are the `K^sh`-points of the generic fibre, such as
  a proper model, Corollary 3.1/4 gives a weak Néron model consisting of a single model;
- §3.5, Proposition 3 and its proof (printed pp. 74–75): the weak Néron property of a
  weak Néron model that is already given. For a smooth `R`-scheme `Z` with irreducible
  special fibre, every `K`-rational map from `Z_K` extends to an `R`-rational map into one
  of its members;
- §3.6, Definition 1 and the remark after it (printed p. 78): extensions of ramification
  index one, among them the local rings of smooth `R`-schemes at generic points of their
  special fibres; Lemma 5 (printed p. 79): smoothenings lift points with values in such
  extensions.

The implication is derived from these results. The smooth locus of a smoothening of an
arbitrary model of finite type need not be a weak Néron model of its generic fibre. For
example, the identity of the affine line over `R` is a smoothening, and its smooth locus
is the whole affine line, but the `K`-point with coordinate `π⁻¹` (for a uniformizer `π`)
does not extend to an `R`-point. The proper initial model supplies these extensions. The Lean proof
does not pass through the `R^sh`-point formulation of weak Néron models or through
Proposition 3. It proves the single-model weak Néron mapping property of the Library
directly from the properness of the initial model and the index-one lifting of §3.6,
Lemma 5. Over the local ring of a smooth test scheme at a generic point of its special
fibre, the valuative criterion of properness extends the generic-fibre morphism into the
proper model. Lemma 5 lifts the extension into the smooth locus, and the local extensions
spread out to opens and glue.

## Proof as implemented

`weakNeronModelExistenceReduction` proves the proposition. Given the smoothening
statement `hS`, a discrete valuation ring `V` with fraction field `K`, and an abelian
variety `B` over `K`:

1. `Langlands.AbelianScheme.properDvrModel` gives a proper flat `V`-scheme `X` with
   structure morphism `f` whose generic fibre is `B` (an `IsPullback` square along
   `Spec K ⟶ Spec V`). The generic fibre `pullback.snd f (Spec K ⟶ Spec V)` is
   isomorphic to the structure morphism of `B`, hence smooth.
2. `hS` gives a proper `g : X' ⟶ X`, an isomorphism on generic fibres, with the lifting
   property. Let `W` be the smooth locus of `F = g ≫ f` (Mathlib's
   `Scheme.Hom.smoothLocus`, an open of `X'`), `w : W ⟶ Spec V` the restriction of `F`
   and `h : W ⟶ X` the restriction of `g`.
3. The morphism `w` is smooth (`Scheme.Hom.preimage_smoothLocus_eq` and
   `Scheme.Hom.smoothLocus_eq_top_iff`), separated, locally of finite type, and
   quasi-compact because `X'` is locally noetherian. An open of `X'` smooth over `V`
   lies in `W`.
4. The generic fibre of `X'` is an open of `X'` smooth over `V`. It is isomorphic to the
   smooth generic fibre of `X`, and `Spec K ⟶ Spec V` is an open immersion. So it lies in
   `W`. Hence the generic fibre of `W` maps isomorphically onto that of `X'` (an explicit
   inverse is built with `IsOpenImmersion.lift`), and `h` is an isomorphism on generic
   fibres.
5. `h` has `WeakNeronLifting.RamificationIndexOneLifting`: a lift given by `hS` lands in
   an open smooth over `V`, which lies in `W` by step 3.
6. `WeakNeronLifting.weakNeronMappingProperty_of_lifting` gives the weak Néron mapping
   property of `w`. The isomorphism of `B` with the generic fibre of `W` over `K` is the
   `IsPullback` isomorphism of step 1 composed with the inverse of the generic-fibre
   isomorphism of `h`.
