# Reduction of the smooth relation quotient theorem

This module proves `SmoothRelationQuotientStatement.{u}` from four prerequisite
propositions. It is a conditional theorem: the final proof of the target applies it
to proofs of the four prerequisites. It is internal to this project; no
literature statement is formalized here. The route follows the smooth case of
Stacks Theorem 80.10.1 (tag 04S6) and Section 80.12 (tag 076L): slice the smooth
relation to an etale one, take the etale quotient, and compare it with the
canonical quotient.

- **P1** `MonomorphismLocallyFiniteTypeSchemeStatement` (Stacks 0463, 03XX; proof
  task `eb482288`). It is used through the Library pair adapter
  `MonomorphismPairScheme.isRepresentedByScheme_of_injective_pair` (Worker 303). The
  adapter says: an algebraic space `R` is represented by a scheme if its endpoint
  maps `s t` to `U` are jointly injective on sections and it has an etale
  surjective atlas on which `s` is induced by a morphism locally of finite type.
- **P2** `SmoothEquivalenceRelationEtaleSliceStatement` (Stacks 04S6 slicing step;
  proof task `3c6168ac`).
- **P4** `SmoothEtaleSourceDescentStatement` (smoothness is etale local on the
  source). Its proof `smoothEtaleSourceDescent` is in the Library.
- **D3** `EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement` (Stacks 02WW).
  Its proof `etaleEquivalenceRelationAlgebraicSpaceQuotient` is in the Library.

This module takes all four as hypotheses and imports none of their proofs.

## The definition `Prerequisites`

`SmoothRelationQuotient.Prerequisites.{u}` is the proposition
`P1 ∧ P2 ∧ P4 ∧ D3`, the conjunction of the four statements above in universe `u`.
It names the hypothesis bundle of the reduction. The theorem
`smoothRelationQuotientStatement_of_prerequisites` derives
`SmoothRelationQuotientStatement.{u}` from it by applying
`smoothRelationQuotientStatement_of` to the four components.

## Helper lemmas

`relative_of_isEtale_isSurjective`: let `P` be a property of scheme morphisms that
is stable under base change and descends along surjective, flat, locally finitely
presented morphisms. Let `f : F ⟶ G` be a representable map of presheaves. Assume
there is a surjective etale map `A` from a scheme `W` to `G` and a represented
pullback square of `f` along `A` whose projection `p₀ : V₀ ⟶ W` has `P`. Then every
represented base change of `f` has `P`. Proof: for a map `g` from a scheme `T`,
base change `A` along `g` to get a surjective etale `pT : T' ⟶ T` and
`fT : T' ⟶ W`. Form the pullback `V'` of the given projection `p : V ⟶ T` along
`pT` in `Over S`. Pasting the three squares shows that `V' ⟶ T'` is a base change
of `p₀` along `fT`, so it has `P` (Mathlib `relative_map`). Fppf descent along `pT`
then gives `P` for `p`.

`app_eq_iff_of_isPullback`: in a kernel-pair square of presheaves with represented
corners, two points have the same image exactly when an arrow joins them.

## The reduction `smoothRelationQuotientStatement_of`

Fix `S`, `U`, `R`, `s`, `t`, the relation witness `h`, an etale atlas `b` of `R`
with smooth endpoint composites `s₀ t₀`, and `U` locally of finite type over `S`.
Write `q` for `quotientMap R s t h`.

1. *`R` is a scheme.* P1, through the pair adapter (injectivity from `h`, atlas
   `b`, `s₀` smooth hence locally of finite type), gives `R₀` with
   `eR : yoneda R₀ ≅ R.presheaf`. Let
   `s₁ t₁ : R₀ ⟶ U` be the preimages of `eR.hom ≫ s` and `eR.hom ≫ t`. The kernel
   pair `isPullback_quotientMap` (SmoothRelationQuotientComparison) transports to
   `IsPullback (Y s₁) (Y t₁) q q`.
2. *`s₁` and `t₁` are smooth.* The atlas gives `e : W ⟶ R₀`, etale and surjective,
   with `e ≫ s₁ = s₀` and `e ≫ t₁ = t₀`. P4 applies. `AtlasRelation.isEquivRel_of_isPullback`
   turns the kernel pair into `IsEquivRel s₁.left t₁.left`.
3. *Slice.* P2, applied with `t := s₁.left` and `s := t₁.left`, gives `g : U'₀ ⟶ U.left`
   locally of finite type with `h = pullback.snd g s₁.left ≫ t₁.left` etale and
   surjective. Set `U' = Over.mk (g ≫ U.hom)` and `gO = Over.homMk g`. Let
   `X = pullback gO s₁` in `Over S`, with projections `prU'` and `ρ`, and let
   `hO = ρ ≫ t₁`. Up to the canonical isomorphism of pullbacks, `hO.left` is `h`,
   so it is etale and surjective.
4. *Restricted relation.* Let `R' = pullback hO gO` with projections `fX` and `sO`,
   and let `tO = fX ≫ prU'`. Pasting the yoneda images of the two pullback squares
   with the kernel pair of `q` gives `IsPullback (Y prU') (Y hO) (Y gO ≫ q) q`.
   Pasting again gives `IsPullback (Y tO) (Y sO) (Y gO ≫ q) (Y gO ≫ q)`. So `R'` is the
   kernel pair of `Y gO ≫ q`. Then `sO` is etale as a base change of `hO`, and
   `tO` is etale because the swap of the equivalence relation `R'` is an
   involution exchanging `tO` and `sO`. `EtaleEquivalenceRelation.ofKernelPair`
   (EtaleEquivalenceRelationPresentation) builds the etale equivalence relation
   `E` on `U'.left`.
5. *Quotient and comparison.* D3, applied to `E` and `U'.hom`, gives an algebraic
   space `Q'` and an etale surjective `a : yoneda U' ⟶ Q'.presheaf` with kernel
   pair `E`. Both `a` and `Y gO ≫ q` are etale locally surjective. For `a` this is
   `isLocallySurjective_etale_of_isEtale_isSurjective`. For `Y gO ≫ q`, the
   composite `Y hO ≫ q` is locally surjective and factors through `Y prU'`. They
   have the same kernel: by `app_eq_iff_of_isPullback`, both kernels are given by
   arrows of `R'`, the D3 kernel pair over `Over.mk (E.t ≫ U'.hom)` having the
   same underlying scheme. `quotientSheafIsoOfPresentation` (SmoothRelationQuotientComparison)
   gives `eQ : (quotientSheaf R s t h).obj ≅ Q'.presheaf` with
   `Y gO ≫ q ≫ eQ.hom = a`.
6. *Conclusions.*
   - The quotient is an fppf sheaf because `Q'` is one (`isSheaf_of_iso_iff`).
   - Its diagonal is representable (`hasRepresentableDiagonal_of_iso`).
   - The kernel pair is `isPullback_quotientMap`.
   - `q` is representable by its representable diagonal. `Y gO ≫ q = a ≫ eQ.inv` is
     etale and surjective. The base change of `q` along it is `Y hO` over `Y prU'`
     (the flipped square of step 4). `prU'.left` is a base change of `s₁.left`, so
     it is smooth and also surjective (`s₁.left` has the reflexivity section).
     `relative_of_isEtale_isSurjective` with `P = Smooth` and `P = Surjective`
     proves `IsSmooth q` and `IsSurjective q`. The descent instances along
     surjective flat locally finitely presented maps come from Mathlib's fpqc
     descent and Zariski locality on the target.
   - The atlas is `a ≫ eQ.inv` from `U'`, and `U'.hom = g ≫ U.hom` is locally of
     finite type.

The module has no `sorry`. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.
