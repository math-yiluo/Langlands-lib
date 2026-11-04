# Extending fraction-field points along a dominating local extension

Author: Worker 254.

This module proves a domination lemma for the existence half of the
valuative criterion. Let `R` be a valuation ring and `R → R'` an injective
local homomorphism into a local domain. If the restriction of a fraction-field
point of a scheme `X` to `Frac R'` extends over `Spec R'`, then the point
already extends over `Spec R`. The declarations live in
`Langlands.GroupScheme.PseudoComplete`. They are used by
`Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange` to descend the
published DVR lifting property `PseudoComplete.HasDVRLifting` along
algebraic field extensions.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), proof
of Proposition C.1.2(3), printed p.582 (PDF p.608), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, says: if `R → R'` is a local
extension of DVRs over `k` with fraction fields `K → K'`, then
`X(R) = X(R') ∩ X(K)` inside `X(K')`, since `R = R' ∩ K` inside `K`.
Hence `X(R) = X(K)` if `X(R') = X(K')`. The proof of C.1.2(2) reuses this.
That is the existence statement proved here. The source assumes `X` separated
of finite type, so that `X(R) ⊆ X(K)`. Only the existence of extensions is
formalized here, and for existence `X` may be any scheme. `R` need only be a
valuation ring and `R'` a local domain.

## Results

- `fractionRingMap f hf : FractionRing R →+* FractionRing R'` is the map of
  fraction fields induced by an injective ring map `f` of domains
  (`IsLocalization.map`). It extends `f` (`fractionRingMap_algebraMap`) and is
  local (`isLocalHom_fractionRingMap`), being a map of fields.
- `isInteger_of_fractionRingMap`: if `R` is a valuation ring and `f` is
  injective and local, then an element of `FractionRing R` whose image in
  `FractionRing R'` lies in `R'` already lies in `R`. This is the identity
  `R = R' ∩ K`.
- `SpecMap_appLE_comp_fromSpec`: a morphism `g : Spec A ⟶ X` with
  `g ⁻¹ᵁ U = ⊤` for an affine open `U` equals
  `Spec.map (g.appLE U ⊤ _ ≫ (Scheme.ΓSpecIso A).hom) ≫ hU.fromSpec`.
- `preimage_eq_top_of_comp`: for a local homomorphism `φ : A ⟶ B` of local
  rings and `x : Spec A ⟶ X`, if `Spec.map φ ≫ x` maps all of `Spec B` into
  an open `U`, then so does `x`.
- `exists_comp_eq_of_dominates`: the domination lemma for plain schemes.
  Let `R, R' : Type u`, with `R` a domain and valuation ring and `R'` a local
  domain. Let `f : R →+* R'` be injective and local, `x` a morphism from
  `Spec (FractionRing R)` to `X`, and `y` one from `Spec R'` to `X`.
  Suppose `y` restricted along `R' → FractionRing R'` equals `x`
  restricted along `fractionRingMap f hf`. Then there is
  `z : Spec R ⟶ X` whose restriction along `R → FractionRing R` is `x`.
- `exists_extension_of_comp_eq`: over a field `k : Type u`, for
  `X : Over (Spec k)` and a domain `R` that is a `k`-algebra, a scheme
  morphism `z : Spec R ⟶ X.left` restricting to `x.left` on the generic point
  is the underlying morphism of a relative morphism
  `xR : algebraSpec k R ⟶ X` with `genericPoint R ≫ xR = x`.
- `fractionAlgHom φ hφ` is `fractionRingMap` as a `k`-algebra map, for an
  injective `k`-algebra map `φ`.
- `exists_extension_of_dominates`: the relative version, in the Library's
  conventions for `HasDVRLifting`. With `φ : R →ₐ[k] R'` injective and local,
  `x : algebraSpec k (FractionRing R) ⟶ X` and `y : algebraSpec k R' ⟶ X`,
  suppose `genericPoint R' ≫ y` equals the relative spectrum of
  `fractionAlgHom φ hφ` composed with `x`. Then there is an
  `xR : algebraSpec k R ⟶ X` with `genericPoint R ≫ xR = x`.

## Implemented proof

**Algebra.** Let `a ∈ FractionRing R`. Since `R` is a valuation ring, either
`a ∈ R` or `a⁻¹ = b` for some `b ∈ R`
(`ValuationRing.isInteger_or_isInteger`). The case `a = 0` is trivial. In the
second case, suppose the image of `a` is `c ∈ R'`. Then `f b * c` maps to `1`
in `FractionRing R'`, so `f b * c = 1` and `f b` is a unit. Locality makes `b`
a unit of `R`, and `a = b⁻¹ ∈ R`.

**Affine factorization.** `SpecMap_appLE_comp_fromSpec` specializes Mathlib's
`IsAffineOpen.SpecMap_appLE_fromSpec` to the affine open `⊤` of `Spec A`,
using `IsAffineOpen.fromSpec_top` and `Scheme.isoSpec_Spec_hom`.

**Closed points.** For `preimage_eq_top_of_comp`, an open of a local spectrum
containing the closed point is everything
(`Scheme.preimage_eq_top_of_closedPoint_mem`). `Spec.map φ` sends the closed
point to the closed point (`Spec_closedPoint`) because `φ` is local. The
point-level rewrite needs
`set_option backward.isDefEq.respectTransparency false`, as in Mathlib's
`Mathlib/AlgebraicGeometry/Stalk.lean`. The option is confined to this one
helper.

**Domination.** Choose an affine open `U` containing the image of the closed
point of `Spec R'`. Then `y ⁻¹ᵁ U = ⊤`. The map `fractionRingMap f hf` is a
local homomorphism of fields, so the restriction hypothesis and
`preimage_eq_top_of_comp` give `x ⁻¹ᵁ U = ⊤`. Both `x` and `y` factor through
`U.fromSpec` as `Spec.map χ` and `Spec.map ψ` with `χ : Γ(U) → Frac R` and
`ψ : Γ(U) → R'`. Cancelling the monomorphism `U.fromSpec` and using
`Spec.map_injective` turns the hypothesis into
`ψ ≫ (R' → Frac R') = χ ≫ fractionRingMap f hf`. Hence each `χ s` maps into
`R'`, and by `isInteger_of_fractionRingMap` it lies in `R`. So `χ` factors
through `R` as `χ'`, built from `RingHom.codRestrict` and the equivalence
`AlgEquiv.ofInjective` of `R` with its image. Take
`z = Spec.map χ' ≫ U.fromSpec`.

**Relative upgrade.** In `exists_extension_of_comp_eq`, the structure map
`z ≫ X.hom` is a morphism between affine schemes. It is the spectrum of
`Spec.preimage (z ≫ X.hom)`. Composed with the injective map
`R → FractionRing R`, it agrees with `algebraMap k R` by `Over.w x`, the
equation `algebraSpec_hom`, and the scalar tower
`k → R → FractionRing R`. So `z ≫ X.hom` is the structure map of
`algebraSpec k R`. Then `Over.homMk z` is the required relative morphism, and
`Over.OverMorphism.ext` turns the scheme-level equation into
`genericPoint R ≫ xR = x`. `exists_extension_of_dominates` applies
`exists_comp_eq_of_dominates` to the underlying morphisms and then
`exists_extension_of_comp_eq`.
