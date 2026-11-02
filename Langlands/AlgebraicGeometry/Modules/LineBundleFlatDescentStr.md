# Descent structures for effective flat descent of line bundles

Module `Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr`, namespace
`Langlands.Scheme.Modules.LineBundleFlatDescent`.

This module sets up the bookkeeping used in the proof of
`Langlands.Scheme.Modules.LineBundleDescentEffectiveStatement` (see
`LineBundleFlatDescentCore` and `LineBundleDescentEffectiveProof`). Its main
inputs are the published composition comparisons
`Langlands.Scheme.Modules.compIso g u u' h C : g^*(u^*C) ≅ u'^*C`
(`PullbackTransport`) for an equation `h : g ≫ u = u'`, and the proved
isomorphism descent `LineBundleIsoDescent.lineBundleIsoDescent`. All
constructions are internal auxiliary devices with no counterpart in the
literature.

## Transport between pullbacks

- `compIso_rfl`, `compIso_assoc`, `compIso_naturality`: for `u' = k ≫ u` the
  comparison is Mathlib's `pullbackComp`; the comparisons are associative and
  natural in the module.
- `tr k hu hv φ`: transport of `φ : u^*C ⟶ v^*D` (with `C` and `D` modules on
  possibly different schemes `A` and `B`) along `k : Z' ⟶ Z` to
  `u'^*C ⟶ v'^*D`, for `hu : k ≫ u = u'` and `hv : k ≫ v = v'`. It is
  `compIso⁻¹ ≫ k^*φ ≫ compIso`. This is the published
  `Langlands.Scheme.Modules.transport` generalized from one base module to two.
  The existing `CommonSourceCocycle.transport` from
  `CommonSourceTransitionTransport` supplies the isomorphism construction;
  `transport_hom` identifies its forward map with `tr`.
- Calculus: `tr_comp`, `tr_id`, `tr_map` (transport of a pullback of a module
  morphism), `tr_compIso` and `tr_compIso_inv` (transport of a composition
  comparison is a composition comparison), `tr_inv`, `tr_inv'`, `inv_eq_tr`,
  `tr_tr` and `tr_tr_eq` (transport along a composite is iterated transport),
  `tr_congr`, and `map_eq_of_tr_eq` (equal transports have equal pullbacks
  along `k`).
- `equalCompositeIso_hom_eq_compIso` writes the canonical equal-composite
  comparison through any common composite. `compat_of_tr_eq` derives the
  compatibility hypothesis of `LineBundleIsoDescentStatement`, for a pair
  `a b` with `a ≫ q = b ≫ q`, from the equality `tr a f = tr b f` of
  transports to a common composite.
- The existing `UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso`
  writes a square comparison through any common composite. Its composition
  comparisons agree definitionally with the public `compIso` used here.

## Faithfulness

- `iso_ext_of_pullback`: if `q` is quasi-compact, flat and surjective, two
  isomorphisms `φ ψ : M ≅ N` of line bundles with `q^*φ = q^*ψ` are equal. This
  follows from the uniqueness half of `lineBundleIsoDescent` applied to
  `e := q^*φ`.
- `iso_ext_of_tr`: the same for isomorphisms between pullbacks, detected by
  their transports along a quasi-compact flat surjection `k`.

## Descent data and descended structures

Fix `p : X ⟶ Y` and a module `F` on `X`.

- `Datum p F` bundles the hypotheses of `LineBundleDescentEffectiveStatement`:
  isomorphisms `θ U a b h : a^*F ≅ b^*F` for every pair with
  `h : a ≫ p = b ≫ p`, the naturality law `nat` and the cocycle law `coc`,
  in exactly the form of the statement. Lemmas: `Datum.θ_tr` (naturality in
  transport form, with arbitrary prescribed composites), `Datum.θ_self`
  (`θ U a a` is the identity), `Datum.θ_symm`.
- `Str D t N`, for `t : T ⟶ Y` and a module `N` on `T`, is a descended
  structure on `N` over `t`. It consists of isomorphisms
  `γ Z g h hs : h^*N ≅ g^*F` for every factorization `hs : h ≫ t = g ≫ p`
  (`g : Z ⟶ X`, `h : Z ⟶ T`), natural under precomposition in transport form
  (`nat`, with arbitrary prescribed composites) and compatible with the
  descent data: `γ Z g₁ h ≫ θ Z g₁ g₂ = γ Z g₂ h` (`coc`). For `t = 𝟙 Y`
  and `Z = X`, `γ X (𝟙 X) p` gives `p^*N ≅ F` (up to `pullbackId`), so the
  effectivity statement amounts to constructing a descended structure.
- `Str.Hom S S' φ`: a morphism `φ : N ⟶ N'` compatible with `S : Str D t N`
  and `S' : Str D t' N'`, that is `h^*φ ≫ S'.γ g h = S.γ g h` at every
  factorization. The base maps `t` and `t'` may differ syntactically. Lemmas:
  `Hom.id`, `Hom.comp` (given `t = t'`), `Hom.inv`.
- `Str.restrict S u t' hu`: restriction along `u : T' ⟶ T` with
  `hu : u ≫ t = t'`, a structure on `u^*N`. `restrict_γ` computes its
  comparisons through any prescribed composite. `Str.transfer S ψ`: transfer
  along `ψ : N' ≅ N`.
- Compatibility of these operations: `Hom.transfer` (`ψ` is compatible with
  `S.transfer ψ` and `S`), `Hom.restrict` (restriction preserves
  compatibility), `Hom.restrict_restrict` (the composition comparison relates a
  twofold restriction to the restriction along the composite), and
  `Hom.square` (a square comparison relates the two twofold restrictions
  around a commutative square).
- `Str.coc_inv` is the cocycle law for inverses. `Str.hom_of_universal`: a
  morphism is compatible as soon as the condition holds at the universal
  factorization `pullback.snd p t ≫ t = pullback.fst p t ≫ p` through
  `X ×_Y T`.

## Uniqueness and existence of compatible isomorphisms

Assume `p` quasi-compact, flat and surjective, and let `N`, `N'` be line
bundles on `T`.

- `Str.hom_ext`: two isomorphisms `N ≅ N'` compatible with `S` and `S'` are
  equal. At the universal factorization both pullbacks along
  `pullback.snd p t` equal `S.γ ≫ S'.γ⁻¹`, and `iso_ext_of_pullback` applies
  to the base change `pullback.snd p t` of `p`.
- `Str.exists_hom`: for `S : Str D t N` and `S' : Str D t N'` there is an
  isomorphism `N ≅ N'` compatible with both. Apply `lineBundleIsoDescent`
  along `pullback.snd p t` to `e := S.γ ≪≫ S'.γ.symm` at the universal
  factorization. Its compatibility for pairs `a b` with equal composites
  follows from `compat_of_tr_eq`, naturality (`nat`) and the cocycle laws
  (`coc`, `coc_inv`). The descended isomorphism is compatible by
  `hom_of_universal`.
