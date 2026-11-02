# Effective flat descent of line bundles over an affine base

Module `Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentCore`,
namespace `Langlands.Scheme.Modules.LineBundleFlatDescent`.

This module proves the local case of effective descent. Let
`D : Datum p F` be descent data for a line bundle `F` along an affine, flat and
surjective `p : X ⟶ Y` (see `LineBundleFlatDescentStr`), and let
`t : T ⟶ Y` with `T` affine. Then `exists_str D hF t` gives a line bundle `N`
on `T` together with a descended structure `Str D t N`. Here `Y` is
arbitrary; the gluing over an affine cover of `Y` is in
`LineBundleDescentEffectiveProof`.

## A trivializing affine flat cover

- `hom_ext_of_isEmpty`: morphisms of modules on an empty scheme are equal (all
  section modules are modules over the zero ring).
- `square_comm_of_eq`: over a pair of equal maps, a square comparison commutes
  with pullbacks of any isomorphism.
- `exists_trivializing_cover`: a line bundle `G` on a quasi-compact scheme `W`
  becomes trivial on some flat surjective `v : V ⟶ W` with `V` affine.
  Construction: by quasi-compactness, finitely many affine trivializing opens
  `U x` cover `W` (`IsLocallyFreeRankOne.exists_affine_trivialization`). Take
  `V = ∐ U x` (affine, as a finite coproduct of affines) and
  `v = Sigma.desc (U x).ι`, which is flat and surjective. The local
  trivializations glue to `v^*G ≅ O_V` by the published isomorphism gluing on
  Mathlib's `sigmaOpenCover`. The overlap condition holds because distinct
  members have empty intersection (`isEmpty_pullback_sigmaι_of_ne`) and on a
  diagonal overlap the two projections agree (`fst_eq_snd_of_mono_eq`).

## Transported automorphisms of the structure sheaf

For `a b : U ⟶ V`, a trivialization `β : G ≅ O_V` and `E : a^*G ≅ b^*G`,
`unitAut a b β E` is the automorphism of `O_U` obtained by conjugating `E` with
`a^*β`, `b^*β` and the canonical `pullbackUnitIso`. By definition the published
`equalCompositeUnitAut q a b h α` is `unitAut a b α (equalCompositeIso q a b h L)`.
Lemmas:

- `unitAut_trans`: composition.
- `unitAut_precomp`: precomposition along `k` corresponds to the published
  `structureAutPullback k`. The proof is that of the published
  `equalCompositeUnitAut_precomp`, for a general `E`.
- `unitAut_eq`: equal transported automorphisms for two trivializations
  `β₁ β₂` mean that `E₁` and `E₂` are intertwined by `β₁ ≪≫ β₂.symm`.

## The unit cocycle

`Datum.pullbackθ D w a b h` is the descent isomorphism `θ (a ≫ w) (b ≫ w)`
rewritten as an isomorphism `a^*(w^*F) ≅ b^*(w^*F)` with composition
comparisons. Lemmas: `pullbackθ_trans` (cocycle law), `pullbackθ_precomp`
(naturality, from `θ_tr`).

`exists_descent_of_trivial`: let `q : V ⟶ T` be affine, flat and surjective,
`w : V ⟶ X` with `q ≫ t = w ≫ p`, and `τ : w^*F ≅ O_V`. The global units
`c U a b h := structureAutScalar (unitAut a b τ (pullbackθ D w a b _))` on
pairs with `a ≫ q = b ≫ q` are natural (by `pullbackθ_precomp`,
`unitAut_precomp` and the published `structureAutScalar_pullback`) and
multiplicative (by `structureAutScalar_trans`, `unitAut_trans` and
`pullbackθ_trans`). The published `unitCocycleDescentEffective` gives a line
bundle `L` on `T` and `α : q^*L ≅ O_V` with comparison scalars `c`. Since
`structureAutScalar` is injective, `unitAut_eq` shows that
`Ξ := α ≪≫ τ.symm : q^*L ≅ w^*F` satisfies

`tr a Ξ ≫ θ (a ≫ w) (b ≫ w) = tr b Ξ` for all `a ≫ q = b ≫ q`.

`descent_compat_gen` states the same with arbitrary prescribed composites.

## The core theorem

`exists_str D hF t` for `[IsAffineHom p] [Flat p] [Surjective p]`,
`hF : IsLocallyFreeRankOne F` and `T` affine. Write `X_T = X ×_Y T` with
projections `Q = pullback.fst p t` and `P = pullback.snd p t`. `X_T` is affine.

1. `exists_trivializing_cover` applied to `Q^*F` on `X_T` gives `v : V ⟶ X_T`.
   Put `q = v ≫ P` (affine, flat, surjective, since `V` and `T` are affine) and
   `w = v ≫ Q`. `exists_descent_of_trivial` gives `L` and `Ξ : q^*L ≅ w^*F`.
2. `e := compIso ≪≫ Ξ ≪≫ compIso⁻¹ : v^*(P^*L) ≅ v^*(Q^*F)` satisfies the
   hypothesis of `lineBundleIsoDescent` along `v` (quasi-compact, flat and
   surjective). For `a ≫ v = b ≫ v` this is `compat_of_tr_eq`, together with
   `descent_compat_gen` and `θ_self`. Descent gives
   `γ₀ : P^*L ≅ Q^*F` with `tr v γ₀ = Ξ`.
3. The descended structure transports `γ₀` along `ℓ = pullback.lift g h`
   using the existing `CommonSourceCocycle.transport` with projections `P`, `Q`
   and prescribed composites `h`, `g`. Naturality is `tr_tr_eq` plus the uniqueness of
   lifts. For the cocycle law, both sides are compared after transport along a
   quasi-compact flat surjection `r : Z' ⟶ Z`, obtained from two base changes
   of `v`, over which the two lifts `ℓ₁ ℓ₂` factor through `v` as `a₁ a₂`. There
   both sides become `tr aᵢ Ξ` composed with descent isomorphisms, and the
   cocycle law is `descent_compat_gen`. `iso_ext_of_tr` then concludes.
