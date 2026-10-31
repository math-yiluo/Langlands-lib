# Descent of functions along quasi-compact flat surjections

This helper module supports the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`. It proves that
sections of the structure sheaf descend along a quasi-compact, flat, surjective morphism
`p : X ⟶ Y` of schemes, over every open of `Y`. It is the sheaf condition of the structure
sheaf for the fpqc topology, restricted to one covering morphism. The lemmas are internal and
have no separate literature source. Everything lives in the namespace
`Langlands.Scheme.UnitCocycleDescent`.

## Global functions

- `exists_appTop_eq_of_effectiveEpi`: let `p` be an effective epimorphism. If a global
  function `s` on `X` satisfies `a.appTop s = b.appTop s` for every scheme `U` and every
  pair `a b : U ⟶ X` with `a ≫ p = b ≫ p`, then `s = p.appTop t` for a global function `t`
  on `Y`.
- `appTop_injective_of_epi`: for an epimorphism `p`, `p.appTop` is injective.

Both proofs use Mathlib's bijection `AffineSpace.toSpecMvPolyIntEquiv PUnit` between
morphisms to the affine line `𝔸¹` and global functions. Under this bijection, composition
with a morphism corresponds to pulling back the function
(`AffineSpace.toSpecMvPolyIntEquiv_comp`). The function `s` gives a morphism `e : X ⟶ 𝔸¹`.
The hypothesis makes `e` coequalize every pair with equal composite to `Y`. So `e` factors
through `p` by `EffectiveEpi.desc`, and the factor gives `t`. For injectivity, two
functions `t` and `t'` with equal pullbacks give morphisms `Y ⟶ 𝔸¹` with equal composites
with `p`. Cancelling the epimorphism `p` shows that the morphisms are equal, so `t = t'`.

## Sections over an open

- `appLE_eq_of_eq` says that `f.appLE O W e` only depends on `f`, not on the inclusion
  proof. `appTop_eq_appLE` writes `c.appTop` as `c.appLE ⊤ ⊤ _`.
- `app_comp_ι_appLE` compares `p.app V` with `(p ∣_ V).appTop`. Both are composed with the
  isomorphisms `Γ(Y, V) ≅ Γ(V, ⊤)` and `Γ(X, p ⁻¹ᵁ V) ≅ Γ(p ⁻¹ᵁ V, ⊤)` given by the open
  immersions `ι`. The proof combines `appLE_comp_appLE` with `morphismRestrict_ι`.
  `ι_appLE_injective` says that the second of these maps is injective, since it is an
  isomorphism.
- `IsPairInvariant p O f` says that a section `f` over an open `O` of `X` satisfies
  `a.appLE O V ha f = b.appLE O V hb f` for every scheme `U`, every pair `a b : U ⟶ X` with
  `a ≫ p = b ≫ p`, and every open `V` of `U` on which both pullbacks are defined.

From now on `p` is quasi-compact, flat and surjective. Then so is `p ∣_ V` for every open
`V` of `Y`. The instance for surjectivity uses `IsZariskiLocalAtTarget.restrict`; Mathlib
supplies the other two. Mathlib's fpqc topology (`Mathlib.AlgebraicGeometry.Sites.Fpqc`)
makes such a morphism an effective epimorphism.

- `app_injective`: `p.app V` is injective for every open `V`. By `app_comp_ι_appLE`, this
  reduces to injectivity of `(p ∣_ V).appTop`, which is `appTop_injective_of_epi`.
- `exists_app_eq_of_isPairInvariant`: a pair-invariant section `f` over `p ⁻¹ᵁ V` equals
  `p.app V g` for a section `g` over `V`. Let `f'` be the global function on `p ⁻¹ᵁ V`
  corresponding to `f`. A pair `a b : U ⟶ p ⁻¹ᵁ V` with equal composite with `p ∣_ V` gives
  the pair `a ≫ ι, b ≫ ι` with equal composite with `p`. Pair invariance on the open `⊤`
  shows that `f'` satisfies the hypothesis of `exists_appTop_eq_of_effectiveEpi` for
  `p ∣_ V`. The resulting function on `V` is the image of a section `g` over `V`, and
  `app_comp_ι_appLE` with `ι_appLE_injective` gives `p.app V g = f`.
