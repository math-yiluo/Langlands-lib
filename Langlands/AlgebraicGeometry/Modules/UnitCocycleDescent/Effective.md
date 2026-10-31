# Effective descent of unit cocycles to line bundles

This helper module assembles the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement` from the other modules in
`UnitCocycleDescent`. It still takes the published algebraic statement
`Langlands.Algebra.UnitCocycleLocalUnitsStatement.{u}` as a hypothesis `hA`. The module
`UnitCocycleDescentEffectiveProof` discharges `hA` with its published proof. The lemmas are
internal. The construction is the classical descent of a module along a faithfully flat
ring map (Stacks Project, Descent, Proposition 3.9, Tag 023N), done on the opens of `Y`.
Everything lives in the namespace `Langlands.Scheme.UnitCocycleDescent`.

The module sets `backward.isDefEq.respectTransparency false`, as some Library files on
sheaves of modules do, so that sections of pullback and pushforward modules unfold during
elaboration.

## Transposes along the pullback–pushforward adjunction

For a morphism `g`, write `g^*` and `g_*` for `Scheme.Modules.pullback g` and
`Scheme.Modules.pushforward g`. Write `φ♭` for the transpose of a map `g^* M ⟶ 𝒪` under
`pullbackPushforwardAdjunction g`, a map `M ⟶ g_* 𝒪`.

- `homEquiv_pullbackComp_inv_comp`: let `f : U ⟶ X` and `φ : p^* M ⟶ 𝒪_X`. Let `A` be the
  composite
  `(f ≫ p)^* M ≅ f^* p^* M ⟶ f^* 𝒪_X ≅ 𝒪_U`
  of `(pullbackComp f p).inv`, `f^* φ` and `(pullbackUnitIso f).hom`. Then `A♭` is
  `φ♭ ≫ p_*(unitToPushforwardUnit f) ≫ (pushforwardComp f p).hom`. The proof uses the
  published lemmas `homEquiv_comp_map`, `pullbackUnitAdjunction` and
  `homEquiv_conjugate` with `conjugateEquiv_pullbackComp_inv`.
- `homEquiv_pullbackComp_inv_comp_app`: on sections over an open `W` of `Y`, the previous
  lemma says `A♭.app W s = f.app (p ⁻¹ᵁ W) (φ♭.app W s)`.
- `homEquiv_pullbackCongr_hom_app`: for `e : g₁ = g₂` and `k : g₂^* M ⟶ 𝒪_U`, the transpose
  of `(pullbackCongr e).hom ≫ k` along `g₁` sends `s` to the restriction of `k♭.app W s`
  along `g₁ ⁻¹ᵁ W = g₂ ⁻¹ᵁ W`. The proof is by `subst`.

## The trivialization

Fix `p` and the family `c`. Write `L = cocycleModule p c` and `ι : L ⟶ p_* 𝒪_X` for the
inclusion of the subsheaf (`UnitCocycleDescent.Submodule`).

- `cocycleTriv p c : p^* L ⟶ 𝒪_X` is the transpose of `ι`.
- `homEquiv_cocycleTriv_app`: its transpose sends a section of `L` over `W` to itself, as a
  section of `𝒪_X` over `p ⁻¹ᵁ W`.

From now on `p` is affine, flat and surjective and `c` is natural and multiplicative
(`IsNatural`, `IsMultiplicative` from `UnitCocycleDescent.Affine`).

- `isLocallyFreeRankOne_cocycleModule`: given `hA`, `L` is locally free of rank one. Every
  point `y` of `Y` has a neighbourhood `W` with a cocycle section that is a unit
  (`exists_unit_cocycleSection`). Then `L` is trivial on `W`
  (`nonempty_restrict_iso_unit`).
- `isIso_cocycleTriv`: given `hA`, `cocycleTriv p c` is an isomorphism. The source `p^* L`
  is locally free of rank one, by the Library's `IsLocallyFreeRankOne.pullback`. Apply the
  local unit criterion `isIso_of_isUnit_app_locally` from
  `UnitCocycleDescent.StalkCriterion`. For a point `x` of `X`, take `W` and `σ` as above for
  `y = p x`. The section of `p^* L` over `p ⁻¹ᵁ W` given by the adjunction unit applied to
  `σ` is sent by `cocycleTriv` to `σ` (`homEquiv_cocycleTriv_app`, `homEquiv_unit`). This is
  a unit.

## The comparison scalars

`structureAutScalar_cocycleTriv`: if `cocycleTriv p c` is an isomorphism `α`, then for every
pair `a b : U ⟶ X` with `h : a ≫ p = b ≫ p`, the scalar
`structureAutScalar (equalCompositeUnitAut p a b h α)` is `c U a b h`.

Proof. By the published `equalCompositeUnitAut_hom` and `equalCompositeIso_hom`, the
automorphism of `𝒪_U` is `A⁻¹ ≫ B`. Here `A` is the composite above for `f = a` and
`φ = α`, and `B` is `(pullbackCongr h).hom` followed by the analogous composite for
`f = b`. The main step `key` shows `B = A ≫ structureMulHom (c U a b h)`. Both sides are
maps out of `(a ≫ p)^* L`, so it suffices to compare their transposes along `a ≫ p` on a
section `s` of `L` over `W`. By the transpose lemmas, the left side gives the restriction of
`b.app (p ⁻¹ᵁ W) s` to `a ⁻¹ᵁ p ⁻¹ᵁ W`. By `homEquiv_naturality_right` and
`structureMulHom_app`, the right side gives `a.app (p ⁻¹ᵁ W) s` times the restriction of
`c U a b h`. These agree because `s` satisfies the cocycle condition of
`UnitCocycleDescent.Submodule` on the open `V = a ⁻¹ᵁ p ⁻¹ᵁ W`. So the automorphism is
`A⁻¹ ≫ A ≫ structureMulHom (c U a b h) = structureMulHom (c U a b h)` (`hE`). Its scalar is
`c U a b h` by `structureEndValue_mulHom`.

## Assembly

`unitCocycleDescentEffective_of_localUnits`: `UnitCocycleLocalUnitsStatement.{u}` implies
`UnitCocycleDescentEffectiveStatement.{u}`. Given `X`, `Y`, `p` and `c` as in the statement,
the line bundle is `L = cocycleModule p c` with `isLocallyFreeRankOne_cocycleModule`. The
trivialization `α` is `asIso (cocycleTriv p c)` (`isIso_cocycleTriv`), and its comparison
scalars are given by `structureAutScalar_cocycleTriv`.
