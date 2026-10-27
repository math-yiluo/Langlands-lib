# Proof that whole generation opens commute with line-bundle section pullback

This module proves the published proposition
`Langlands.SchemeModule.LineBundlePullbackSectionOpenStatement.{u}` from
`Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenStatement`, which it
imports unchanged.

## Main result

`Langlands.SchemeModule.lineBundlePullbackSectionOpen` is the theorem

```lean
theorem lineBundlePullbackSectionOpen : LineBundlePullbackSectionOpenStatement.{u}
```

for an arbitrary universe `u`. It holds for all schemes `X Y : Scheme.{u}`,
every morphism `f : Y ⟶ X`, every `L : LineBundle X` and every
`s : GlobalSections L.obj`. It states the equality in `Y.Opens`

```text
trivializationOpen ((Scheme.Modules.pullback f).obj L.obj) (pullbackSection f L.obj s)
  = f ⁻¹ᵁ (trivializationOpen L.obj s).
```

The only hypothesis used is the local rank-one property carried by `L`. The
pullback is Mathlib's actual `Scheme.Modules.pullback f`. The section is the
published `pullbackSection`, and both sides are the published whole generation
opens `trivializationOpen`.

## Auxiliary results

All helper lemmas are stated in namespace `Langlands.SchemeModule`.

- `sectionHom_pullbackSection f M s` (public): for any `M : X.Modules` and
  `s : GlobalSections M`, the section morphism of `pullbackSection f M s`
  equals the published `pullbackSectionHom f M s`.
  `pullbackSection` is by definition the value at one on `⊤` of
  `pullbackSectionHom`. The proof applies injectivity of
  `(sectionHomEquiv _).symm` and cancels with `Equiv.symm_apply_apply`. The
  remaining goal is definitional: the inverse of `sectionHomEquiv` evaluates a
  morphism at one on `⊤`.
- `pullback_structureEnd_eq_mulHom f ψ` (public): for
  `ψ : structureModule X ⟶ structureModule X`, conjugating the pulled-back
  endomorphism `(pullback f).map ψ` by the canonical `pullbackUnitIso f` gives
  `structureMulHom (f.appTop (structureEndValue ψ ⊤))`. That is
  multiplication by the pullback of the global value of `ψ` at one. The proof
  transposes both sides along `pullbackPushforwardAdjunction f`, using the
  published characterization `Langlands.Scheme.Modules.pullbackUnitAdjunction`
  of `pullbackUnitIso`. It then compares the two morphisms into the
  pushforward on each open `U` and each section `a`. There
  `structureEnd_app_eq_mul_res`, `structureMulHom_app` and `map_mul` reduce
  the comparison to naturality of `f.app` for the inclusion `U ≤ ⊤`.
  The published `structureAutPullback_eq_ofUnit` in `StructureUnitScalars`
  makes the same computation only for automorphisms. Here `ψ` is an arbitrary
  endomorphism, which need not be invertible.
- `pullback_structureEnd_stalk_isIso_iff f ψ y` (public): the abelian-group
  stalk map of `(pullback f).map ψ` at `y` is an isomorphism if and only if
  the stalk map of `ψ` at `f y` is. By the previous lemma, `(pullback f).map ψ`
  is `pullbackUnitIso f` conjugated with the scalar endomorphism `ψ'`, and
  composition with isomorphisms is cancelled. Then the published
  `unitEnd_stalkIso_iff_residue_ne_zero`, applied to `ψ'` at `y` and to `ψ`
  at `f y`, gives both sides as nonvanishing of residues. The value of `ψ'` is
  `f.appTop` of the value of `ψ` (`structureEndValue_mulHom`). Mathlib's
  `Scheme.Γevaluation_naturality_apply` rewrites the residue of `f.appTop a`
  at `y` as the image of the residue of `a` at `f y` under
  `f.residueFieldMap y`. A ring homomorphism between fields is injective, so
  `map_ne_zero` finishes.
- `isIso_map_iso_comp_iff` (private): `F.map (α.hom ≫ g ≫ β.inv)` is an
  isomorphism if and only if `F.map g` is.
- `pullback_stalk_isIso_iff f hM φ y` (public): if `M` is locally free of rank
  one and `φ : structureModule X ⟶ M`, then the stalk map of
  `(pullback f).map φ` at `y` is an isomorphism if and only if the stalk map
  of `φ` at `f y` is. The proof chooses a trivializing open `U ∋ f y` with
  `e : M|_U ≅ O_U` from the rank-one property. It sets `V = f ⁻¹ᵁ U` and
  `g = f ∣_ U`, and forms the scalar endomorphism
  `ψ = (restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map φ ≫ e.hom` of
  `O_U`. A chain of equivalences then passes:
  1. to the restriction to `V` at `⟨y, _⟩`, by the published
     `isIso_stalk_restrict_iff`;
  2. to `pullback g` of the restriction to `U`, by `NatIso.isIso_map_iff`.
     The natural isomorphism used is the published
     `Langlands.Scheme.Modules.restrictPullbackNatIso f U` from
     `Langlands.AlgebraicGeometry.ModuleLocalHomPullback`, of type
     `pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅ restrictFunctor U.ι ⋙
     pullback (f ∣_ U)`. It is whiskered on the right by the stalk functor at
     `⟨y, _⟩`;
  3. to `pullback g` of `ψ`, by cancelling the isomorphisms around `ψ`;
  4. to `ψ` at `g ⟨y, _⟩`, by `pullback_structureEnd_stalk_isIso_iff`;
  5. back to `φ` at `U.ι (g ⟨y, _⟩) = f y`, by cancelling the isomorphisms,
     `isIso_stalk_restrict_iff` and `morphismRestrict_base_coe`.

## Proof of the main theorem

Let `L'` be the line bundle on `Y` with object `(pullback f).obj L.obj`. Its
rank-one property is the published `IsLocallyFreeRankOne.pullback`. The
published `lineBundle_stalkFrame_set_eq` identifies the underlying set of a
line bundle's whole generation open with the set of its stalk frames. The
proof uses it for `L'` with `pullbackSection f L.obj s` and for `L` with `s`.
By `Opens.ext` it then suffices to show, for each `y : Y`, that
`IsStalkFrame ((pullback f).obj L.obj) (pullbackSection f L.obj s) y` holds
if and only if `IsStalkFrame L.obj s (f y)` holds. After unfolding
`IsStalkFrame` the proof rewrites with `sectionHom_pullbackSection` and the
definition of `pullbackSectionHom`. It then discards the isomorphism
`(pullbackUnitIso f).inv` with `isIso_comp_left_iff`. The remaining
equivalence is `pullback_stalk_isIso_iff f L.property (sectionHom L.obj s) y`.

## Provenance

The statement is an internal derived proposition, as its own Markdown
explains. The proof follows the route suggested there. It uses local rank-one
trivializations to show that the stalk frame condition is preserved and
reflected under pullback. On residue fields it uses only that the induced ring
homomorphism between fields is injective. It does not use `lineBundleSectionResidueComparison`.
