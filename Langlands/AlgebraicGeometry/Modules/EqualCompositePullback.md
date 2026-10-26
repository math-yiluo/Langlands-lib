# Canonical comparison of pullbacks along equal composites

This module, in namespace `Langlands.Scheme.Modules`, works with arbitrary
schemes `U`, `X`, `Y` in one universe `u`, a morphism `p : X ⟶ Y`, two
morphisms `a b : U ⟶ X` and a proof `h : a ≫ p = b ≫ p`. For each module
sheaf `M : Y.Modules` it defines the canonical isomorphism
`a^* p^* M ≅ b^* p^* M`. For each trivialization `α : p^* M ≅ O_X` it defines
the induced automorphism of the structure sheaf `O_U`. It also proves the
elementary laws of both constructions.

Here `f^*` is Mathlib's `Scheme.Modules.pullback f`, and `O_S` is
`SheafOfModules.unit S.ringCatSheaf`. `pullbackUnitIso f : f^* O_T ≅ O_S` is
the published canonical unit comparison in
`Langlands.AlgebraicGeometry.Modules.PullbackUnit`.

## Provenance

This is an internal, derived categorical interface. It was requested as a
generic prerequisite for the intrinsic-character construction (task
cda49074). That construction is motivated by Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (preliminary draft), Chapter VII, 7.1–7.4. The
book does not state these generalized categorical lemmas; the module claims no
correspondence with a numbered result there. Every construction is a composite
of canonical isomorphisms that already exist: Mathlib's `pullbackComp` and
`pullbackCongr`, and the published `pullbackUnitIso`. Every law follows from
the coherence results published in
`Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs` and
`Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs`.

## The canonical comparison

`equalCompositeIso p a b h M : a^* p^* M ≅ b^* p^* M` composes three
isomorphisms, in this order:

1. `(Scheme.Modules.pullbackComp a p).app M : a^* p^* M ≅ (a ≫ p)^* M`;
2. `(Scheme.Modules.pullbackCongr h).app M : (a ≫ p)^* M ≅ (b ≫ p)^* M`;
3. `((Scheme.Modules.pullbackComp b p).app M).symm : (b ≫ p)^* M ≅ b^* p^* M`.

`equalCompositeNatIso p a b h` is the same composite as a natural isomorphism
`pullback p ⋙ pullback a ≅ pullback p ⋙ pullback b` of functors
`Y.Modules ⥤ U.Modules`. `equalCompositeNatIso_app` says its component at
`M` is `equalCompositeIso p a b h M`.

Evaluation lemmas:

- `equalCompositeIso_hom` (by `rfl`): the forward map is
  `(pullbackComp a p).hom.app M ≫ (pullbackCongr h).hom.app M ≫
  (pullbackComp b p).inv.app M`.
- `equalCompositeIso_inv`: the inverse map is
  `(pullbackComp b p).hom.app M ≫ (pullbackCongr h).inv.app M ≫
  (pullbackComp a p).inv.app M`.
- `equalCompositeIso_hom_eq_compHom`: the forward map is the published
  generalized comparison
  `Langlands.SchemeModule.RigidifiedModule.compHom a p (b ≫ p) h M`, followed
  by `(pullbackComp b p).inv.app M`.

Laws, each holding for arbitrary proofs of the equations involved:

- `equalCompositeIso_refl` (simp): for `h : a ≫ p = a ≫ p`, the comparison is
  `Iso.refl _`.
- `equalCompositeIso_symm`: for `h : a ≫ p = b ≫ p` and
  `h' : b ≫ p = a ≫ p`, `equalCompositeIso p b a h' M` equals
  `(equalCompositeIso p a b h M).symm`.
- `equalCompositeIso_trans` (cocycle law): for `h : a ≫ p = b ≫ p`,
  `h' : b ≫ p = c ≫ p` and `h'' : a ≫ p = c ≫ p`, the composite
  `equalCompositeIso p a b h M ≪≫ equalCompositeIso p b c h' M` equals
  `equalCompositeIso p a c h'' M`.
- `equalCompositeIso_hom_naturality` (with a `reassoc` form): for
  `φ : M ⟶ N`, `a^* (p^* φ) ≫ (equalCompositeIso p a b h N).hom` equals
  `(equalCompositeIso p a b h M).hom ≫ b^* (p^* φ)`.
- `equalCompositeIso_precomp_hom` (with a `reassoc` form): for any scheme
  `V`, any `q : V ⟶ U` and any `h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p`, the map
  `(pullbackComp q a).hom.app (p^* M) ≫ (equalCompositeIso p (q ≫ a) (q ≫ b) h' M).hom`
  equals `q^* (equalCompositeIso p a b h M).hom ≫ (pullbackComp q b).hom.app (p^* M)`.
- `equalCompositeIso_precomp`: the same as an equation of isomorphisms.
  `equalCompositeIso p (q ≫ a) (q ≫ b) h' M` equals
  `((pullbackComp q a).app (p^* M)).symm ≪≫ (pullback q).mapIso (equalCompositeIso p a b h M) ≪≫ (pullbackComp q b).app (p^* M)`.

## The trivialized automorphism of `O_U`

`equalCompositeUnitAut p a b h α`, for `α : p^* M ≅ O_X` (with `M` implicit),
is the automorphism of `O_U` given by composing, in this order:

1. `(pullbackUnitIso a).symm : O_U ≅ a^* O_X`;
2. `((pullback a).mapIso α).symm : a^* O_X ≅ a^* p^* M`;
3. `equalCompositeIso p a b h M : a^* p^* M ≅ b^* p^* M`;
4. `(pullback b).mapIso α : b^* p^* M ≅ b^* O_X`;
5. `pullbackUnitIso b : b^* O_X ≅ O_U`.

Write `α_a` for the trivialization `a^* p^* M ≅ O_U` given by `a^* α` followed
by `pullbackUnitIso a`, and define `α_b` the same way. The automorphism is
then `α_a⁻¹`, followed by the canonical comparison, followed by `α_b`. It
compares the trivialization along `b` with the one along `a`, moved across by
the canonical comparison: the transported action divided by the trivial action.

Evaluation lemmas:

- `equalCompositeUnitAut_hom` (by `rfl`): the forward map is
  `(pullbackUnitIso a).inv ≫ a^* α.inv ≫ (equalCompositeIso p a b h M).hom ≫
  b^* α.hom ≫ (pullbackUnitIso b).hom`.
- `equalCompositeUnitAut_inv`: the inverse map is
  `(pullbackUnitIso b).inv ≫ b^* α.inv ≫ (equalCompositeIso p a b h M).inv ≫
  a^* α.hom ≫ (pullbackUnitIso a).hom`.

Laws, again for arbitrary proofs of the equations:

- `equalCompositeUnitAut_refl` (simp): for `h : a ≫ p = a ≫ p`, the
  automorphism is `Iso.refl _`.
- `equalCompositeUnitAut_symm`: `equalCompositeUnitAut p b a h' α` equals
  `(equalCompositeUnitAut p a b h α).symm`.
- `equalCompositeUnitAut_trans` (cocycle law):
  `equalCompositeUnitAut p a b h α ≪≫ equalCompositeUnitAut p b c h' α` equals
  `equalCompositeUnitAut p a c h'' α`.
- `equalCompositeUnitAut_precomp` (compatibility with pullback along any
  `q : V ⟶ U` of schemes): `equalCompositeUnitAut p (q ≫ a) (q ≫ b) h' α`
  equals
  `(pullbackUnitIso q).symm ≪≫ (pullback q).mapIso (equalCompositeUnitAut p a b h α) ≪≫ pullbackUnitIso q`.
- `equalCompositeUnitAut_of_iso` (change of module): for an isomorphism
  `e : M ≅ N` and `β : p^* N ≅ O_X`, the automorphism for the trivialization
  `(pullback p).mapIso e ≪≫ β` of `p^* M` equals the automorphism for `β`.
- `equalCompositeUnitAut_pullbackUnitIso` (simp): for `M = O_Y` and the
  canonical trivialization `α = pullbackUnitIso p`, the automorphism is
  `Iso.refl _`.

The helper `pullbackUnitIso_inv_pullbackCongr_hom` says that for `hfg : f = g`
with `f g : U ⟶ X`, the composite `(pullbackUnitIso f).inv ≫
(pullbackCongr hfg).hom.app O_X ≫ (pullbackUnitIso g).hom` is the identity.

None of these results takes a linearization, group action, scalar, character
or coherence hypothesis as input. Identifying `Aut(O_U)` with units of global
sections is outside this module.

## Proofs

- `equalCompositeIso_inv`, `equalCompositeIso_hom_eq_compHom` and
  `equalCompositeNatIso_app` unfold the definitions (`compHom` is
  `pullbackComp`, then `pullbackCongr`) and finish with `simp`.
- `equalCompositeIso_refl`, `_symm` and `_trans` unfold `equalCompositeIso`
  and Mathlib's `pullbackCongr`, which is an `eqToIso` of functors. `simp`
  cancels the inverse/forward pairs of `pullbackComp` components and composes
  the resulting `eqToHom` maps, which gives the claimed identities.
- `equalCompositeIso_hom_naturality` is the naturality of
  `equalCompositeNatIso p a b h`, rewritten with `equalCompositeNatIso_app`.
- `equalCompositeIso_precomp_hom` first composes both sides with
  `(pullbackComp (q ≫ b) p).hom.app M`, which is an isomorphism
  (`cancel_mono`). It then uses two instances of the published `compHom_assoc`
  together with `compHom_rfl`. One instance is for `q`, `a`, `p` with the
  equations `h` and `h'`. The other is for `q`, `b`, `p` with the defining
  equations. The left side becomes
  `(pullbackComp q a).hom.app (p^* M) ≫ compHom (q ≫ a) p ((q ≫ b) ≫ p) h' M`.
  The first instance turns this into
  `q^* (compHom a p (b ≫ p) h M) ≫ compHom q (b ≫ p) ((q ≫ b) ≫ p) _ M`.
  Inserting `q^* (pullbackComp b p).inv.app M ≫ q^* (pullbackComp b p).hom.app M`,
  which is the identity, and applying the second instance gives the right side.
  The last step uses `equalCompositeIso_hom_eq_compHom` and functoriality of
  `q^*`. `equalCompositeIso_precomp` is the isomorphism form: `Iso.ext`, then
  this equation after cancelling `(pullbackComp q a).inv` against its forward
  map.
- `pullbackUnitIso_inv_pullbackCongr_hom`: substituting `hfg` turns
  `pullbackCongr rfl` into the identity, and `simp` cancels the unit
  comparisons.
- `equalCompositeUnitAut_inv` is computed by `simp` from the definition.
  `equalCompositeUnitAut_refl` follows from `equalCompositeIso_refl`, after
  which the inverse/forward pairs cancel. `equalCompositeUnitAut_symm` rewrites
  with `equalCompositeIso_symm` and compares with the inverse formula.
- `equalCompositeUnitAut_trans` rewrites the three automorphisms by
  `equalCompositeUnitAut_hom` and the composite comparison by
  `equalCompositeIso_trans`. In the middle, `b^* α.hom ≫ pullbackUnitIso b ≫
  (pullbackUnitIso b).inv ≫ b^* α.inv` then cancels by `simp`.
- `equalCompositeUnitAut_precomp` rewrites the comparison for `q ≫ a`,
  `q ≫ b` with `equalCompositeIso_precomp`. It then uses naturality of
  `(pullbackComp q a).inv` at `α.inv` and of `(pullbackComp q b).hom` at
  `α.hom`. It also uses the published `pullbackUnitComposition` for `q` and
  `b`, and the published `pullbackUnitIso_inv_comp` for `q` and `a` (in a
  rearranged form). These move every factor under `q^*`. `simp` then closes
  the goal with functoriality of `q^*`.
- `equalCompositeUnitAut_of_iso` expands the composite trivialization.
  `equalCompositeIso_hom_naturality` at `e.inv` moves `a^* p^* e.inv` across
  the comparison. Then `b^* (p^* e.inv) ≫ b^* (p^* e.hom)` cancels
  (`Iso.map_inv_hom_id` and functoriality).
- `equalCompositeUnitAut_pullbackUnitIso` uses `pullbackUnitIso_inv_comp` for
  `a`, `p` and `pullbackUnitComposition` for `b`, `p`. These turn the two ends
  into the unit comparisons along `a ≫ p` and `b ≫ p`. The helper
  `pullbackUnitIso_inv_pullbackCongr_hom` then gives the identity.

## Technical notes

Several lemmas use the local option
`backward.isDefEq.respectTransparency false`. This lets elaboration identify
`SheafOfModules.unit S.ringCatSheaf` across the scheme-module wrappers, as in
the published coherence modules. The module adds no hypotheses beyond those
displayed and no axioms.
