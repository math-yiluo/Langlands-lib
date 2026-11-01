# Proof: relative polarizations are stable under canonical base change

Authors: Worker 766.

This module proves the published proposition
`Langlands.AbelianScheme.PolarizationBaseChangeStatement.{u}` from module
`Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeStatement`:

```lean
theorem Langlands.AbelianScheme.polarizationBaseChange :
    PolarizationBaseChangeStatement.{u}
```

For all construction inputs, every morphism `b : S' ⟶ S`, every abelian scheme `A/S` with
its actual endpoint choices (`hA`, `geometryA`, `MA`, `evaluationA` for `A` and `hA'`,
`geometryA'`, `MA'`, `evaluationA'` for `A_{S'}`) and every homomorphism
`lam : A ⟶ dualAbelianSchemeFromEvaluation A ...`, the theorem shows that `IsPolarization`
of `lam` implies `IsPolarization` of `dualAbelianBaseChangeMap ... b A ... lam`. The full
predicate is kept on both sides: the isogeny condition and the ample-Mumford presentation
clause at every geometric point. The theorem has no hypotheses beyond those of the statement.

The proof uses two helper modules, each with its own Markdown file:

- `Langlands.AlgebraicGeometry.Picard.AmpleMumfordTransport`: the predicate
  `HasAmpleMumfordPresentation` pulls back along a homomorphism of abelian schemes over one
  base whose underlying map is a closed immersion, provided the two Poincaré pullbacks agree
  once the rigidification is forgotten (`hasAmpleMumfordPresentation_of_homomorphism`).
- `Langlands.AlgebraicGeometry.Picard.DualBaseChangePoincare`: the Poincaré pullback along
  the base-changed dual map `dualBaseChangeMap A hA universality b f` is, as an ordinary line
  bundle, the pullback along `baseChangeFamilySpaceMap b A A.X` of the Poincaré pullback
  along `f` (`dualBaseChangeMapPoincareForgetIso`).

## Comparison lemmas in this module

Let `b : S' ⟶ S`, `c : S'' ⟶ S'` and `t : S''' ⟶ S''`, and let `A` be an abelian scheme over
`S`. `baseChangeCompIso b c A : A_{S''} ≅ (A_{S'})_{S''}` is the comparison between direct
and successive base change (module `Langlands.AbelianScheme.BaseChangeCoherence`).

- `hom_baseChange_map_fst`: for a homomorphism `φ : Z ⟶ W` over `S''`, the underlying map
  of `(baseChange t).map φ` followed by the projection `W_{S'''} ⟶ W` equals the projection
  `Z_{S'''} ⟶ Z` followed by the underlying map of `φ`.
- `baseChangeFamilySpaceMap_self_fst` and `baseChangeFamilySpaceMap_self_snd`: the two
  projection identities of `baseChangeFamilySpaceMap t Z Z.X` from the Library, restated for
  the self-product of `Z`. They exist so that `simp only` can rewrite with them; rewriting
  with the general forms timed out.
- `hom_baseChangeCompIso_inv_fst`: the underlying map of `(baseChangeCompIso b c A).inv`
  followed by the projection to `A` is the composite of the two successive projections
  (from `GroupScheme.baseChangeCompIso_inv_fst`).
- `mumfordProductMap_baseChangeComp` (equation E). Let `g` be
  `(baseChange t).map (baseChangeCompIso b c A).inv`. Then `mumfordProductMap g` followed by
  the two family-space maps for the direct base change (along `t`, then along `c ≫ b`)
  equals the three family-space maps for the successive base change (along `t`, `c`, `b`).
  Both sides are maps from the self-product of `((A_{S'})_{S''})_{S'''}` over `S'''` to
  `A ×_S A`. The proof applies `pullback.hom_ext` and, on each factor, `simp only` with the
  projection identities above and `mumfordProductMap_fst`/`mumfordProductMap_snd`.
- `isIso_hom_baseChange_map_baseChangeCompIso_inv` (instance): the underlying map of `g` is
  an isomorphism, with inverse the underlying map of
  `(baseChange t).map (baseChangeCompIso b c A).hom`. In particular it is a closed immersion.
- `hasAmpleMumfordAfterBaseChange_comp`. The hypotheses are `hA : HasDualScheme A`,
  `f : A.X ⟶ dualScheme A hA`, and an ample Mumford presentation after base change along `t`
  of the direct dual map `dualBaseChangeMap A hA universality (c ≫ b) f`. The conclusion is
  an ample Mumford presentation after base change along `t` of the successive dual map
  `dualBaseChangeMap _ _ universality c (dualBaseChangeMap A hA universality b f)`. The proof
  applies `hasAmpleMumfordPresentation_of_homomorphism` to `g`. Its compatibility hypothesis
  is a chain of ordinary line-bundle isomorphisms on the self-product of
  `((A_{S'})_{S''})_{S'''}`:
  1. `dualBaseChangeMapPoincareForgetIso` along `t`, then (pulled back) along `c`, then along
     `b`, with `LineBundle.pullbackCompEqIso` to combine the iterated pullbacks. This writes
     the successive side as the pullback of the Poincaré pullback along `f` by the three
     family-space maps of the successive base change.
  2. `LineBundle.pullbackEqIso` of equation E, which replaces that composite by
     `mumfordProductMap g` followed by the two family-space maps of the direct base change.
  3. The inverse of the analogous chain for the direct side: `dualBaseChangeMapPoincareForgetIso`
     along `t` and along `c ≫ b`, pulled back along `mumfordProductMap g`, again combined with
     `LineBundle.pullbackCompEqIso`.

## Proof of the main theorem

Introduce all inputs and the hypothesis `h : IsPolarization ... lam`. The target map is
`(baseChange b).map lam ≫ e.hom`, where `e` is the canonical comparison
`dualAbelianBaseChangeIso ... b A ...`.

**Isogeny.** The group-scheme homomorphisms underlying `e.hom` and `e.inv` form an
isomorphism `eg` of group schemes over `S'`. Hence `e.hom` is an isogeny by
`Langlands.GroupScheme.isIsogeny_of_isIso`. The isogeny condition for the target is then
`(h.1.baseChange b).comp he`, using `IsIsogeny.baseChange` and `IsIsogeny.comp` (module
`Langlands.AbelianScheme.IsogenySpecialization`).

**Geometric fibres.** Let `K` be an algebraically closed field and
`s : Spec K ⟶ S'` a geometric point. By `dualAbelianBaseChangeMap_hom`, the underlying map
of the target homomorphism is `dualBaseChangeMap A hA universality b (groupHom lam).hom.hom`.
The goal becomes the field presentation, at `s`, of
`dualBaseChangeMap _ hA' universality s (dualBaseChangeMap A hA universality b _)`.
Applying `h.2` at the geometric point `s ≫ b : Spec K ⟶ S` gives a field extension
`ι : K →+* K'` and an ample Mumford presentation after base change along
`Spec.map (CommRingCat.ofHom ι)` of the direct dual map
`dualBaseChangeMap A hA universality (s ≫ b) _`. The lemma `hasAmpleMumfordAfterBaseChange_comp`
with `c = s` and `t = Spec.map (CommRingCat.ofHom ι)` turns it into the required presentation
for the successive dual map with the same `K'` and `ι`.

The conclusion of `IsPolarization` uses the given witness `hA'`, and the transport lemma
uses `hasDualScheme_baseChange universality b A hA`. Both are proofs of the proposition
`HasDualScheme A_{S'}`, so they are definitionally equal by proof irrelevance and the term
elaborates without a cast. The endpoint data `geometryA'`, `MA'` and `evaluationA'` enter only
through `dualAbelianBaseChangeIso` and the target type, and are not changed. The proof uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The mathematical route is the one in the statement's Markdown. The isogeny part is the base
change of an isogeny composed with an isomorphism. For the fibre part, the iterated fibre at
`s` is compared with the direct fibre at `s ≫ b` through `baseChangeCompIso`, and the ample
Mumford presentation is transported across that comparison. The transported data are the
pullbacks of the given line bundles, evaluations built from canonical isomorphisms, and the
classifier equality, proved through the Poincaré-family comparisons. This is internal, derived
infrastructure for the Library's existing constructions. The file chooses no new
identification of duals, uses only the supplied construction inputs, and asserts no
existence, representability or other unconditional result.
