# Pullback of line bundles glued from unit cocycles

Module `Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback`, namespace
`Langlands.AlgebraicGeometry.Picard.CocycleGluing`.

This module shows that pulling back commutes with the gluing construction
`glued g` of `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof`. Fix a
morphism of schemes `q : Y ⟶ X`, an index type `ι : Type u`, a family of opens
`T : ι → X.Opens` and a unit family `g : ∀ i j, (Γ(X, T i ⊓ T j))ˣ`. The
pulled-back family `pullbackCocycle q g` lives on the opens `q ⁻¹ᵁ T i` of `Y`.
Its `(i, j)` entry is the image of `g i j` under
`q.appLE (T i ⊓ T j) (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) le_rfl`. The main definition is

```
noncomputable def pullbackIso (hT : (⨆ i, T i) = ⊤) (hg : IsCocycle g) :
    (Scheme.Modules.pullback q).obj (glued g) ≅ glued (pullbackCocycle q g)
```

So the pullback of the line bundle glued from `g` is the line bundle glued from
the pulled-back cocycle. The isomorphism is a specific morphism, not one chosen
by `Classical.choice`. Its forward map `pullbackHom q g` is the adjunction
transpose of the morphism `toPushforward q g` that applies `q.appLE` to every
component. It sends the pullback of the local generator `genSec g i` to the
local generator `genSec (pullbackCocycle q g) i`.

## Conventions

The conventions are those of `CocycleLineBundleProof`. A section of `glued g`
over `U` is a family `(b i)` with `b i ∈ Γ(X, U ⊓ T i)` and `b i = g i j * b j`
on every open inside `U ⊓ T i ⊓ T j`. `comp g m i` is the `i`-th component of
a section `m`. `genSec g hg i hV` is the local generator over an open
`V ≤ T i`; its `j`-th component is `g j i` restricted.

The pulled-back sheaf `glued (pullbackCocycle q g)` uses the opens
`fun i ↦ q ⁻¹ᵁ T i` of `Y`. In Mathlib `q ⁻¹ᵁ (A ⊓ B)` is definitionally
`q ⁻¹ᵁ A ⊓ q ⁻¹ᵁ B`, so the inclusions used with `q.appLE` are `le_rfl`.
`Scheme.Modules.pullbackLocalSection q s` is the image of a section `s` over
`U` under the unit of the pullback–pushforward adjunction; it is a section of
`(Scheme.Modules.pullback q).obj (glued g)` over `q ⁻¹ᵁ U`.

## Declarations

### Restriction and `q.appLE`

- `res_appLE`: restricting `q.appLE U V e a` to `V' ≤ V` gives
  `q.appLE U V' _ a`.
- `appLE_res`: `q.appLE U' V e` applied to the restriction of `a` from `U` to
  `U' ≤ U` equals `q.appLE U V _ a`.
- `res_app`: restricting `q.app U a` to `V ≤ q ⁻¹ᵁ U` gives `q.appLE U V _ a`.

### The pulled-back cocycle

- `pullbackCocycle q g i j : (Γ(Y, q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j))ˣ` is the image of
  `g i j` under the ring map `q.appLE (T i ⊓ T j) (q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j) le_rfl`
  (`Units.map`). Lemma `pullbackCocycle_val` (by `rfl`).
- `res_pullbackCocycle`: the restriction of `pullbackCocycle q g i j` to any
  `V ≤ q ⁻¹ᵁ T i ⊓ q ⁻¹ᵁ T j` is `q.appLE (T i ⊓ T j) V _ (g i j)`.
- `IsCocycle.pullback`: if `g` satisfies the cocycle identity, then so does
  `pullbackCocycle q g`. Proof: apply `q.appLE` on the triple overlap to the
  cocycle identity for `g`, and rewrite the restrictions with `appLE_res` and
  `res_pullbackCocycle`.

### Componentwise pullback of sections

- `pullbackFam q b` for `b : Fam T U` is the family on the pieces
  `q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i` whose `i`-th component is
  `q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (b i)`. Lemmas:
  `pullbackFam_apply`, `pullbackFam_add`, `pullbackFam_smul`
  (`pullbackFam q (r • b) = q.app U r • pullbackFam q b`), and
  `famRes_pullbackFam` (it commutes with restriction).
- `compat_pullbackFam`: if `b` satisfies the gluing relation for `g`, then
  `pullbackFam q b` satisfies it for `pullbackCocycle q g`.
- `pullbackFam_gen`: `pullbackFam q (gen g i hV)` is
  `gen (pullbackCocycle q g) i _`, the family of the pulled-back local
  generator.

### The comparison morphism

- `toPushforward q g : glued g ⟶ (Scheme.Modules.pushforward q).obj
  (glued (pullbackCocycle q g))` sends a section `m` of `glued g` over `U` to
  the section `mk _ (pullbackFam q m) _` of `glued (pullbackCocycle q g)` over
  `q ⁻¹ᵁ U`. Its linearity over `Γ(X, U)` is `pullbackFam_smul`, and its
  naturality is `famRes_pullbackFam`. Lemma `toPushforward_app` (by `rfl`).
- `pullbackHom q g : (Scheme.Modules.pullback q).obj (glued g) ⟶
  glued (pullbackCocycle q g)` is the image of `toPushforward q g` under the
  inverse of the hom-equivalence of
  `Scheme.Modules.pullbackPushforwardAdjunction q`. It needs neither the
  cocycle identity nor a cover hypothesis.
- `pullbackHom_app_pullbackLocalSection`: on `pullbackLocalSection q m` the
  morphism `pullbackHom q g` gives `mk _ (pullbackFam q m) _`. This is
  `Scheme.Modules.homEquiv_symm_app_pullbackLocalSection`.
- `comp_pullbackHom_app_pullbackLocalSection`: the `i`-th component of that
  image is `q.appLE (U ⊓ T i) (q ⁻¹ᵁ U ⊓ q ⁻¹ᵁ T i) le_rfl (comp g m i)`.
- `pullbackHom_app_genSec`: for a cocycle `g` and `V ≤ T i`,
  `pullbackHom q g (pullbackLocalSection q (genSec g hg i hV)) =
  genSec (pullbackCocycle q g) (hg.pullback q) i _` over `q ⁻¹ᵁ V`. Proof:
  `pullbackHom_app_pullbackLocalSection` and `pullbackFam_gen`.

### The isomorphism

- `isFrameOn_genSec`: for a cocycle `g`, the generator `genSec g hg i le_rfl`
  over `T i` is a frame on `T i` (`Scheme.Modules.IsFrameOn`): on every open
  `W ≤ T i`, multiplication by its restriction is a bijection
  `Γ(X, W) → Γ(glued g, W)`. Proof: `map_genSec` identifies the restriction
  with `genSec g hg i _` over `W`, and `smul_genSec_bijective` gives the
  bijection.
- `isIso_pullbackHom`: if `⨆ i, T i = ⊤` and `g` is a cocycle, then
  `pullbackHom q g` is an isomorphism. Proof: the criterion
  `Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top` on the cover
  `fun i ↦ q ⁻¹ᵁ T i` of `Y` (`q.iSup_preimage_eq_top hT`). The frames are
  `pullbackLocalSection q (genSec g hg i le_rfl)` (a frame by
  `Scheme.Modules.IsFrameOn.pullbackLocalSection` and `isFrameOn_genSec`) and
  `genSec (pullbackCocycle q g) _ i le_rfl` (a frame by `isFrameOn_genSec`
  for the pulled-back cocycle). They correspond by `pullbackHom_app_genSec`.
- `pullbackIso q g hT hg` is `asIso (pullbackHom q g)`, displayed above.
  Lemma `pullbackIso_hom` (`(pullbackIso q g hT hg).hom = pullbackHom q g`, by
  `rfl`).
- `comp_pullbackIso_hom_app_pullbackLocalSection`: the component formula for
  `pullbackIso` on pulled-back sections.
- `pullbackIso_hom_app_genSec`: `pullbackIso` sends
  `pullbackLocalSection q (genSec g hg i hV)` to
  `genSec (pullbackCocycle q g) _ i _`, for every `V ≤ T i`.
- `pullbackIso_inv_app_genSec`: the inverse sends
  `genSec (pullbackCocycle q g) _ i _` back to
  `pullbackLocalSection q (genSec g hg i hV)`.

## Sources and provenance

Provenance: derived. Sources:

- Stacks Project, Sheaves of Modules, Lemma 17.25.3 (tag 0B8L), in the
  registered folder
  `stacks-local-freeness-invertibility-sections-2026-10-21`, file `01CR.html`
  (Section 17.25, Invertible modules). It states: "Let
  f : (X, O_X) → (Y, O_Y) be a morphism of ringed spaces. The pullback f^*L of
  an invertible O_Y-module is invertible."
- Stacks Project, Cohomology of Sheaves, Lemma `cohomology-lemma-h1-invertible`
  (tag 09NU), in the registered folder
  `stacks-flasque-affine-vanishing-kunneth-a04446e5`, file `cohomology.tex`,
  lines 405-474 (tag map: `tags.txt` line 12227). It identifies
  `H¹(X, O_X^*)` with `Pic(X)` through the local generators of an invertible
  sheaf. The gauge module `CocycleLineBundleGauge` uses it in the same way.

Correspondence with the sources. Lemma 17.25.3 says that the pullback of an
invertible module is invertible. This module proves a sharper, explicit form
for the sheaves `glued g`: the pullback is again a glued sheaf, and its
cocycle is the image of `g` under the ring maps `q.appLE`. Lemma 09NU
describes an invertible sheaf through its local generators. Here the
corresponding statement is the generator formula: `pullbackIso` carries the
pullback of the local generator `genSec g i` to the local generator
`genSec (pullbackCocycle q g) i`. This module states only the sheaf-level
isomorphism and these formulas; it says nothing about cohomology classes.

The Lean proof is this module's own construction. It does not follow the proof
of Lemma 17.25.3, which goes through tensor inverses. The morphism is built
from the pullback–pushforward adjunction of Mathlib, and it is shown to be an
isomorphism by matching local frames with the frame criterion
`isIso_of_isFrameOn_of_iSup_eq_top` from the ported Anthropic FLT library.

Differences from the sources. The sources work with an arbitrary invertible
module. This module works only with the sheaves `glued g` over a family of
opens `T`. The morphism `pullbackHom` exists for every unit family `g` and
every family `T`; the cocycle identity and the cover hypothesis
`⨆ i, T i = ⊤` are used only for the isomorphism.
