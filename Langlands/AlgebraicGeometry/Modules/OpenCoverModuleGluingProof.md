# Proof of gluing of module sheaves over a scheme open cover

This module proves the published proposition
`Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u}` from
[`OpenCoverModuleGluingStatement`](OpenCoverModuleGluingStatement.md), which it
imports unchanged. It also imports
[`OpenCoverHomGluing`](OpenCoverHomGluing.md) for `hom_map_app` and
`squarePullbackIso_hom_compHom`. Through that import it uses
[`ModuleLocalHomPullbackProofs`](../ModuleLocalHomPullbackProofs.md)
(`presheaf_map_subsingleton`, `restrictCompIso`,
`restrictCompIso_hom_app_comp`) and the pullback comparison `compHom` of
[`RigidifiedPullbackProofs`](../Picard/RigidifiedPullbackProofs.md).

## Main result

`Langlands.Scheme.Modules.openCoverModuleGluing` is the theorem

```lean
theorem openCoverModuleGluing : OpenCoverModuleGluingStatement.{u}
```

for an arbitrary universe `u`. It holds for every scheme `X : Scheme.{u}`,
every open cover `𝒰 : X.OpenCover.{u}` with maps `uᵢ := 𝒰.f i`, every family
of module sheaves `Mᵢ : (𝒰.X i).Modules` and every family of isomorphisms
`φᵢⱼ : p₁* Mᵢ ≅ p₂* Mⱼ` on `Uᵢ ×[X] Uⱼ` satisfying the statement's cocycle
condition on the triple overlaps
`pullback (pullback.fst uᵢ uⱼ) (pullback.fst uᵢ uₖ)`. It produces a module
sheaf `N : X.Modules`, isomorphisms `ψᵢ : uᵢ* N ≅ Mᵢ` and the statement's
compatibility of the `ψᵢ` with the `φᵢⱼ`. No hypothesis beyond the
statement's is used; in particular `φᵢᵢ = id` is not assumed. The theorem
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Strategy

The proof follows the first proof of Stacks Lemma 6.33.2 (tag 00AK), in the
module form of Lemma 6.33.3. There the sections of the glued sheaf over `W` are
the compatible families in `∏ᵢ 𝓕ᵢ(W ∩ Uᵢ)`. The Lean proof realises this as a
limit in `X.Modules`, so the module structure and the sheaf condition come from
Mathlib's limits of module sheaves.

1. **Glued module.** `N` is the multiequalizer in `X.Modules` of the pushed
   forward pieces `Gᵢ := (uᵢ)_* Mᵢ` against
   `Hᵢⱼ := (uᵢ)_* (p₁)_* (Mⱼ restricted along p₂)`. The two maps
   `Gᵢ ⟶ Hᵢⱼ ⟵ Gⱼ` restrict to the overlap; the first one also applies
   `φᵢⱼ`. Sections of `N` over an open `O` of `X` are exactly the families
   `sₖ ∈ Γ(Mₖ, uₖ⁻¹ O)` with matching images in every `Hᵢⱼ`.
2. **Relation.** Matching images define a relation `Rel i j O` between
   sections of the pieces. The cocycle condition makes it transitive over
   opens inside the middle piece. Taking all three indices equal shows that
   over an open inside piece `k` the relation `Rel k k` is equality.
3. **Projections.** Over an open inside the range of `uₖ`, the projection of
   `N` to `Gₖ` is bijective on sections. So the map from the restriction of
   `N` along `uₖ` to `Mₖ` is an isomorphism. Composed with Mathlib's
   `restrictFunctorIsoPullback`, it gives `ψₖ`.
4. **Compatibility.** The multiequalizer condition, read on sections over the
   overlaps, gives the statement's compatibility of `ψᵢ`, `ψⱼ` and `φᵢⱼ`.

Except for the final theorem, all declarations below are in the namespace
`Langlands.Scheme.Modules.OpenCoverModuleGluing`. Throughout,
`p₁ = pullback.fst uᵢ uⱼ`, `p₂ = pullback.snd uᵢ uⱼ` and
`Vᵢ = (𝒰.f i).opensRange`. The file sets
`backward.isDefEq.respectTransparency false` and
`backward.defeqAttrib.useBackward true`, as `OpenCoverHomGluing` does.

## Restriction maps (section `Restriction`)

For a module `F` on a scheme: `res_res` says that two composable restriction
maps compose to any restriction map with the same ends (the opens form a
preorder, `presheaf_map_subsingleton`). `res_self` says that a restriction map
from an open to itself is the identity. `res_bijective` says that a
restriction map between equal opens is bijective.

## The gluing diagram

- `φr i j : Mᵢ.restrict p₁ ≅ Mⱼ.restrict p₂` is `φᵢⱼ` transported to
  restrictions with `restrictFunctorIsoPullback` on both sides.
- `G i := (pushforward uᵢ).obj Mᵢ` and
  `H i j := (pushforward uᵢ).obj ((pushforward p₁).obj (Mⱼ.restrict p₂))`.
- `aMap i j : G i ⟶ H i j` pushes forward along `uᵢ` the unit of
  `restrictAdjunction p₁` followed by `(pushforward p₁).map (φr i j).hom`.
- `overlapIso i j F` compares `(uⱼ)_* (p₂)_* F` with `(uᵢ)_* (p₁)_* F` by
  `pushforwardComp`, `pushforwardCongr pullback.condition.symm` and
  `pushforwardComp` again. `bMap i j : G j ⟶ H i j` pushes forward along `uⱼ`
  the unit of `restrictAdjunction p₂` and then applies `overlapIso`.
- `aMap_app` (by `rfl`) and `bMap_app` compute both maps on sections over an
  open `O` of `X`. `aMap` restricts a section of `Mᵢ` over `uᵢ⁻¹ O` to
  `p₁ ''ᵁ (p₁⁻¹ uᵢ⁻¹ O)` and applies `φr`. `bMap` is a restriction map of `Mⱼ`.
- `index` is the `MulticospanIndex (MulticospanShape.prod 𝒰.I₀) X.Modules`
  with left objects `G`, right objects `H p.1 p.2` and maps `aMap`, `bMap`.
  `glued := multiequalizer index`, `proj k := Multiequalizer.ι index k`, and
  `proj_condition` / `proj_condition_apply` record
  `proj i ≫ aMap i j = proj j ≫ bMap i j`, also on sections.
- `secFun O` is the sections functor `X.Modules ⥤ Type u` over `O`, the
  composite of `Scheme.Modules.toPresheaf X`, evaluation at `op O` and
  `forget Ab`. The file shows that it preserves limits.
- `proj_ext`: sections of `glued` over `O` with equal projections are equal.
  `proj_exists`: every family `s k : Γ(G k, O)` with
  `aMap i j (s i) = bMap i j (s j)` for all `i, j` is the family of
  projections of a section of `glued`. Both use
  `Types.isLimitEquivSections` for the image under `secFun O` of the limit
  cone. The case analysis on the walking multicospan follows Mathlib's
  `Concrete.multiequalizerEquivAux`.

## Bijectivity on a piece (section `Bijective`)

`preimage_fst_eq` identifies `p₁⁻¹ uᵢ⁻¹ O` with `p₂⁻¹ uⱼ⁻¹ O`. `le_image_fst`,
`image_snd_le` and `le_image_snd` compare the images of this open under `p₁`
and `p₂` with `uᵢ⁻¹ O` and `uⱼ⁻¹ O`. They use the ranges of the projections
(`opensRange_pullbackFst`, `opensRange_pullbackSnd`). Hence
`aMap_bijective`: `aMap i j` is bijective on sections over `O ≤ Vⱼ`, and
`bMap_bijective`: `bMap i j` is bijective on sections over `O ≤ Vᵢ`.

## The overlap relation (section `Relation`)

`Rel i j O x y` means `(aMap i j).app O x = (bMap i j).app O y` for
`x : Γ(G i, O)` and `y : Γ(G j, O)`.

- `rel_map`: the relation is preserved by restriction to a smaller open.
- `rel_restrict`: if `Rel i j O x y`, then on every open `A ≤ p₁⁻¹ uᵢ⁻¹ O`
  of the overlap, `φr` sends the restriction of `x` to the restriction of
  `y`. `rel_of` is the converse for `A = p₁⁻¹ uᵢ⁻¹ O`.
- `H_map_injective`, `preimage_inf_eq` and `rel_of_inf`: the relation over `O`
  holds once it holds over `O ⊓ Vᵢ ⊓ Vⱼ`, because both opens have the same
  preimage in the overlap.

## The cocycle condition on sections (section `Cocycle`)

These lemmas work in a general configuration: open immersions
`t₁ : W ⟶ Zab`, `q : W ⟶ Zbc`, `t₂ : W ⟶ Zac` and pairs of open immersions
from `Zab`, `Zbc`, `Zac` to `Ua`, `Ub`, `Uc`, with the three commutative squares
`h₀`, `h₁`, `h₂` of the statement. The cocycle equation `H` is written with
`squarePullbackIso` exactly as in the statement.

- `rHom b b' ψ` transports a morphism of pullbacks along open immersions to a
  morphism of restrictions. `φr_hom` says `(φr i j).hom = rHom p₁ p₂ (φ i j).hom`.
- `conj_eq'`: conjugating a pulled back morphism by the comparisons `compHom`
  agrees with iterated restriction via `restrictCompIso`.
- `restrict_cocycle`: `H` implies the corresponding equation between iterated
  restrictions, with each `squarePullbackIso` rewritten as `compHom ≫ inv
  compHom` (`squarePullbackIso_hom_compHom`).
- `rCI_hom_apply`, `rCI_inv_apply`: on sections, `restrictCompIso` and its
  inverse are restriction maps. `image_congr` transports images along an
  equality of morphisms.
- `section_cocycle` evaluates `restrict_cocycle` on sections over an open `U`
  of `W` (with `maxRecDepth 8000`). `section_trans` deduces that two relations
  `x ~ y` (through `φab`) and `y ~ z` (through `φbc`) over the images of `U`
  give `x ~ z` through `φac`.

## Wrappers for the kernel (section `Wrappers`)

`CompEq4 f₁ f₂ f₃ f₄ g₁ g₂` is the proposition `f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂`
and `CompEq2 f₁ f₂ g₁ g₂` is `f₁ ≫ f₂ = g₁ ≫ g₂`, in any category. `of_eq` and
`eq` convert in both directions by definitional unfolding. They play no
mathematical role. The statement's hypothesis and conclusion, retyped in this
file, differ from the statement's elaborated terms only in the auxiliary proofs
of the `HasPullback` instances. The two terms are definitionally equal, but the
kernel unfolds the composition `≫` before it compares the morphisms, and that
check exceeded the default heartbeat limit. A regular definition such as
`CompEq4` makes the kernel compare the morphisms first, so the check is quick.

`CocycleCondition 𝒰 M φ` is the statement's cocycle hypothesis, for all
`i j k`, with the six morphisms passed to `CompEq4`.

## Transitivity (section `Transitivity`)

`image_le_of_le_preimage`, `preimage_congr` and `rel_of'` (a form of `rel_of`
for an open given up to equality) are helpers. `rel_trans_aux` proves
transitivity of `Rel` in the general configuration above, for overlaps of the
cover. It uses `section_trans` and requires `p₁⁻¹ uₐ⁻¹ P ≤ t₂.opensRange` for
the overlap `(a, c)`. `rel_trans`: under `CocycleCondition`, if
`P ≤ V_b`, then `Rel a b P x y` and `Rel b c P y z` imply `Rel a c P x z`. It
instantiates `rel_trans_aux` with the triple overlap of the statement; the
range condition follows from `opensRange_pullbackSnd` and
`opensRange_pullbackFst`.

## Reflexivity and symmetry (section `Symmetry`)

Assume `CocycleCondition`.

- `rel_self`: for `P ≤ Vₖ`, every `x : Γ(G k, P)` satisfies `Rel k k P x x`.
  Let `y`, `z` be the sections with `bMap k k y = aMap k k x` and
  `bMap k k z = aMap k k y` (bijectivity of `bMap k k`). Transitivity gives
  `Rel k k P x z`. Bijectivity then gives `z = y` and `x = y`. This is the
  sections form of the remark that `φₖₖ = id` follows from the cocycle
  condition with `i = j = k`.
- `rel_self_iff`: for `P ≤ Vₖ`, `Rel k k P x y ↔ x = y`.
- `rel_symm`: for `P ≤ Vᵢ` and `P ≤ Vₖ`, `Rel k i P z s` implies
  `Rel i k P s z`.

## Projections on a piece (section `Projection`)

- `proj_app_injective`: for `O ≤ Vₖ`, `(proj k).app O` is injective. Use
  `proj_ext`, `proj_condition_apply` and bijectivity of `aMap i k`.
- `proj_app_surjective` (under `CocycleCondition`): for `O ≤ Vₖ` and
  `z : Γ(G k, O)`, choose `s i` with `aMap i k (s i) = bMap i k z`. The
  family `s` is compatible: by `rel_of_inf` it suffices to check
  `Rel i j` over `O ⊓ Vᵢ ⊓ Vⱼ`, which follows from `rel_map`, `rel_trans` and
  `rel_symm`. `proj_exists` gives `x` with projections `s`, and
  `rel_self_iff` gives `s k = z`. `proj_app_bijective` combines the two.
- `restrictProj k` is the composite of the restriction of `proj k` along `uₖ`
  with the counit of `restrictAdjunction uₖ` at `Mₖ`. `restrictProj_app_apply`
  computes it on sections. `restrictProj_app_bijective` shows it is bijective
  on every open `W` of `Uₖ`, since `uₖ ''ᵁ W ≤ Vₖ`. `restrictProj_isIso`
  concludes with `Scheme.Modules.Hom.isIso_iff_isIso_app`.

## Compatibility (section `Compatibility`)

- `pullback_compat_of_restrict`: for a commutative square `f ≫ a = g ≫ b` of
  open immersions, an equation
  `f*(ψa) ≫ e = (squarePullbackIso b f g a h N).hom ≫ g*(ψb)` follows from the
  same equation read on iterated restrictions. It uses
  `squarePullbackIso_hom_compHom`, `restrictCompIso_hom_app_comp` and the
  naturality of `restrictFunctorIsoPullback`.
- `hom_ext_apply` and `restrict_square_ext`: an equation of iterated
  restrictions around such a square can be checked on sections.
- `restrictProj_map_apply` and `restrict_compat`: the projections `restrictProj
  i` and `restrictProj j` are compatible with `φr i j` on iterated
  restrictions. This is `proj_condition_apply` read through `rel_restrict`.
- `pieceIso k : uₖ* glued ≅ Mₖ` is the inverse of
  `(restrictFunctorIsoPullback uₖ).app glued` followed by
  `asIso (restrictProj k)`. `restrictFunctorIsoPullback_hom_pieceIso_hom`
  recovers `restrictProj k`.
- `pieceIso_compat` (under `CocycleCondition`) is the statement's
  compatibility for `ψ = pieceIso`, in `CompEq2` form. It follows from
  `pullback_compat_of_restrict`, `φr_hom` and `restrict_compat`.

## Final assembly

`openCoverModuleGluing` takes the statement's data. It converts the hypothesis
`hφ` into `hφ' : CocycleCondition 𝒰 M φ` by
`(CompEq4.of_eq (hφ i j k) :)`. The type ascription without a type makes the
implicit morphisms of `of_eq` come from the statement's term, so the kernel
compares two `CompEq4` terms. It then returns
`⟨glued 𝒰 M φ, pieceIso 𝒰 M φ hφ', fun i j => CompEq2.eq (pieceIso_compat hφ' i j)⟩`.
Here the expected type assigns the implicit morphisms of `CompEq2.eq`.

## Source

- `stacks-glueing-sheaves-00AK-2026-10-31` (the source cited by the statement):
  Stacks Project, Sheaves on Spaces, Section 6.33 (tag 00AK), Glueing sheaves,
  Lemma 6.33.2 (first proof: sections are compatible families in
  `∏ᵢ 𝓕ᵢ(W ∩ Uᵢ)`) and Lemma 6.33.3 (the same construction for sheaves of
  `𝒪`-modules), and comments #7767–#7768 (`φᵢᵢ = id` follows from the cocycle
  condition).

The Lean route differs from Stacks in presentation only. It works with
pullbacks along the open immersions `uᵢ` and with Mathlib's fiber products
instead of intersections of opens. It builds the glued sheaf as a limit in
`X.Modules` instead of checking the sheaf axioms by hand. It also derives the
needed reflexivity and symmetry of the overlap relation on sections from the
cocycle condition.
