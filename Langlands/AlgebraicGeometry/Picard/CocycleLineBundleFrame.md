# Module sheaves with local frames as glued line bundles

Module `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame`, namespace
`Langlands.AlgebraicGeometry.Picard.CocycleGluing`.

This module shows that a sheaf of modules with local frames on a cover is
isomorphic to the line bundle `glued g` of
`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof` built from the
transition functions of the frames. Fix a scheme `X`, a sheaf of modules
`M : X.Modules`, an index type `ι : Type u`, a family of opens
`T : ι → X.Opens`, and sections `e i : Γ(M, T i)`. Assume that each `e i` is a
frame on `T i`, and that `g : ∀ i j, (Γ(X, T i ⊓ T j))ˣ` gives the transition
functions of the frames:

```
(he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i))
(htrans : IsTransition e g)   -- e j = g i j • e i on T i ⊓ T j
```

The main definition is

```
noncomputable def frameIso (hT : (⨆ i, T i) = ⊤) : M ≅ glued g
```

It is a specific morphism, not one chosen by `Classical.choice`. Its forward
map `toGlued he htrans` sends a section of `M` to its family of coefficients
with respect to the frames `e i`. It sends `e i` to the local generator
`genSec g i`.

## Conventions

`Scheme.Modules.IsFrameOn s U` (from the ported Anthropic FLT library) says that
for every open `W ≤ U`, the map `r ↦ r • s|W` from `Γ(X, W)` to `Γ(M, W)` is a
bijection.

The conventions for `glued g` are those of `CocycleLineBundleProof`. A section
of `glued g` over `U` is a family `(b i)` with `b i ∈ Γ(X, U ⊓ T i)` and
`b i = g i j * b j` on every open inside `U ⊓ T i ⊓ T j`. `comp g m i` is the
`i`-th component of a section `m`, and `mk g b hb` is the section with
components `b`. `genSec g hg i hV` is the local generator over an open
`V ≤ T i`; its `j`-th component is `g j i` restricted.

The transition relation `IsTransition e g` uses the same orientation as the
hypothesis `htrans` of the FLT theorem
`Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame`:

```
def IsTransition (e : ∀ i, Γ(M, T i)) (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) : Prop :=
  ∀ i j, e j|(T i ⊓ T j) = g i j • e i|(T i ⊓ T j)
```

(written in Lean with `M.presheaf.map (homOfLE inf_le_right).op` and
`M.presheaf.map (homOfLE inf_le_left).op`). With this orientation the
coefficient family of a section satisfies the gluing relation of `glued g`:
if `s = b i • e i = b j • e j` on an overlap, then `b i = g i j * b j`.

## Declarations

### Restriction in `M`

- `mres_mres`: restricting from `U` to `V` and then to `W` is restricting from
  `U` to `W`.
- `mres_self`: restricting from `U` to `U` is the identity.

### Coefficients with respect to a frame

Fix a frame `s` on `U` (`hs : Scheme.Modules.IsFrameOn s U`).

- `frameCoeff hs hW x : Γ(X, W)`, for `W ≤ U` and `x : Γ(M, W)`, is the unique
  `r` with `r • s|W = x`. It is the inverse of the bijection given by `hs`
  (`Equiv.ofBijective`).
- `frameCoeff_smul_frame`: `frameCoeff hs hW x • s|W = x`.
- `frameCoeff_eq`: if `r • s|W = x`, then `frameCoeff hs hW x = r`.
- `frameCoeff_add`, `frameCoeff_smul` (`frameCoeff hs hW (r • x) =
  r * frameCoeff hs hW x`), `frameCoeff_frame` (the coefficient of `s|W`
  is `1`).
- `res_frameCoeff`: restricting the coefficient of `x` to `W' ≤ W` gives the
  coefficient of the restriction of `x`.
- `frameCoeff_mul_frameCoeff`: for frames `s` on `U` and `t` on `U'` and
  `W ≤ U ⊓ U'`, the coefficient of `t|W` with respect to `s` times the
  coefficient of `s|W` with respect to `t` is `1`.

### Transition functions

- `IsTransition e g`, displayed above.
- `IsTransition.res`: the transition relation restricted to any open
  `V ≤ T i ⊓ T j`: `e j|V = (g i j)|V • e i|V`.
- `isCocycle_of_isTransition he htrans : IsCocycle g`: the transition
  functions of a family of frames satisfy the cocycle identity
  `g i j * g j k = g i k` on triple overlaps (the restrictions are left out
  here). Proof: on `T i ⊓ T j ⊓ T k`, `e k = g j k • g i j • e i` and
  `e k = g i k • e i`; since `e i` is a frame, the coefficients agree.
- `IsTransition.unique he`: if `IsTransition e g` and `IsTransition e g'`,
  then `g = g'`.
- `frameCocycle e he i j : (Γ(X, T i ⊓ T j))ˣ` constructs the transition
  functions from the frames: its value is the coefficient of `e j` with respect
  to `e i` on `T i ⊓ T j`, and its inverse is the coefficient of `e i` with
  respect to `e j` (they are inverse by `frameCoeff_mul_frameCoeff`).
- `isTransition_frameCocycle he : IsTransition e (frameCocycle e he)`.

### The morphism to the glued sheaf

- `frameFam he s : Fam T U`, for `s : Γ(M, U)`, is the family whose `i`-th
  member is the coefficient of `s|(U ⊓ T i)` with respect to `e i`
  (`frameFam_apply`). Lemmas: `res_frameFam`, `frameFam_add`, `frameFam_smul`,
  and `famRes_frameFam` (it commutes with restriction).
- `compat_frameFam he htrans s : Compat g (frameFam he s)`: the coefficient
  family satisfies the gluing relation of `glued g`. Proof: on an open
  `V ≤ U ⊓ T i ⊓ T j`, `(g i j * b j) • e i = b j • e j = s`, so
  `b i = g i j * b j` by `frameCoeff_eq`.
- `toGlued he htrans : M ⟶ glued g` sends `s` over `U` to
  `mk g (frameFam he s) _`. Its additivity and `Γ(X, U)`-linearity are
  `frameFam_add` and `frameFam_smul`, and its naturality is
  `famRes_frameFam`. It needs neither the cocycle identity nor a cover
  hypothesis.
- `comp_toGlued_app`: the `i`-th component of `toGlued he htrans s` is the
  coefficient of `s|(U ⊓ T i)` with respect to `e i` (by `rfl`).
- `toGlued_app_frame he htrans hg i hV`: for a cocycle `g` (any proof `hg`)
  and `V ≤ T i`, `toGlued` sends `e i|V` to `genSec g hg i hV`. Proof: the
  `j`-th component of `genSec g hg i hV` is `g j i` restricted, and
  `IsTransition.res` gives `e i = g j i • e j` on `V ⊓ T j`.
- `toGlued_app_frame_self`: the case `V = T i`, where `e i` itself goes to
  `genSec g hg i le_rfl`.

### The isomorphism

- `isIso_toGlued he htrans hT`: if `⨆ i, T i = ⊤`, then `toGlued he htrans` is
  an isomorphism. Proof: the criterion
  `Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top` from the ported Anthropic
  FLT library, applied to the frames `e i` of `M` and
  `genSec g _ i le_rfl` of `glued g` on the cover `T`. The cocycle proof is
  `isCocycle_of_isTransition`. The generators are frames by `map_genSec` and
  `smul_genSec_bijective`, and they correspond under `toGlued` by
  `toGlued_app_frame_self`.
- `frameIso he htrans hT := asIso (toGlued he htrans)`, displayed above.
  Lemma `frameIso_hom` (`(frameIso he htrans hT).hom = toGlued he htrans`, by
  `rfl`).
- `comp_frameIso_hom_app`: the component formula, as in `comp_toGlued_app`.
- `frameIso_hom_app_frame`: `frameIso` sends `e i|V` to `genSec g hg i hV` for
  every `V ≤ T i`.
- `frameIso_inv_app_genSec`: the inverse sends `genSec g hg i hV` to `e i|V`.
- `eq_comp_smul_genSec g hg i hV m`: over `V ≤ T i`, every section `m` of
  `glued g` is `(comp g m i)|V • genSec g hg i hV`. This lemma concerns only
  `glued g`; it uses the gluing relation of `m` between the indices `j` and
  `i`.
- `frameIso_inv_app`: the inverse of `frameIso` over `V ≤ T i` sends a section
  `m` of `glued g` to `(comp g m i)|V • e i|V`. Proof: `eq_comp_smul_genSec`,
  linearity of the inverse, and `frameIso_inv_app_genSec`.

## Related results

The FLT theorem `Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame`
(module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame`)
states, for the different gluing construction `Scheme.Modules.glueOfCocycle`
of a `Scheme.Modules.UnitCocycle`, that an isomorphism with the same frame
property exists. This module works with `CocycleGluing.glued` instead. It
gives a specified isomorphism, and its component and inverse formulas hold
over every open, not only on the opens `T i`. It also constructs the
transition functions from the frames (`frameCocycle`) and proves that they
form a cocycle.

## Sources and provenance

Provenance: derived. Source: Stacks Project, Cohomology of Sheaves, Lemma
`cohomology-lemma-h1-invertible` (tag 09NU), in the registered folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, file `cohomology.tex`,
lines 405-474 (tag map: `tags.txt` line 12227). The lemma identifies
`H¹(X, O_X^*)` with `Pic(X)`. Its proof uses the sheaf `L^*` of local
generators of an invertible sheaf `L`: the sections `s` over `U` for which
`O_U → L_U`, `f ↦ f s`, is an isomorphism. It notes (lines 425-427): "if
s, s' ∈ L^*(U) then there exists a unique f ∈ O_X^*(U) such that fs = s'".
The gauge module `CocycleLineBundleGauge` and the pullback module
`CocycleLineBundlePullback` cite the same lemma.

Correspondence with the source. The predicate `Scheme.Modules.IsFrameOn s U`
is the condition that `s` lies in `L^*(U)`, stated through sections over all
opens inside `U`. `frameCocycle` and `IsTransition.unique` are the quoted
sentence applied to `e i|(T i ⊓ T j)` and `e j|(T i ⊓ T j)`: there is a unique
unit `g i j` with `g i j • e i = e j`. `isCocycle_of_isTransition` is the
resulting cocycle identity, which gives the class of `L` in `H¹(X, O_X^*)`
under the map of the source. `frameIso` proves, for the sheaves of this
project, that the module is recovered from these transition functions up to
isomorphism: any sheaf of modules with frames on a cover is isomorphic to
`glued g`. This module states only the sheaf-level isomorphism and its
formulas; it says nothing about cohomology classes or the group structure of
`Pic(X)`.

The Lean proof is this module's own construction; the source omits most
details. The morphism takes frame coefficients, so no gluing of sections in
`M` is needed. It is shown to be an isomorphism by the FLT frame criterion
`isIso_of_isFrameOn_of_iSup_eq_top`.

Differences from the source. The source works with an arbitrary invertible
module on a locally ringed space and with all local generators at once. This
module works on a scheme with one chosen frame `e i` on each open of a family
`T`. The morphism `toGlued` exists for every family `T` and every `g` with
`IsTransition e g`; the cover hypothesis `⨆ i, T i = ⊤` is used only for the
isomorphism.
