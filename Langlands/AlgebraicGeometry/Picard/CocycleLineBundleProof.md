# Line bundles glued from unit cocycles: proof

`Langlands.AlgebraicGeometry.Picard.cocycleLineBundle` proves the published
proposition `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleStatement.{u}`
from module `Langlands.AlgebraicGeometry.Picard.CocycleLineBundleStatement`.
Its type is exactly that proposition, with no outer hypotheses. The statement
pair and everything it imports are unchanged.

The module also exposes the consumer theorem
`Langlands.AlgebraicGeometry.Picard.exists_cocycleLineBundle`. It has the same
conclusion for a fixed scheme `X`, index type `ι : Type u`, family of opens
`T : ι → X.Opens` and units `g i j ∈ Γ(X, T i ⊓ T j)ˣ`, given the cover
hypothesis `hT : ⨆ i, T i = ⊤` and the cocycle identity `hg`, stated exactly
as in the target. It returns `N : LineBundle X` such that every compatible
family `a` (with `a i ∈ Γ(X, T i)` and `a i = g i j * a j` on `T i ⊓ T j`)
has a global section `t : GlobalSections N.obj` with
`T i ⊓ trivializationOpen N.obj t = X.basicOpen (a i)` for every `i`. One
bundle `N` serves every compatible family. `cocycleLineBundle` applies
`exists_cocycleLineBundle` to the universally quantified data.

The construction and auxiliary lemmas live in namespace
`Langlands.AlgebraicGeometry.Picard.CocycleGluing`. They are described below.

## Implemented proof

The bundle is built directly as a subsheaf of a product sheaf. Its sections
over `U` are the families `(b i)` with `b i ∈ Γ(X, U ⊓ T i)` that satisfy
`b i = g i j * b j` on every open contained in `U ⊓ T i ⊓ T j`. The proof does
not use torsors, Čech cohomology or sheafification.

### The sheaf of families

- `Fam T U` is the type `∀ i, Γ(X, U ⊓ T i)` of families of functions on the
  pieces of `U`. It carries the product additive group. `Γ(X, U)` acts on it
  componentwise by restriction and multiplication:
  `(r • b) i = r|_(U ⊓ T i) * b i` (`Fam.smul_apply`).
- `famRes T h` for `h : V ≤ U` restricts each component along
  `V ⊓ T i ≤ U ⊓ T i`. It commutes with the action (`famRes_smul`):
  `famRes (r • b) = r|_V • famRes b`.
- `famPresheaf T` is the resulting abelian presheaf, and `famModules T` is the
  presheaf of modules over `X.ringCatSheaf.obj` obtained by
  `PresheafOfModules.ofPresheaf` from `famRes_smul`.
- `famPresheaf_isSheaf`: the presheaf of families is a sheaf. The proof uses
  Mathlib's unique-gluing criterion for type-valued presheaves. Let `U k` be a
  family of opens and let compatible families `sf k ∈ Fam T (U k)` be given.
  For each `i`, the components `(sf k) i` are sections of `X.sheaf` on the
  opens `U k ⊓ T i`, which cover `(⨆ k, U k) ⊓ T i`. They agree on overlaps
  because `sf k` and `sf l` agree on `U k ⊓ U l`. So
  `X.sheaf.existsUnique_gluing'` glues them uniquely to a section on
  `(⨆ k, U k) ⊓ T i`. These glued sections form the glued family, and
  uniqueness holds componentwise.
- `famSheaf T : X.Modules` packages `famModules T` with this sheaf condition.

### The glued sheaf

- `IsCocycle g` is the cocycle identity of the target statement, verbatim.
  `cocycle_res` restates it on any open `W` that lies in all three pairwise
  overlaps: `g i j|_W * g j k|_W = g i k|_W`.
- `Compat g b` for `b : Fam T U` says the following. For all `i j` and every
  open `V` with `V ≤ U ⊓ T i` and `V ≤ U ⊓ T j`, `b i|_V = g i j|_V * b j|_V`.
  The condition is quantified over all such `V`, rather than imposed once on
  `U ⊓ T i ⊓ T j`. Closure under restriction is then immediate.
- `compat_zero`, `compat_add`, `compat_smul` and `compat_res`: the compatible
  families form a sub-presheaf of modules.
- `gluedSubmodule g : SheafOfModules.Submodule (famSheaf T)` is that
  sub-presheaf of modules (Mathlib's `Sheaf/Submodule`). Its field `isSheaf`
  says that membership is local. Let `b` be a family over `U` whose
  restrictions to a cover of `U` are compatible. To check `b i|_V =
  g i j|_V * b j|_V` on `V`, the lemma `eq_of_local` (equality of two
  functions that agree near each point, from `X.sheaf.eq_of_locally_eq'`)
  reduces the identity to the opens `V ⊓ W`. Here `W` ranges over the
  covering opens, and on `V ⊓ W` the identity is compatibility of
  `b|_W`.
- `glued g : X.Modules` is `(gluedSubmodule g).toSheafOfModules`.

Sections of `glued g` over `U` are the pairs `mk g b hb` of a family `b` and
a proof `hb : Compat g b`. Restriction and the action are componentwise
(`map_mk` and `smul_mk`, both by `rfl`). `comp g m i` is the `i`-th
component, and `eq_of_comp` is extensionality.

### Local generators

- `gen g i hV` for an open `V ≤ T i` is the family whose `j`-th component is
  `g j i` restricted to `V ⊓ T j`. In the statement's notation it is the local
  generator `e i` on `V`, written in the components of the other charts.
- `gen_compat`: if `g` is a cocycle then `gen g i hV` is compatible. The
  needed identity `g j i = g j k * g k i` is `cocycle_res` for the indices
  `j k i`.
- `genSec g hg i hV` is the corresponding section of `glued g` over `V`.
  `map_genSec` shows that restricting it to `W ≤ V` gives `genSec` over `W`.
- `smul_genSec_bijective`: for `V ≤ T i`, the map `r ↦ r • genSec g hg i hV`
  from `Γ(X, V)` to `Γ(glued g, V)` is bijective.
  - Injectivity: the `i`-th component of `r • genSec` is
    `r|_(V ⊓ T i) * g i i|`. The restriction of the unit `g i i` is a unit,
    so `r|_(V ⊓ T i)` is determined. Restricting back along
    `V ≤ V ⊓ T i` recovers `r`.
  - Surjectivity: for a section `m`, take `r` to be the restriction of
    `comp g m i` to `V`. Compatibility of `m` on `V ⊓ T j` gives
    `comp g m j = g j i * (comp g m i)|`, which is the `j`-th component of
    `r • genSec`.

  The proof uses only that `g i i` is a unit. It never needs `g i i = 1` or
  `g i j * g j i = 1`.

### Local rank one

`isLocallyFreeRankOne_glued` proves `IsLocallyFreeRankOne (glued g)` from
`hT` and the cocycle identity. Let `x` be a point. Since `⨆ i, T i = ⊤`, some
`T i` contains `x`. (If `ι` is empty, then `hT` forces `X` to be empty and
there is nothing to prove; the argument handles this case without a case
split.) Let `N'` be the restriction `(glued g).restrict (T i).ι` to the open
subscheme `T i`. Let `s` be the global section of `N'` given by `genSec` over
`(T i).ι ''ᵁ ⊤`.

- For an open `W` of `T i` and `a ∈ Γ(T i, W)`, the published
  `Langlands.SchemeModule.LineBundleDescent.sectionHom_app` and `map_genSec`
  give
  `(sectionHom N' s).app W a = ((T i).ι.appIso W).inv a • genSec` over
  `(T i).ι ''ᵁ W`.
- `((T i).ι.appIso W).inv` is bijective, and so is
  `r ↦ r • genSec` (`smul_genSec_bijective`). So every component of
  `sectionHom N' s` is bijective. Mathlib's
  `Scheme.Modules.Hom.isIso_iff_isIso_app` then makes `sectionHom N' s` an
  isomorphism `structureModule (T i) ≅ N'`.
- The inverse of this isomorphism is the required
  `N' ≅ SheafOfModules.unit (T i).toScheme.ringCatSheaf`, because
  `structureModule (T i)` is by definition the unit module.

### The global section of a compatible family

- `IsCompatibleFamily g a` is the compatibility hypothesis of the target
  statement, verbatim.
- `sec a : Fam T ⊤` restricts each `a i` from `T i` to `⊤ ⊓ T i`, and
  `sec_compat` shows that it is compatible.
- `globalSec g ha : GlobalSections (glued g)` is the corresponding section.
- `map_globalSec`: on any open `V ≤ T i`, the restriction of `globalSec g ha`
  is `a i|_V • genSec g hg i hV`. Componentwise this is
  `a j| = a i| * g j i|` on `V ⊓ T j`, which is the hypothesis `ha j i`
  restricted to `V ⊓ T j`.

### The generation open

`inf_trivializationOpen_globalSec` proves
`T i ⊓ trivializationOpen (glued g) (globalSec g ha) = X.basicOpen (a i)`.
Both inclusions use the published
`Langlands.SchemeModule.LineBundleDescent.trivializesOn_iff_bijective`. It
says that `TrivializesOn M s U` holds exactly when `(sectionHom M s).app V`
is bijective for every `V ≤ U`. By `sectionHom_app` and `map_globalSec`, on
an open `W ≤ T i` this component sends `r` to `(r * a i|_W) • genSec`.

- `⊆`: let `x ∈ T i` lie in some open `U` on which the section trivializes.
  The component on `U ⊓ T i` is surjective, so some `r` maps to `genSec`. That
  is, `(r * a i|) • genSec = 1 • genSec`. Injectivity in
  `smul_genSec_bijective` gives `r * a i| = 1`, so `a i` restricts to a unit
  on `U ⊓ T i`. Then `X.basicOpen_of_isUnit` and `Scheme.basicOpen_res` give
  `U ⊓ T i = (U ⊓ T i) ⊓ X.basicOpen (a i)`, and `x` lies there.
- `⊇`: `X.basicOpen (a i) ≤ T i`, and the section trivializes on
  `X.basicOpen (a i)`. For `W ≤ X.basicOpen (a i)`, the restriction of `a i`
  to `W` is a unit (`RingedSpace.isUnit_res_basicOpen`, restricted further to
  `W`). So `r ↦ (r * a i|_W) • genSec` is bijective. Injectivity cancels the
  unit; surjectivity multiplies the preimage under `smul_genSec_bijective`
  by its inverse. Since `trivializationOpen` is the supremum of the
  trivializing opens, `X.basicOpen (a i)` lies in it.

### Assembly

`exists_cocycleLineBundle` takes `N = ⟨glued g, isLocallyFreeRankOne_glued g
hT hg⟩`. Every compatible family `a` gets `t = globalSec g ha`, and
`inf_trivializationOpen_globalSec` gives the equality for each `i`. The
bundle depends only on `T` and `g`, so the quantifier order of the target is
respected.

## Scope

All the generality of the target is kept: arbitrary schemes, index types in
universe `u` (including empty ones), arbitrary open covers, unit families
subject only to the triple-overlap identity, and every compatible family,
including zero and non-units. No finiteness, affineness, nonemptiness,
quasi-compactness, separatedness or noetherianity hypothesis is used, and
neither `g i i = 1` nor `g i j * g j i = 1` is assumed or derived.

## Reused infrastructure

- Published Library: `Langlands.SchemeModule.LineBundleDescent.sectionHom_app`
  and `trivializesOn_iff_bijective` (module
  `Langlands.AlgebraicGeometry.Picard.LineBundleDescent`). Through that
  module's imports: `GlobalSections`, `structureModule`, `sectionHom`,
  `TrivializesOn` and `trivializationOpen`
  (`Langlands.AlgebraicGeometry.Modules.SectionLocus`), and `LineBundle` and
  `IsLocallyFreeRankOne` (`Langlands.AlgebraicGeometry.Picard.LineBundle`).
  The proof does not need the stalk criteria or the `unitEnd*` lemmas
  suggested in the task. On each `T i` the explicit generator reduces
  everything to bijectivity of multiplication maps on sections.
- Mathlib: `SheafOfModules.Submodule` and its `toSheafOfModules`,
  `PresheafOfModules.ofPresheaf`,
  `TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types`,
  `TopCat.Sheaf.existsUnique_gluing'`, `TopCat.Sheaf.eq_of_locally_eq'`,
  `Scheme.Modules.restrict` and `Scheme.Modules.Hom.isIso_iff_isIso_app`,
  `Scheme.Hom.appIso`, `Scheme.basicOpen_res`, `Scheme.basicOpen_of_isUnit`
  and `RingedSpace.isUnit_res_basicOpen`.

The file sets `backward.isDefEq.respectTransparency false`, as many Mathlib
algebraic-geometry files and Library modules do. It lets the rewriting lemmas
match sections of `structureModule X` and of `X.presheaf`, which are
definitionally equal. It affects elaboration only, not the statements.

## Source correspondence

The target is an internal, derived formulation; see the statement's
companion `CocycleLineBundleStatement.md`. In the registered Stacks snapshot
`stacks-norms-field-ample-descent-2026-10-26` (file `0BCX.html`, proof of
Lemma 31.18.2), units satisfying the cocycle condition "define an invertible
`O_Y`-module". The source obtains this module from Cohomology, Lemma 20.6.1
(registered snapshot `stacks-first-cohomology-invertible-20-6-2026-10-28`,
files `09NT.html` and `09NU.html`). That lemma's surjectivity proof builds the
module from an `O_X^*`-torsor as the sheafification of
`U ↦ (F(U) × O_X(U)) / O_X^*(U)`.

The proof here follows a different route. It realizes the glued module
concretely as compatible families of local coordinates inside
`∏ i O_X(U ∩ T_i)`, with no torsor and no sheafification. In the companion's
convention `e j = g i j * e i`, a section with local expressions `b i` (that
is, equal to `b i * e i` on `T i`) is recorded as the family `(b i)`. The
relation `b i = g i j * b j` is the statement's compatibility condition. The
local generator `e i` is the family `gen g i` with components `g j i`. The
computation of the generation open is the local argument sketched in the
statement companion: on `T i` the section morphism of `t` is multiplication
by `a i`, and that is an isomorphism exactly over `X.basicOpen (a i)`.

## Authorship

Worker 303 wrote the Lean proof and this companion.
