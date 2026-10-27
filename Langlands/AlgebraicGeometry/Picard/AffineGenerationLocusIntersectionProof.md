# Affineness of an affine open intersected with a line-bundle section locus

`Langlands.AlgebraicGeometry.Picard.affineGenerationLocusIntersection` proves
the published proposition
`Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionStatement.{u}`
from module `Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionStatement`.
The theorem's type is that proposition itself. It adds no outer hypotheses.
For every scheme `X : Scheme.{u}`, every `L : LineBundle X`, every
`s : Langlands.SchemeModule.GlobalSections L.obj`, and every open `U` with
`IsAffineOpen U`, it proves
`IsAffineOpen (U ⊓ Langlands.SchemeModule.trivializationOpen L.obj s)`.
The conclusion is affineness of the whole intersection, not the existence of
affine neighborhoods. The published statement pair and everything it imports
are unchanged.

The module also proves supporting lemmas in namespace `Langlands.SchemeModule`.
They are described below.

## Implemented proof

The proof does not use the symmetric-algebra quotient of the source.
It combines a local description of the section locus with Mathlib's affineness
criterion `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`.
That criterion (Stacks, tag 01QF) says the following. Let `Y` be an open and
`S` a subset of `Γ(X, Y)` that generates the unit ideal. If every
`X.basicOpen g` with `g ∈ S` is affine, then `Y` is affine.

### Endomorphisms of the structure module

For `φ : structureModule X ⟶ structureModule X` and an open `V`,
`unitEndCoefficient φ V` is the section `φ.app V 1` of `Γ(X, V)`.
The following lemmas hold for every scheme.

- `unitEndCoefficient_app`: on sections over `V`, `φ` is multiplication by
  this coefficient. The proof uses linearity of `φ.app V` over `Γ(X, V)`.
- `unitEnd_naturality` and `unitEndCoefficient_res`: `φ` commutes with
  restriction, so the coefficient on a smaller open is the restriction of
  the coefficient on a larger open.
- `unitEnd_app_isIso`: if the coefficient on `V` is a unit, then `φ.app V` is
  bijective, hence an isomorphism.
- `unitEnd_localUnit`: if `φ` induces an isomorphism on the stalk at `x`,
  then some open `V` containing `x` has a unit coefficient. Surjectivity on
  the stalk gives a germ mapping to the germ of `1`. Equality of germs then
  holds on a smaller neighborhood `V`. There `φ.app V a = 1`, that is,
  `a * unitEndCoefficient φ V = 1`.
- `unitEnd_restrict_isIso`: if the coefficient on `V` is a unit, then the
  restriction of `φ` to the open subscheme `V` is an isomorphism. The
  component of the restriction at an open `W` of `V` is `φ.app (V.ι ''ᵁ W)`.
  Its coefficient is a restriction of a unit, so it is an isomorphism by
  `unitEnd_app_isIso`.

The coefficient construction and the lemmas other than
`unitEndCoefficient_res` are imported from
[Modules.LineBundleFrameOpen](../Modules/LineBundleFrameOpen.md).
Integration exposed that module's existing private helpers and renamed
`unitEndValue` and `unitEnd_app` to `unitEndCoefficient` and
`unitEndCoefficient_app`, preserving their definitions and statements.
This module reuses those declarations and states `unitEndCoefficient_res`
separately from the restriction calculation already used there.

`unitEnd_stalkIso_iff_mem_basicOpen` then proves that `φ` induces an
isomorphism on the stalk at `x` if and only if
`x ∈ X.basicOpen (unitEndCoefficient φ ⊤)`.

- Forward direction: take the open `V` from `unitEnd_localUnit`. The
  coefficient on `V` is a unit, so `X.basicOpen_of_isUnit` shows that its
  basic open is all of `V`. That coefficient is the restriction of the global
  coefficient, so `Scheme.basicOpen_res` rewrites its basic open as
  `V ⊓ X.basicOpen (unitEndCoefficient φ ⊤)`. Hence `x` lies in the global
  basic open.
- Reverse direction: on `B = X.basicOpen (unitEndCoefficient φ ⊤)` the
  restricted coefficient is a unit (`RingedSpace.isUnit_res_basicOpen`). So
  the restriction of `φ` to `B` is an isomorphism by
  `unitEnd_restrict_isIso`. The published
  `Langlands.SchemeModule.isIso_stalk_restrict_iff`
  (`Modules.SectionLocusComparison`) transports this to the stalk of `φ`
  at `x`.

### The section locus on a trivializing open

`exists_inf_trivializationOpen_eq_basicOpen` takes a line bundle `L`, a
section `s`, an open `W`, and a trivialization
`e : L.obj.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf`.
It produces `a : Γ(X, W)` with
`W ⊓ trivializationOpen L.obj s = X.basicOpen a`.

The proof sets `ψ` to the endomorphism of the structure module of the open
subscheme `W` given by

```lean
(Scheme.Modules.restrictUnitIso W.ι).inv ≫
  (Scheme.Modules.restrictFunctor W.ι).map (sectionHom L.obj s) ≫ e.hom
```

The outer factors are isomorphisms. `isIso_stalk_restrict_iff` therefore shows
that `ψ` is a stalk isomorphism at `y : W` exactly when
`IsStalkFrame L.obj s (W.ι y)` holds. The published theorem
`Langlands.SchemeModule.lineBundle_stalkFrame_set_eq`
(`Modules.LineBundleFrameOpen`) identifies the set of stalk-frame points with
the whole `trivializationOpen L.obj s`. The previous lemma, applied on the
scheme `W`, identifies the stalk-isomorphism points of `ψ` with the basic open
of `unitEndCoefficient ψ ⊤`. Set `a` to the image of that coefficient under
`W.topIso.hom`. Then `Scheme.Opens.ι_image_basicOpen_topIso_inv` identifies
the image of that basic open in `X` with `X.basicOpen a`, and the two
inclusions follow elementwise.

### The affineness argument

Let `Y = U ⊓ trivializationOpen L.obj s`. Let `S ⊆ Γ(X, U)` be the set of
`g` such that `X.basicOpen g ⊓ trivializationOpen L.obj s` is affine.

1. `S` generates the unit ideal of `Γ(X, U)`. By `self_le_iSup_basicOpen_iff`
   for the affine open `U`, it suffices that the basic opens of elements of
   `S` cover `U`. Take `x ∈ U`. The `LineBundle` property gives an open `W`
   containing `x` and a trivialization `e` of `L.obj` on `W`. The previous
   lemma gives `a` with `W ⊓ trivializationOpen L.obj s = X.basicOpen a`.
   `IsAffineOpen.exists_basicOpen_le` gives `g ∈ Γ(X, U)` with
   `x ∈ X.basicOpen g ≤ W`. Since `X.basicOpen g ≤ W`, the open
   `X.basicOpen g ⊓ trivializationOpen L.obj s` equals the basic open of the
   restriction of `a` to `X.basicOpen g`, by `Scheme.basicOpen_res`. This is
   a basic open of the affine open `X.basicOpen g`, so it is affine
   (`IsAffineOpen.basicOpen` twice). Hence `g ∈ S` and `x ∈ X.basicOpen g`.
2. Let `ρ` be restriction from `U` to `Y`. Then `Ideal.span (ρ '' S) = ⊤`,
   because ideal maps preserve spans and the unit ideal.
3. For `g ∈ S`, `Scheme.basicOpen_res` gives
   `X.basicOpen (ρ g) = Y ⊓ X.basicOpen g`. Since `X.basicOpen g ≤ U`, this is
   `X.basicOpen g ⊓ trivializationOpen L.obj s`, which is affine because
   `g ∈ S`.

`isAffineOpen_of_isAffineOpen_basicOpen` applied to `Y` and `ρ '' S` then
shows that `Y` is affine.

The argument applies to every scheme, including the empty scheme and
non-reduced schemes. It uses no separatedness, quasi-compactness,
noetherianity, or quasi-coherence hypothesis. Local rank one is used only
through the `LineBundle` property. The locus is the actual maximal
`trivializationOpen`, used through the published
`lineBundle_stalkFrame_set_eq`. No residue comparison, tensor-power, or
ampleness result is used.

## Provenance

The target is Stacks Project Lemma 28.27.4, tag 01PV, in the registered
retained snapshot `stacks-ampleness-tensor-isomorphism-2026-10-24`
(`01PR.html`): for an invertible module `L` on a scheme `X`, a section `s`,
and an affine open `U`, the intersection `U ∩ X_s` is affine. The source
proves this through the quotient `Sym_R(N)/(s - 1)` of the symmetric algebra
of an invertible module `N` over `R`. The Lean proof uses a different
route, which the task contract allows. It uses the local fact that, on a
trivializing open, `X_s` is the basic open of the coordinate of `s`. Then it
applies the affineness criterion of Stacks tag 01QF, which Mathlib provides
as `isAffineOpen_of_isAffineOpen_basicOpen`. The source defines `X_s` through
the nonvanishing of `s` in the fiber. The Library locus is the maximal open on
which `s` trivializes `L`. The proof works with the Library locus directly,
through stalk frames, and does not need
`Langlands.SchemeModule.lineBundleResidueOpenComparison`.
