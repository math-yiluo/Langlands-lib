# Čech cochains compute actual derived `R`-module sections

Author: Worker 958.

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution`. It defines the `ℕ`-indexed complex of
`R`-modules formed by the alternating Čech cochains of the Anthropic FLT port and proves that,
for `π : X ⟶ Spec R` separated and `M` quasi-coherent, its image in the derived category of
`R`-modules is isomorphic to the actual right derived complex of `R`-module global sections
at `M`:

```lean
def cechCochainComplex {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
    (𝒰 : X.OrderedAffineCover) (M : X.Modules) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of R ((OModulePresheaf.ofModules π M).cochain 𝒰 i))
    (fun i => ModuleCat.ofHom ((OModulePresheaf.ofModules π M).d 𝒰 i)) (fun i => by
      apply ModuleCat.hom_ext
      exact OModulePresheaf.d_comp_d _ 𝒰 i)

theorem nonempty_cechCochainComplex_iso (R : CommRingCat.{u}) (X : Scheme.{u})
    (π : X ⟶ Spec R) [IsSeparated π] (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] :
    Nonempty (DerivedCategory.Q.obj ((cechCochainComplex π 𝒰 M).extend
        ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex
        (DerivedSections.relativeGlobalSections π)).obj M))
```

The theorem is stated with the local instance `HasDerivedCategory.standard`.
`DerivedSections.relativeGlobalSections π : X.Modules ⥤ ModuleCat R` is the Library's functor of
global sections regarded as `R`-modules through `π`, and `DerivedPlus.derivedComplex F` is the
Library's bounded-below right derived complex of `F`, here included in the unbounded derived
category by `DerivedCategory.Plus.ι`. The left side is the Čech complex, extended by zero to
negative degrees (`ComplexShape.embeddingUpNat`), in `DerivedCategory (ModuleCat R)`.

## Imported interface

From the Library's port of the Anthropic FLT source, module
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (namespace
`AlgebraicGeometry.OModulePresheaf`): for `F : OModulePresheaf π`, `F.cochain 𝒰 i` is the type
`∀ s : 𝒰.Idx i, F.obj (𝒰.inter s)` of alternating `i`-cochains and
`F.d 𝒰 i : F.cochain 𝒰 i →ₗ[R] F.cochain 𝒰 (i + 1)` is the alternating Čech differential, with
`d_apply`: `F.d 𝒰 i c s = ∑ j : Fin (i + 2), (-1)^j • F.res _ (c (𝒰.face s j))`. From
`...Def_AlgebraicGeometry_OModulePresheafOfModules`: `OModulePresheaf.ofModules π M` has
objects `Γ(M, U)`, the `R`-module structure through `π`, and restriction maps of `M`. From
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d`:
`d_comp_d : F.d 𝒰 (i + 1) ∘ₗ F.d 𝒰 i = 0`.

`cechCochainComplex π 𝒰 M` is, term for term, the complex written inline in the Library's
`Langlands.AlgebraicGeometry.Modules.NoetherianCechPerfectRepresentativeStatement` (where
`R : Type u` and `π : X ⟶ Spec (.of R)`); the definition gives that complex a name so that the
comparison above can be combined with statements about it.

## Declarations

- `isIso_derivedResolutionComparison F ε hK` (section `Abstract`): for an additive, left exact
  functor `F : C ⥤ D` between abelian categories with derived categories, `C` with enough
  injectives, and a right resolution `ε : A[0] ⟶ K` (`QuasiIso ε`) of `A` by objects with
  `(F.rightDerived (n + 1)).obj (K.X i)` zero for all `i, n`, the Library's canonical
  comparison `AcyclicResolution.derivedResolutionComparison F ε` (from the image of `F K` to
  the right derived complex of `F` at `A`) is an isomorphism. Proof: let `I` be Mathlib's
  chosen injective resolution of `A` and `φ = lift ε (𝟙 A) I.ι : K ⟶ I.cocomplex`. The
  Library's `AcyclicComparison.quasiIso_map` (with `comp_lift_id`) shows that `F` applied to
  `φ` is a quasi-isomorphism; it stays one after extension to `ℤ`
  (`HomologicalComplex.quasiIso_extendMap_iff`) and is transported along the Library's
  `extendMapIso` (extension commutes with applying `F`). So
  `(derivedResolutionFunctor F).map φ` is an isomorphism
  (`DerivedCategory.isIso_Q_map_iff_quasiIso`), and the comparison is this map followed by the
  inverse of the Library's `derivedResolutionIso F I`.
- `inter_le_cechOpen`, `cechOpen_le_inter`: `𝒰.inter s` and `cechOpen 𝒰 s ⊤` (from
  `CechResolution.Exact`) are equal opens; `map_map_of_le_of_le` says restricting along both
  inclusions is the identity on sections.
- `toCochainFun 𝒰 M x s`: for a global section `x` of `cechTerm 𝒰 M p`, its `s`-component
  (`toSec`, `cr` of `CechResolution.Exact`) as a section of `M` over `𝒰.inter s`. It is
  bijective onto all families (`toCochainFun_injective`, `toCochainFun_surjective`, from
  `toSec_injective`, `toSec_surjective`), additive (`toCochainFun_add`), compatible with the
  `Γ(X, ⊤)`-action through restriction of scalars to `𝒰.inter s` (`toCochainFun_smul`), and
  carries the global sections of `cechD 𝒰 M p` to the alternating sum of restricted faces
  (`toCochainFun_cechD`, from `toSec_cechD`).
- `relativeGlobalSections_smul`, `relativeGlobalSections_map_apply`: the `R`-action on
  `(relativeGlobalSections π).obj N` is the `Γ(X, ⊤)`-action through
  `DerivedSections.structureRingHom π`, and the functor acts on maps by `f.app ⊤` (both `rfl`).
  `structureRingHom_comp`: the ring map from `R` to `Γ(X, 𝒰.inter s)` through
  `structureRingHom π` and restriction equals `(Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ _ _`, the
  ring map defining the `R`-module structure of `OModulePresheaf.ofModules π M`.
- `toCochain π 𝒰 M p`: `toCochainFun` as an `R`-linear map from
  `(relativeGlobalSections π).obj (cechTerm 𝒰 M p)` to
  `(OModulePresheaf.ofModules π M).cochain 𝒰 p` (linearity by `toCochainFun_smul` and
  `structureRingHom_comp`). `d_toCochainFun`: `toCochainFun` intertwines `cechD 𝒰 M p` on global
  sections with `OModulePresheaf.d` (compare `toCochainFun_cechD` with `d_apply`).
- `sectionsIso π 𝒰 M p`: the resulting isomorphism of `R`-modules (`LinearEquiv.ofBijective`).
- `cechCochainComplex π 𝒰 M`: the complex displayed above.
- `sectionsComplexIso π 𝒰 M`: the isomorphism of `ℕ`-indexed complexes of `R`-modules from
  `relativeGlobalSections π` applied to `cechComplex 𝒰 M` to `cechCochainComplex π 𝒰 M`, with
  components `sectionsIso` (`HomologicalComplex.Hom.isoOfComponents`; the squares commute by
  `d_toCochainFun`).
- `nonempty_cechCochainComplex_iso`: the main theorem. Proof: `cechAug 𝒰 M` is a
  quasi-isomorphism (`quasiIso_cechAug` of `CechResolution.Exact`) and the terms of
  `cechComplex 𝒰 M` are acyclic for `relativeGlobalSections π`
  (`isZero_relativeCohomology_cechTerm` of `CechResolution.Acyclic`, using `IsSeparated π`
  and quasi-coherence of `M`), so `isIso_derivedResolutionComparison` makes the canonical
  comparison an isomorphism. Composing it with `Q` of the extension of
  `sectionsComplexIso.symm` and of `extendMapIso` gives the isomorphism.

## Provenance

The theorem is Stacks Project, Cohomology of Schemes, Lemma
`lemma-cech-cohomology-quasi-coherent` (tag 01XD), in the form of an isomorphism in the derived
category for the alternating Čech complex of a finite ordered affine cover of a scheme separated
over an affine base (where all finite intersections are affine, Lemma `lemma-affine-diagonal`,
tag 0BDX). Source: `coherent.tex` of the registered folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`), lines 219 and 246. Stacks deduces 01XD from the
Čech-to-cohomology spectral sequence (Cohomology of Sheaves, Lemma
`lemma-cech-spectral-sequence-application`, tag 01ET, `cohomology.tex` line 1574) and states it
on cohomology groups; the Lean proof instead uses the sheafified Čech resolution (Stacks, Cohomology of Sheaves, Lemma `lemma-covering-resolution`, tag 02FU,
`cohomology.tex` line 4571) and the Library's comparison of acyclic resolutions with derived
functors. The definition `cechCochainComplex` is the ordered Čech complex
`Č_ord^•(𝒰, M)` of Stacks, Cohomology of Sheaves, Definition
`definition-ordered-cech-complex` (tag 01FI; cochains and differential at `cohomology.tex`
lines 4121–4150, definition at line 4152), taken in `R`-modules, for the finite totally ordered
cover `𝒰`; it is built from the FLT port's `cochain` and `d` (Anthropic FLT source, registered
as `anthropic-flt-complete-lean-source-6e837e75`,
`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean` lines 126–134) exactly as in
the Library's `NoetherianCechPerfectRepresentativeStatement`. The Lean proofs are this
module's own.
