# The pushforward of the structure sheaf along a finite flat morphism of constant degree

Lean module: `Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardFreeCharts`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, the proof
of `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`. Let
`f : Y₁ ⟶ Y` be finite, flat and locally of finite presentation, with Mathlib degree
`f.finrank y = d` at every point (`Scheme.Hom.finrank`, Mathlib
`AlgebraicGeometry/Morphisms/FlatRank.lean`). This module proves that `f_* 𝒪_{Y₁}` has free
charts of rank `d` and that its formation commutes with arbitrary base change. These are
standard facts (a finite flat finitely presented algebra is a finite projective module, of
constant rank `d`, and pushforward along an affine morphism commutes with base change). They
are used in `FiniteFlatBaseChangeEuler`, whose finite flat base change step is applied to the
multiplication `[k]` of an abelian variety. All declarations are derived. None is a new
mathematical notion or a statement target.

The module feeds the Library criterion `AffineSectionsData`
(`Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion`). That criterion says: for
every base change of `f` to an affine `Spec R`, the `R`-module of global sections is finite,
projective, of constant stalk rank `r`, and compatible with further affine base change. Its
published consequences give local freeness of rank `r`
(`AffineSectionsData.isLocallyFreeOfRank`) and invertibility of the base-change morphism
`pushforwardBaseChange` (`AffineSectionsData.isIso_baseChange`).

## Declarations

- `isoSpec_hom_comp_specMap_structureRingHom f`: for an affine scheme `X` and
  `f : X ⟶ Spec R`, `X.isoSpec.hom ≫ Spec.map (structureRingHom f) = f`, where the Library's
  `structureRingHom f = (ΓSpecIso R).inv ≫ f.appTop`. Proof: Mathlib's
  `Scheme.isoSpec_hom_naturality` and `Scheme.isoSpec_Spec_hom`.
- `relativeGlobalSectionsStructureSheafLinearEquiv f`: the relative global sections of the
  structure sheaf along `f : X ⟶ Spec R` are the ring `Γ(X, ⊤)`. Its `R`-module structure is
  the algebra structure given by `structureRingHom f`. The underlying map is the identity,
  and all fields are proved by `rfl`.
- `affineSectionsData_structureSheaf f d hd`: under the hypotheses above,
  `AffineSectionsData f (structureSheaf Y₁) d`.
- `exists_freeChart_of_affineSectionsData`: affine sections data of rank `r` for `M` give,
  around every point of the base, an open `V` with
  `(f_* M)|_V ≅ SheafOfModules.free (ULift (Fin r))`. This repeats the proof of the Library's
  `AffineSectionsData.isLocallyFreeOfRank` but returns the chart itself. Choose an affine open
  `U ∋ y` and form the base change `XR` of `f` to `Spec Γ(U)`. The Library's
  `exists_freeNeighborhood_of_finite_projective_rankAtStalk` gives a free neighbourhood in
  `Spec Γ(U)`. It is transported through `openCartesianBaseChangeIso` and
  `freeChartOnOpensRange`.
- `exists_freeChart_pushforward_structureSheaf f d hd y`: the free chart of rank `d` of
  `f_* 𝒪_{Y₁}` around `y`.
- `pushforwardStructureSheafBaseChangeIso f d hd q φ q₁ hsq`: for every cartesian square
  `φ : Z₁ ⟶ Z`, `q₁ : Z₁ ⟶ Y₁`, `q : Z ⟶ Y`, `f` (that is, `IsPullback φ q₁ q f`),
  `φ_* 𝒪_{Z₁} ≅ q^*(f_* 𝒪_{Y₁})`. It is the inverse of the invertible morphism
  `pushforwardBaseChange q f φ q₁` (by `AffineSectionsData.isIso_baseChange`), composed with
  `pullbackUnitIso q₁`. No flatness of `q` is needed.

## Proof of `affineSectionsData_structureSheaf`

Let `x : Spec R ⟶ Y` and let `p : XR ⟶ Y₁`, `fR : XR ⟶ Spec R` be a cartesian square over `f`
and `x`. Finiteness, flatness and local finite presentation are stable under base change
(`MorphismProperty.of_isPullback`), so `fR` has them, and `XR` is affine. Let
`φ = structureRingHom fR`. By the first lemma, `Spec.map φ = XR.isoSpec.inv ≫ fR`, so
`Spec.map φ` is finite, flat and locally of finite presentation. By Mathlib's
`IsFinite.SpecMap_iff`, `Flat.SpecMap_iff` and `LocallyOfFinitePresentation.SpecMap_iff`, the
ring map `φ` is finite, flat and of finite presentation. With the algebra structure of `φ`:

- `Γ(XR, ⊤)` is a finite, flat and finitely presented `R`-module
  (`Module.FinitePresentation.of_finite_of_finitePresentation`), hence projective
  (`Module.Flat.projective_of_finitePresentation`).
- Its stalk rank at a prime `q` is `φ.finrank q` (by definition of `RingHom.finrank`). This
  equals `Scheme.Hom.finrank (Spec.map φ) q` (`Scheme.Hom.finrank_SpecMap_eq_finrank`), hence
  `Scheme.Hom.finrank fR q` (`Scheme.Hom.finrank_comp_left_of_isIso` and the first lemma),
  hence `f.finrank (x q)` (`Scheme.Hom.finrank_of_isPullback`), which is `d`.

The `R`-module in `AffineSectionsData` is the relative global sections of `p^* 𝒪_{Y₁}` along
`fR`. It is `R`-linearly equivalent to `Γ(XR, ⊤)` through `pullbackUnitIso p` and
`relativeGlobalSectionsStructureSheafLinearEquiv`, so it is finite, projective and of stalk
rank `d` (`Module.rankAtStalk_eq_of_equiv`). The last condition asks that the scalar
base-change map be invertible for every further base change along `Spec.map φ'`. The further
base change `XT` is affine, because `fR` is finite. `p^* 𝒪_{Y₁}` is quasi-coherent, being a
line bundle. The Library's `isIso_scalarSectionsBaseChangeMap_of_isPullback_affine` therefore
applies.

The module uses only Mathlib and published Library results.
