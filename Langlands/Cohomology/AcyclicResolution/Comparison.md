# Comparison of right resolutions with right derived functors

Author: Worker 61. The module imports my `Langlands.Cohomology.AcyclicResolution.Lift`
(`lift`, `comp_lift`, `homotopyOfComp`, `f_zero_comp_d`, `isLimitKernelFork`) and
Worker 3's `Langlands.Cohomology.AcyclicResolution.Statement` (only for the hypothesis
of `comparisonNatIso`). From Mathlib it uses `InjectiveResolution.isoRightDerivedObj`,
`InjectiveResolution.isoRightDerivedObj_inv_naturality`, `InjectiveResolution.desc`,
`Functor.mapHomotopy`, `Homotopy.homologyMap_eq`, `Functor.toRightDerivedZero`,
`InjectiveResolution.toRightDerivedZero'`, `InjectiveResolution.toRightDerivedZero_eq`,
`Functor.rightDerivedZeroIsoSelf`, `KernelFork.mapIsLimit` and
`HomologicalComplex.cyclesIsKernel`.

Composition `f ≫ g` is `f` followed by `g`. `(single₀ C).obj A`, written `A[0]` below, is
the cochain complex with `A` in degree zero and zero elsewhere. `Hⁿ(F K)` abbreviates
`(F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).obj K`, the
degree-`n` cohomology of `F` applied termwise to `K`.

## Setting

All declarations are in the namespace `Langlands.Cohomology.AcyclicResolution`. `C` is an
abelian category (`C : Type u`, `Category.{v} C`) with `[HasInjectiveResolutions C]`, `D`
is an abelian category (`D : Type u'`, `Category.{v'} D`), and `F : C ⥤ D` is an additive
functor. `F` is not assumed left exact unless stated. The declarations that do not involve
right derived functors (`comp_lift_id`, `toCyclesZero`, `toCyclesZero_iCycles`,
`cyclesZeroIso`, `cyclesZeroIso_hom`, `homologyZeroIso`) omit
`[HasInjectiveResolutions C]`.

A right resolution of `A` is a cochain map `ε : A[0] ⟶ K` with `[QuasiIso ε]`, where
`K : CochainComplex C ℕ`. Nothing is assumed about the terms of `K`. A lift of `ε` to an
injective resolution `I` of `A` is a cochain map `φ : K ⟶ I.cocomplex` with
`ε ≫ φ = I.ι`; such lifts are called augmentation-compatible below.

## The comparison map

- `comparison F I φ n : Hⁿ(F K) ⟶ (F.rightDerived n).obj A`, for an injective resolution
  `I` of `A`, any cochain map `φ : K ⟶ I.cocomplex` and `n : ℕ`, is the homology map of
  `F φ` followed by `(I.isoRightDerivedObj F n).inv`. No compatibility of `φ` is required
  to define it. This is the formula of Worker 3's statements: the comparison in
  `AcyclicResolutionComparisonStatement` and `ResolutionComparisonIndependenceStatement`,
  and `SmoothGodementComparison.comparisonMap`.
- `comp_lift_id ε I : ε ≫ lift ε (𝟙 A) I.ι = I.ι`: the lift of `ε` over the identity of
  `A` is augmentation-compatible.
- `comparison_eq F ε φ ψ hφ hψ n : comparison F I φ n = comparison F J ψ n` for two
  injective resolutions `I`, `J` of `A` and augmentation-compatible lifts `φ`, `ψ`. The
  comparison map therefore depends neither on the injective resolution nor on the lift.
  Proof: with `h := InjectiveResolution.desc (𝟙 A) J I`, `homotopyOfComp` gives a
  homotopy `φ ≫ h ≃ ψ` since both composites with `ε` are `J.ι`. Its image under `F` gives
  equal homology maps, and `isoRightDerivedObj_inv_naturality` for `h` over `𝟙 A` finishes.
- `resolutionComparison F ε n := comparison F (injectiveResolution A)
  (lift ε (𝟙 A) (injectiveResolution A).ι) n`, the comparison map for Mathlib's chosen
  injective resolution and the lift over the identity.
- `resolutionComparison_eq F ε I φ hφ n : resolutionComparison F ε n = comparison F I φ n`
  for every augmentation-compatible lift `φ` to every injective resolution `I`.

## Naturality

Let `η : B[0] ⟶ L` be another cochain map, `f : A ⟶ B`, and `g : K ⟶ L` a map of
resolutions over `f`, i.e. `hg : ε ≫ g = (single₀ C).map f ≫ η`.

- `comparison_naturality F ε η f g hg φ ψ hφ hψ n` (with a `reassoc` form): for an
  augmentation-compatible lift `φ` of `ε` to `I` and `ψ : L ⟶ J.cocomplex` with
  `η ≫ ψ = J.ι`,
  `(F.mapHomologicalComplex _ ⋙ homologyFunctor D _ n).map g ≫ comparison F J ψ n =
  comparison F I φ n ≫ (F.rightDerived n).map f`.
  Only `ε` is assumed to be a quasi-isomorphism. Proof: with
  `h := InjectiveResolution.desc f J I`, `homotopyOfComp` gives `g ≫ ψ ≃ φ ≫ h`, and
  `isoRightDerivedObj_inv_naturality` for `h` over `f` finishes.
- `resolutionComparison_naturality F ε η f g hg n` (with a `reassoc` form): the same for
  `resolutionComparison`, assuming also `[QuasiIso η]`.

## Degree zero

- `toCyclesZero F ε : F.obj A ⟶ ((F.mapHomologicalComplex _).obj K).cycles 0` is the lift
  of `F.map (ε.f 0)` to the degree-zero cycles, using `f_zero_comp_d`.
  `toCyclesZero_iCycles` (`simp`, with a `reassoc` form) says that its composite with the
  inclusion of cycles is `F.map (ε.f 0)`. `QuasiIso ε` is not needed.
- `toRightDerivedZero_eq_comparison F ε I φ hφ`: for any augmentation-compatible lift,
  `F.toRightDerivedZero.app A = toCyclesZero F ε ≫ homologyπ 0 ≫ comparison F I φ 0`.
  No exactness of `F` and no `QuasiIso ε` are needed. Proof: `toCyclesZero F ε` followed
  by the cycles map of `F φ` is Mathlib's `I.toRightDerivedZero' F`, and Mathlib's
  `InjectiveResolution.toRightDerivedZero_eq` expresses `F.toRightDerivedZero.app A`
  through it.

From here on `[QuasiIso ε]` and `[PreservesFiniteLimits F]` are assumed.

- `cyclesZeroIso F ε : F.obj A ≅ ((F.mapHomologicalComplex _).obj K).cycles 0` compares
  two kernels of `F.map (K.d 0 1)`. One is the image under `F` of the kernel fork
  `isLimitKernelFork ε` (`A` is the kernel of `K⁰ ⟶ K¹`), which `F` preserves because it
  preserves finite limits. The other is the cycles. `cyclesZeroIso_hom` says that its
  morphism is `toCyclesZero F ε`.
- `homologyZeroIso F ε : H⁰(F K) ≅ F.obj A` is the inverse of `cyclesZeroIso F ε`
  followed by `CochainComplex.isoHomologyπ₀`.
- `comparison_zero F ε I φ hφ`: for every augmentation-compatible lift,
  `comparison F I φ 0 = (homologyZeroIso F ε).hom ≫ F.rightDerivedZeroIsoSelf.inv.app A`.
  Here `F.rightDerivedZeroIsoSelf.inv` is `F.toRightDerivedZero`.

## The comparison transformation of a functorial resolution

Let `𝒦 : C ⥤ CochainComplex C ℕ` and `e : single₀ C ⟶ 𝒦` be a natural transformation with
`he : ∀ A, QuasiIso (e.app A)`, an explicit hypothesis.

- `comparisonNatTrans F 𝒦 e he n :
  𝒦 ⋙ F.mapHomologicalComplex _ ⋙ homologyFunctor D _ n ⟶ F.rightDerived n` has
  component `resolutionComparison F (e.app A) n` at `A`. Naturality is
  `resolutionComparison_naturality` with `g := 𝒦.map f`, which lies over `f` by the
  naturality of `e`.
- `comparisonNatTrans_app F 𝒦 e he A I φ hφ n`: the component at `A` equals
  `comparison F I φ n` for every injective resolution `I` of `A` and every
  `φ : 𝒦.obj A ⟶ I.cocomplex` with `e.app A ≫ φ = I.ι`.

With `[PreservesFiniteLimits F]`:

- `homologyZeroNatIso F 𝒦 e he : 𝒦 ⋙ F.mapHomologicalComplex _ ⋙ homologyFunctor D _ 0 ≅ F`
  has components `homologyZeroIso F (e.app A)`. Its naturality follows from that of
  `comparisonNatTrans` and `rightDerivedZeroIsoSelf` through `comparison_zero`.
- `comparisonNatTrans_zero`: `comparisonNatTrans F 𝒦 e he 0 =
  (homologyZeroNatIso F 𝒦 e he).hom ≫ F.rightDerivedZeroIsoSelf.inv`. The instance
  `isIso_comparisonNatTrans_zero` records that it is an isomorphism.
- `comparisonNatIso F 𝒦 e he hcomp hacyc n :
  𝒦 ⋙ F.mapHomologicalComplex _ ⋙ homologyFunctor D _ n ≅ F.rightDerived n` takes two
  hypotheses: `hcomp : AcyclicResolutionComparisonStatement.{u, v, u', v'}`, Worker 3's
  statement that acyclic resolutions compute right derived functors, and
  `hacyc : ∀ A i n, IsZero ((F.rightDerived (n + 1)).obj ((𝒦.obj A).X i))`, the
  `F`-acyclicity of every term. Under these, every component of `comparisonNatTrans` is an
  isomorphism, and `comparisonNatIso` is `asIso` of it (`comparisonNatIso_hom`, `simp`).
  The statement is not proved in this module, which keeps `hcomp` as a hypothesis. It is
  proved, at the same four universes, by the theorem `acyclicResolutionComparisonStatement`
  in `Langlands.Cohomology.AcyclicResolution.ComparisonProof`, which uses the long exact
  sequence of right derived functors in `Langlands.Cohomology.RightDerivedSequence`; this
  module imports neither. A caller can supply that theorem as `hcomp`; `hacyc` remains a
  separate input.

## Provenance and interpretation

Cartan–Eilenberg, *Homological Algebra* (1956), Chapter V, §3, printed p.83 (PDF page
105), defines for an acyclic right complex `X` over `A` "a natural homomorphism
(2) H(T(X,Y)) → RT(A,C)": with `X'` the injective resolution of `A` used to define
`RT(A,C)`, Proposition 1.1a gives a map `F : X → X'` over the identity of `A`, `T(F, G)`
induces (2), and "since, by 1.1 and 1.1a, F and G are unique up to a homotopy, it follows
that (2) is independent of the choice of F and G." For a covariant functor `T` of one
variable this is `comparison` with `comparison_eq`. In this module the independence also
covers the choice of the injective resolution, because Mathlib identifies `Rⁿ F A` with
the cohomology of `F I` for every injective resolution `I` through `isoRightDerivedObj`.
Cartan–Eilenberg call the homomorphism natural without stating the naturality separately.
`comparison_naturality` states it for maps of resolutions over a map `f : A ⟶ B`. Its
proof is the same homotopy argument applied to maps over `f`, which Proposition 1.1a also
covers.

Chapter V, §5, printed p.89 (PDF page 111), defines `τ⁰ : T → R⁰T` as the map induced by
the augmentation of an injective resolution. Proposition 5.1 says that `τ⁰` is an
equivalence if and only if `T` is left exact. Its proof notes that for left exact `T`
the sequence `0 → T(A) → T(X⁰) → T(X¹)` is exact, and that the kernel of the last map is
`H⁰T(X) = R⁰T(A)`. Mathlib's `F.toRightDerivedZero` is `τ⁰`, and
`F.rightDerivedZeroIsoSelf` is its inverse for left exact `F`.
`toRightDerivedZero_eq_comparison` and `comparison_zero` are internal results relating
`τ⁰` to the comparison map (2). They apply the argument of Proposition 5.1 to an arbitrary
acyclic right complex `K` instead of an injective resolution: `F` preserves the kernel
`A ⟶ K⁰ ⟶ K¹` (`cyclesZeroIso`), and the comparison map in degree zero is this
identification followed by `τ⁰`.

Cartan and Eilenberg work with modules. Grothendieck, *Sur quelques points d'algèbre
homologique* (1957), Section 2.3, printed p.143 (PDF page 25), transfers their Chapter V
to abelian categories in which the needed injective resolutions exist. Here this is
`[HasInjectiveResolutions C]`, which Mathlib's `Functor.rightDerived` requires.

The functorial transformation `comparisonNatTrans` and the conditional isomorphism
`comparisonNatIso` are internal packaging. They are the form needed to compare the
cohomology of a functorial resolution, such as the smooth Godement complex
(`Godement.smoothComplexFunctor` with `CokernelComplex.augmentationNat`), with right
derived functors. Its components are pinned to the comparison maps of all
augmentation-compatible lifts by `comparisonNatTrans_app`.

## Relation to other modules and tasks

- `comparison_eq` and `comparison_naturality` contain the mathematical content of Worker
  3's `ResolutionComparisonIndependenceStatement` and
  `ResolutionComparisonNaturalityStatement`. This module does not prove the statement
  propositions themselves, which quantify over all categories at fixed universes. They are
  proved, as direct applications of these two theorems, by
  `resolutionComparisonIndependenceStatement` in
  `Langlands.Cohomology.AcyclicResolution.IndependenceProof` and
  `resolutionComparisonNaturalityStatement` in
  `Langlands.Cohomology.AcyclicResolution.NaturalityProof`.
- `ResolutionLiftStatement`, `ResolutionComparisonTransformationStatement`,
  `AcyclicResolutionComparisonStatement` and `AcyclicResolutionEquivarianceStatement` are
  not addressed by this module. The first three are proved elsewhere:
  `resolutionLiftStatement` in `AcyclicResolution.LiftProof`,
  `resolutionComparisonTransformationStatement` in `AcyclicResolution.TransformationProof`
  and `acyclicResolutionComparisonStatement` in `AcyclicResolution.ComparisonProof`. The
  Library has no proof of `AcyclicResolutionEquivarianceStatement`.
- Worker 3's `SmoothGodementComparison.comparisonMap R G X I φ q` is `comparison` for
  `F := smoothSheafCompactSections R G X`, by definition.

## Scope

- One covariant additive functor of one variable and `ℕ`-indexed cochain complexes only.
- Invertibility in positive degrees is not proved in this module: `comparisonNatIso` takes
  `AcyclicResolutionComparisonStatement` as an explicit hypothesis, which the theorem
  `acyclicResolutionComparisonStatement` proves.
- `homologyZeroIso`, `comparison_zero`, `homologyZeroNatIso` and `comparisonNatTrans_zero`
  require `F` to preserve finite limits; `toRightDerivedZero_eq_comparison` does not.
