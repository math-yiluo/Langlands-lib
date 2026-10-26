# Lifting right resolutions into complexes of injective objects

Author: Worker 61. The module imports only Mathlib. It uses
`Injective.factorThru`, `ShortComplex.Exact.descToInjective`,
`CochainComplex.mkHom`, `Homotopy.mkCoinductive`, `Homotopy.equivSubZero`,
`quasiIsoAt_iff_exactAt`, `HomologicalComplex.exactAt_succ_single_obj`,
`HomologicalComplex.cyclesIsKernel`, `CochainComplex.isoHomologyπ₀`,
`HomologicalComplex.singleObjHomologySelfIso` and `isoOfQuasiIsoAt`. The
constructions follow Mathlib's `InjectiveResolution.desc` and
`InjectiveResolution.descHomotopyZero`.

Composition `f ≫ g` is `f` followed by `g`. `(single₀ C).obj A`, written `A[0]`
below, is the cochain complex with `A` in degree zero and zero elsewhere.

## Setting

All declarations are in the namespace `Langlands.Cohomology.AcyclicResolution`.
`C` is an abelian category (`Category.{v} C`, `C : Type u`), `A` an object of
`C`, `K : CochainComplex C ℕ` and `ε : A[0] ⟶ K` a cochain map with
`[QuasiIso ε]`. This is a right resolution in the sense of Worker 3's
`Langlands.Cohomology.AcyclicResolution.Statement`. Nothing is assumed about the
terms of `K`.

## Exactness of a right resolution

- `exactAt_succ ε n : K.ExactAt (n + 1)`: `K` is exact in every positive degree,
  because `A[0]` is.
- `exact_succ ε n`: the short complex `Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²` is exact.
- `f_zero_comp_d ε : ε.f 0 ≫ K.d 0 1 = 0` (with an `_assoc` form). This holds for
  every cochain map out of `A[0]`; it does not use `QuasiIso`.
- `kernelFork ε` is the kernel fork `A ⟶ K⁰` of `K.d 0 1`, and
  `isLimitKernelFork ε : IsLimit (kernelFork ε)` says it is a kernel. The proof
  identifies `ε.f 0` with the inclusion of the degree-0 cycles of `K` through
  the isomorphism `H⁰(A[0]) ≅ H⁰(K)` induced by `ε`.
- `exact₀ ε`: the short complex `A ⟶ K⁰ ⟶ K¹` is exact.
- Instance `mono_f_zero`: `ε.f 0` is a monomorphism.

## The lift

Here `L : CochainComplex C ℕ` has injective terms (`[∀ n, Injective (L.X n)]`),
`f : A ⟶ B` is a morphism of `C`, and `η : B[0] ⟶ L` is a cochain map. Nothing
is assumed about the exactness of `L`. An injective resolution `J` of `B` gives
such data with `L := J.cocomplex` and `η := J.ι`.

- `liftFZero ε f η : K.X 0 ⟶ L.X 0` extends `(((single₀ C).map f) ≫ η).f 0`
  along the monomorphism `ε.f 0` into the injective object `L.X 0`
  (`f_zero_comp_liftFZero`, also as `_assoc` and `simp`).
- `liftFOne ε f η : K.X 1 ⟶ L.X 1` extends `liftFZero ε f η ≫ L.d 0 1` along
  `K.d 0 1`, using `exact₀`. `d_comp_liftFOne` records the commuting square.
- `liftFSucc ε L n g g' w` is the inductive step: given components `g` in degree
  `n` and `g'` in degree `n + 1` with `K.d n (n + 1) ≫ g' = g ≫ L.d n (n + 1)`,
  it extends `g' ≫ L.d (n + 1) (n + 2)` along `K.d (n + 1) (n + 2)` using
  `exact_succ`. It returns the new component together with its commuting square.
- `lift ε f η : K ⟶ L` is the cochain map assembled from these components by
  `CochainComplex.mkHom`.
- `comp_lift ε f η : ε ≫ lift ε f η = (single₀ C).map f ≫ η`. That is, the lift
  lies over `f`. In degree zero this is `f_zero_comp_liftFZero`; in positive
  degrees `A[0]` is zero.

## Homotopies

Here `L` is again a complex with injective terms; no augmentation is needed.

- `homotopyZeroZero χ comm`, `homotopyZeroOne χ comm` and
  `homotopyZeroSucc ε χ n g g' w` are the components of the homotopy, of
  degree `-1`. They come with the `simp` lemmas `comp_homotopyZeroZero`,
  `comp_homotopyZeroOne` and `comp_homotopyZeroSucc`. Each component extends a
  map along a differential of `K`, using `exact₀` or `exact_succ` and the
  injectivity of the terms of `L`.
- `homotopyZero χ comm : Homotopy χ 0` for a cochain map `χ : K ⟶ L` with
  `comm : ε ≫ χ = 0`, assembled by `Homotopy.mkCoinductive`.
- `homotopyOfComp ε φ ψ h : Homotopy φ ψ` for cochain maps `φ ψ : K ⟶ L` with
  `h : ε ≫ φ = ε ≫ ψ`. It is `homotopyZero (φ - ψ)` transported by
  `Homotopy.equivSubZero`.

## Provenance and interpretation

Cartan–Eilenberg, *Homological Algebra* (1956), Chapter V, §1, printed p.78
(PDF page 100), defines: "A right complex X over A is a positive complex X and
an augmentation map ε: A → X. The right complex is called injective if all Xⁿ
are injective; it is called acyclic if ε induces an isomorphism A ≈ H(X), or
equivalently if the sequence 0 → A → X⁰ → X¹ → ⋯ → Xⁿ → Xⁿ⁺¹ → ⋯ is exact." A map
`F : X → X'` over `f : A → A'` is a map of complexes with `F ∘ ε = ε' ∘ f`. Proposition 1.1a states:
"Let X be an acyclic right complex over A, X′ an injective right complex over
A′, and let f: A → A′. There is then a map F: X → X′ over f, and any two such
maps are homotopic." Cartan and Eilenberg state it without proof, as the dual
of Proposition 1.1 (pp.76–77, PDF pages 98–99). That proof constructs `F` and
the homotopy degree by degree, as this module does.

The translation is as follows.

- An acyclic right complex over `A` is `ε : A[0] ⟶ K` with `[QuasiIso ε]`. A
  cochain map out of `A[0]` is exactly a morphism `A ⟶ K⁰` whose composite with
  the first differential is zero.
- An injective right complex over `B` is `L` with injective terms and an
  augmentation `η : B[0] ⟶ L`.
- A map over `f` is a cochain map `F : K ⟶ L` with
  `ε ≫ F = (single₀ C).map f ≫ η`. The existence half of Proposition 1.1a is
  `lift` with `comp_lift`.
- The uniqueness half is `homotopyOfComp`: two maps `F, F'` over `f` satisfy
  `ε ≫ F = ε ≫ F'`. `homotopyOfComp` assumes only this equality, so it needs no
  augmentation of `L`.

Cartan and Eilenberg work with modules over a ring. Grothendieck, *Sur
quelques points d'algèbre homologique* (1957), Section 2.3, printed p.143
(PDF page 25), transfers their Chapter V to abelian categories: the theory
"se développe comme dans [6, Chap. V]", where [6] is Cartan–Eilenberg, and
"l'exposé de [6] se transporte tel quel", subject only to the existence of
injective (or projective) resolutions needed to define derived functors. His
footnote 3 on the same page defines a right resolution of `A` as a complex of
positive degrees with an augmentation `A ⟶ C`, `A` viewed as a complex in
degree 0, such that `0 → A → C⁰ → C¹ → ⋯` is exact. This is the source of the
abelian-category setting here. The lift itself needs no global existence of
injectives: the target `L` is given, and only its terms are assumed injective.

The Lean argument is an adaptation of Mathlib, not a transcription of
Cartan–Eilenberg. Mathlib's `InjectiveResolution.desc` and
`InjectiveResolution.descHomotopyZero` treat the special case in which the
source is also an injective resolution and the target is an injective
resolution (Cartan–Eilenberg, Proposition 1.2a, p.78). Their proofs use only
the exactness of the source and the injectivity of the target terms. This
module copies them with the source replaced by an arbitrary right resolution,
the target by an arbitrary complex of injectives with augmentation, and the
identity of `A` by `f`. The exactness of the source comes from `QuasiIso ε`
through `exactAt_succ` and `isLimitKernelFork`. Like the dual of
Cartan–Eilenberg's proof of Proposition 1.1, the construction proceeds degree by
degree, but it is phrased through Mathlib's `CochainComplex.mkHom` and
`Homotopy.mkCoinductive`.

## Relation to the statement module

Worker 3's `ResolutionLiftStatement` asks, for an injective resolution `I` of
`A`, for a cochain map `φ : K ⟶ I.cocomplex` with `ε ≫ φ = I.ι` and for
homotopies between any two such maps. The intended proof uses
`lift ε (𝟙 A) I.ι` with `comp_lift`, and `homotopyOfComp`.
`ResolutionComparisonIndependenceStatement`,
`ResolutionComparisonNaturalityStatement` and
`ResolutionComparisonTransformationStatement` are intended to follow from
`homotopyOfComp` with Mathlib's `InjectiveResolution.desc` and
`InjectiveResolution.isoRightDerivedObj`.

## Scope

- No proposition of Worker 3's statement module is proved in this module. The
  four proofs above are planned as separate proof tasks.
- `AcyclicResolutionComparisonStatement` (acyclic resolutions compute right
  derived functors) is not addressed. It needs the long exact sequence of right
  derived functors, which is not used here.
- Only `ℕ`-indexed cochain complexes are treated. The lift is a chosen cochain
  map; no compatibility of `lift` with composition or with change of `f` is
  stated beyond what `homotopyOfComp` gives.
