# Independence of the resolution comparison from the injective resolution

Author: Worker 716. This module proves Worker 3's statement
`Langlands.Cohomology.ResolutionComparisonIndependenceStatement` from the module
`Langlands.Cohomology.AcyclicResolution.Statement`. It imports Worker 61's published module
`Langlands.Cohomology.AcyclicResolution.Comparison`, which in turn imports the statement
module and Worker 61's `Langlands.Cohomology.AcyclicResolution.Lift`.

Composition `f ≫ g` is `f` followed by `g`. `(single₀ C).obj A`, written `A[0]` below, is
the cochain complex with `A` in degree zero and zero elsewhere. `Hⁿ(F ·)` abbreviates the
functor `F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n` from
`CochainComplex C ℕ` to `D`: apply `F` termwise, then take degree-`n` cohomology.

## Theorem

`Langlands.Cohomology.resolutionComparisonIndependenceStatement :
ResolutionComparisonIndependenceStatement.{u, v, u', v'}`, with all four universe
parameters free and no hypotheses beyond those of the statement. Spelled out, it says:

Let `C : Type u` be an abelian category (`Category.{v} C`) with
`[HasInjectiveResolutions C]`, let `D : Type u'` be an abelian category
(`Category.{v'} D`), and let `F : C ⥤ D` be an additive functor. `F` is not assumed left
exact. Let `A : C`, `K : CochainComplex C ℕ`, and `ε : A[0] ⟶ K` a quasi-isomorphism
(`QuasiIso ε`); nothing is assumed about the terms of `K`. Let `I` and `J` be injective
resolutions of `A`, and let `φ : K ⟶ I.cocomplex` and `ψ : K ⟶ J.cocomplex` be cochain
maps with `ε ≫ φ = I.ι` and `ε ≫ ψ = J.ι`. Then for every `n : ℕ`

`Hⁿ(F ·).map φ ≫ (I.isoRightDerivedObj F n).inv =
Hⁿ(F ·).map ψ ≫ (J.isoRightDerivedObj F n).inv`

as maps `Hⁿ(F K) ⟶ (F.rightDerived n).obj A`. Here `I.isoRightDerivedObj F n` is
Mathlib's identification of `(F.rightDerived n).obj A` with the degree-`n` cohomology of
`F` applied to `I.cocomplex`. So the comparison map from the cohomology of `F K` to the
right derived functor depends neither on the injective resolution nor on the
augmentation-compatible lift. This is the uniqueness part of the comparison of
Cartan–Eilenberg, Homological Algebra, Chapter V, Proposition 1.1a, for a covariant
functor.

## Proof

After introducing the data, each side of the equation is, by definition, Worker 61's
`AcyclicResolution.comparison F I φ n` and `AcyclicResolution.comparison F J ψ n`
respectively. The proof is the published theorem
`AcyclicResolution.comparison_eq F ε φ ψ hφ hψ n`, which states exactly this equality;
the introduced hypothesis `QuasiIso ε` is its instance argument.

That theorem is proved in `Langlands.Cohomology.AcyclicResolution.Comparison` as follows.
Let `h := InjectiveResolution.desc (𝟙 A) J I : I.cocomplex ⟶ J.cocomplex`, the map of
injective resolutions over `𝟙 A` (Mathlib's `desc f I' J'` goes from `J'.cocomplex` to
`I'.cocomplex`). Then `φ ≫ h` and `ψ` are both cochain maps `K ⟶ J.cocomplex`, and both
compose with `ε` to `J.ι` (by `hφ`, `InjectiveResolution.desc_commutes` and `hψ`). So
`AcyclicResolution.homotopyOfComp` gives a homotopy `φ ≫ h ≃ ψ`; it uses only that `ε` is
a quasi-isomorphism and that the terms of the common target `J.cocomplex` are injective.
Applying `F.mapHomotopy` and `Homotopy.homologyMap_eq` gives
`Hⁿ(F ·).map ψ = Hⁿ(F ·).map φ ≫ Hⁿ(F ·).map h`. Mathlib's
`InjectiveResolution.isoRightDerivedObj_inv_naturality` for `h` over `𝟙 A` says
`(I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map (𝟙 A) =
Hⁿ(F ·).map h ≫ (J.isoRightDerivedObj F n).inv`; with
`(F.rightDerived n).map (𝟙 A) = 𝟙` it identifies
`Hⁿ(F ·).map h ≫ (J.isoRightDerivedObj F n).inv` with `(I.isoRightDerivedObj F n).inv`.
Hence `Hⁿ(F ·).map ψ ≫ (J.isoRightDerivedObj F n).inv =
Hⁿ(F ·).map φ ≫ (I.isoRightDerivedObj F n).inv`.

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
