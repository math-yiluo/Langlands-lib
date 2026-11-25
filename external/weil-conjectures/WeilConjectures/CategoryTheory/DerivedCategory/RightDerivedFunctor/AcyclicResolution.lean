/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution

/-!
# Right derived functors computed by acyclic resolutions

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives and K-injective resolutions. The unbounded right derived functor
`F.rightDerivedFunctor` is computed by bounded below complexes of `F`-acyclic objects:

- `CategoryTheory.Functor.rightDerivedFunctorObjQIsoOfRightAcyclic`: for a bounded below complex
  `K` of `F`-acyclic objects, `RF(K) ≅ F(K)` in `D(D)`;
- `CategoryTheory.Functor.rightDerivedFunctorSingleObjIsoOfResolution`: for a resolution
  `X[0] ⟶ K` of an object `X` by `F`-acyclic objects, `RF(X[0]) ≅ F(K)` in `D(D)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **A bounded below complex of acyclic objects computes the right derived functor.** For a
complex `K` which is strictly concentrated in degrees `≥ a` and whose terms are `F`-acyclic,
`RF(K) ≅ F(K)` in the derived category: the unit of the bounded below right derived functor is an
isomorphism on `K` (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`),
and the bounded below and the unbounded right derived functors agree on bounded below complexes
(`CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`). -/
noncomputable def rightDerivedFunctorObjQIsoOfRightAcyclic (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (hK : ∀ n, F.rightAcyclic (K.X n)) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) :=
  let L : CochainComplex.Plus C := ⟨K, a, inferInstance⟩
  let H := (HomotopyCategory.Plus.quotient C).obj L
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hK
  F.rightDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso C).symm.app K) ≪≫
    (F.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Qh.obj H)).symm ≪≫
    (DerivedCategory.Plus.ι (C := D)).mapIso (asIso (F.rightDerivedFunctorPlusUnith.app H)).symm ≪≫
    (DerivedCategory.quotientCompQhIso D).app _

/-- **An acyclic resolution computes the right derived functor.** For a resolution
`ε : X[0] ⟶ K` of an object `X` by a complex `K` (indexed by `ℕ`) of `F`-acyclic objects,
`RF(X[0]) ≅ F(K)` in the derived category, where `K` is viewed as a complex indexed by `ℤ`
concentrated in degrees `≥ 0`. -/
noncomputable def rightDerivedFunctorSingleObjIsoOfResolution {X : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ε] (hK : ∀ n, F.rightAcyclic (K.X n)) :
    F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex _).obj (K.extend ComplexShape.embeddingUpNat)) :=
  have : QuasiIso (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff ε ComplexShape.embeddingUpNat).2 inferInstance
  F.rightDerivedFunctor.mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0 rfl).symm ≪≫
      asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat))) ≪≫
    F.rightDerivedFunctorObjQIsoOfRightAcyclic _ 0
      (HomologicalComplex.prop_extend_X _ ComplexShape.embeddingUpNat hK)


/-- **The cohomology of the right derived functor.** For an object `X`, the `q`-th cohomology of
`RF(X[0])` is the classical right derived functor `R^q F(X)`: both are computed by an injective
resolution of `X`, which is a K-injective resolution of `X[0]`. -/
noncomputable def homologyRightDerivedFunctorSingleObjIso (X : C) (q : ℕ) :
    (DerivedCategory.homologyFunctor D q).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≅
      (F.rightDerived q).obj X :=
  let R := CochainComplex.KInjectiveResolution.ofIsGE ((CochainComplex.singleFunctor C 0).obj X) 0
  (DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctor.mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app X)) ≪≫
    R.homologyRightDerivedFunctorObjIso F q ≪≫ R.rightDerivedHomologyIsoRightDerived F q

end CategoryTheory.Functor
