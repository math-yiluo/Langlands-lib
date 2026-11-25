/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Right derived functors computed by K-injective resolutions

Let `v : C ⥤ D` be an additive functor between abelian categories and `K ⟶ I` a K-injective
resolution of a cochain complex `K` (`CochainComplex.KInjectiveResolution`). We compare the
complex `Rv(K) = v(I)` with the right derived functors of `v` available in the project:

- the classical right derived functors: for an object `X`, `Hᵖ(Rv(X[0])) ≅ Rᵖv(X)`
  (`CochainComplex.KInjectiveResolution.rightDerivedHomologyIsoRightDerived`);
- the bounded below right derived functor `R⁺v`: `Hᵖ(R⁺v(K)) ≅ Hᵖ(v(I))` for `K` bounded below
  (`CochainComplex.KInjectiveResolution.homologyRightDerivedFunctorPlusObjIso`);
- the unbounded right derived functor `R(v)`, when `C` has K-injective resolutions:
  `R(v)(K) ≅ v(I)` in the derived category
  (`CochainComplex.KInjectiveResolution.rightDerivedFunctorObjIso`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex.KInjectiveResolution

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (v : C ⥤ D)
  [v.Additive]

/-- **K-injective resolutions of `X[0]` compute the classical right derived functors**: for a
K-injective resolution `R` of `X[0]`, `Hᵖ(Rv(X[0])) ≅ Rᵖv(X)`.

(blueprint: `lem-sp-kinjective-computes`) -/
noncomputable def rightDerivedHomologyIsoRightDerived [HasInjectiveResolutions C] {X : C}
    (R : ((CochainComplex.singleFunctor C 0).obj X).KInjectiveResolution) (p : ℕ) :
    R.rightDerivedHomology v p ≅ (v.rightDerived p).obj X :=
  R.rightDerivedHomologyIso (injectiveResolution X).kInjectiveResolution v p ≪≫
    ((injectiveResolution X).isoRightDerivedObjCochainComplex v p).symm

/-- **K-injective resolutions compute `R⁺v`**: for a bounded below complex `K` and a K-injective
resolution `R` of `K`, `Hᵖ(R⁺v(K)) ≅ Hᵖ(v(I))`.

(blueprint: `def-sp-kinjective-bridge`) -/
noncomputable def homologyRightDerivedFunctorPlusObjIso [EnoughInjectives C]
    [HasDerivedCategory C] [HasDerivedCategory D] (K : CochainComplex.Plus C)
    (R : K.obj.KInjectiveResolution) (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D p).obj
        (v.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      R.rightDerivedHomology v p :=
  have := K.2.choose_spec
  let R₀ := (exists_of_isStrictlyGE K.obj K.2.choose).choose
  have h₀ := (exists_of_isStrictlyGE K.obj K.2.choose).choose_spec
  let L : CochainComplex.Plus C := ⟨R₀.I, K.2.choose, h₀.1⟩
  have : ∀ i, Injective (L.obj.X i) := h₀.2
  let φ : K ⟶ L := ObjectProperty.homMk R₀.ι
  have : IsIso (DerivedCategory.Plus.Q.map φ) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) φ
      ((HomologicalComplex.mem_quasiIso_iff R₀.ι).2 R₀.quasiIso_ι)
  (DerivedCategory.Plus.homologyFunctor D p).mapIso
      (v.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map φ))) ≪≫
    v.homologyRightDerivedFunctorPlusObjQIsoOfInjective L p ≪≫ R₀.rightDerivedHomologyIso R v p

variable [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  {K : CochainComplex C ℤ} (R : K.KInjectiveResolution)

/-- **K-injective resolutions compute the unbounded right derived functor**: for a K-injective
resolution `K ⟶ I`, `R(v)(K) ≅ v(I)` in the derived category.

(blueprint: `def-sp-kinjective-bridge`) -/
noncomputable def rightDerivedFunctorObjIso :
    v.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Qh.obj (R.rightDerived v) :=
  v.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map R.ι)) ≪≫
    v.rightDerivedFunctorObjQIso R.I ≪≫
    (DerivedCategory.quotientCompQhIso D).symm.app _

/-- The cohomology of the unbounded right derived functor is computed by K-injective
resolutions: `Hᵖ(R(v)(K)) ≅ Hᵖ(v(I))`.

(blueprint: `def-sp-kinjective-bridge`) -/
noncomputable def homologyRightDerivedFunctorObjIso (p : ℤ) :
    (DerivedCategory.homologyFunctor D p).obj
        (v.rightDerivedFunctor.obj (DerivedCategory.Q.obj K)) ≅
      R.rightDerivedHomology v p :=
  (DerivedCategory.homologyFunctor D p).mapIso
      (v.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map R.ι)) ≪≫
        v.rightDerivedFunctorObjQIso R.I) ≪≫
    (DerivedCategory.homologyFunctorFactors D p).app _

end CochainComplex.KInjectiveResolution
