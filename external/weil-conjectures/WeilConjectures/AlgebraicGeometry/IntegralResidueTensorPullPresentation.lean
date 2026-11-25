/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorModel

/-! # Ordinary pullback data and the derived residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Remark 6.8.15.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

@[irreducible] noncomputable def residueRestrictedRegularPullIso
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar Λ f).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y)))) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      ((Mod.comap (coefficientMap φ X)).obj (Mod.regular (condensedRingObj A X))) := by
  let P := Mod.regular (condensedRingObj A Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap φ Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  letI := residueOrdinaryUpperStarMonoidal A f
  let e : (f)^*⟦Λ⟧.obj (SY.obj P) ≅
      SX.obj (Mod.regular (condensedRingObj A X)) :=
    (comapUpperStarIso φ f).symm.app P ≪≫
      SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
  unfold residueExchangeUpperStar
  exact ((f)^*⟦Λ⟧.singleFunctorCompLeftDerivedFunctorIso).app (SY.obj P) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The defining exact-pullback comparison for the restricted regular module.

The ordinary comparison is restriction/pullback followed by the restricted
inverse monoidal unit comparison. Unfolding its name recovers exactly the
ordinary isomorphism used in `residueRestrictedRegularPullIso`.

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; the fixed ordinary and
single-object comparisons above.
(auxiliary; not a blueprint node) -/
theorem residueRestrictedRegularPullIso_def
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueRestrictedRegularPullIso Λ A φ f =
      (by
        unfold residueExchangeUpperStar
        exact ((f)^*⟦Λ⟧.singleFunctorCompLeftDerivedFunctorIso).app
            ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (residueOrdinaryRestrictedRegularPullIso Λ A φ f)) := by
  unfold residueRestrictedRegularPullIso residueOrdinaryRestrictedRegularPullIso
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
