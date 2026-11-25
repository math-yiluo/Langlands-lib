/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat

/-!
# Reduction of a bounded flat model

Let `R` be a Noetherian commutative ring, `I` an ideal, and `P` a complex of flat sheaves of
`R`-modules concentrated in degrees `[a, b]`, representing `K = Q(P)` in the derived category.
The termwise reduction `P / I P` (`CategoryTheory.Sheaf.quotSMulTop`) is a complex of flat
sheaves of `R ⧸ I`-modules in degrees `[a, b]`; hence it has Tor amplitude in `[a, b]` over
`R ⧸ I`, and with scalars restricted back to `R` it is
`P ⊗ (R ⧸ I)`, which computes `K ⊗ᴸ (R ⧸ I)` (`CategoryTheory.Sheaf.flatModel_quotSMulTop`).

This is the site-general content of blueprint `lem-sf-reduction-flat-model`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)] (I : Ideal R)
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} (R ⧸ I)))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} (R ⧸ I))]


/-- **Reduction of a bounded flat model.** Let `P` be a complex of flat sheaves of modules over a
Noetherian ring `R`, concentrated in degrees `[a, b]`. Its termwise reduction `P' = P / I P` is a
complex of flat sheaves of `R ⧸ I`-modules concentrated in degrees `[a, b]`, so `Q(P')` has Tor
amplitude in `[a, b]` over `R ⧸ I`; and restricting the scalars of `Q(P')` back to `R` gives
`Q(P ⊗ (R ⧸ I))`, which is the derived reduction `Q(P) ⊗ᴸ (R ⧸ I)` since `P` is K-flat.

The terms of `P'` are flat by `CategoryTheory.Sheaf.flat_quotSMulTop_obj`; restricting scalars
termwise gives `P ⊗ (R ⧸ I)` (`CategoryTheory.Sheaf.quotSMulTopCompRestrictScalarsIso`). -/
theorem Sheaf.flatModel_quotSMulTop {a b : ℤ}
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n)) :
    CochainComplex.IsStrictlyGE (((Sheaf.quotSMulTop J I).mapHomologicalComplex _).obj P) a ∧
      CochainComplex.IsStrictlyLE (((Sheaf.quotSMulTop J I).mapHomologicalComplex _).obj P) b ∧
      (∀ n, ObjectProperty.flat ((((Sheaf.quotSMulTop J I).mapHomologicalComplex _).obj P).X n)) ∧
      DerivedCategory.torAmplitudeIn _ a b
        (DerivedCategory.Q.obj (((Sheaf.quotSMulTop J I).mapHomologicalComplex _).obj P)) ∧
      Nonempty ((Sheaf.restrictScalars J (Ideal.Quotient.mk I)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj (((Sheaf.quotSMulTop J I).mapHomologicalComplex _).obj P)) ≅
        DerivedCategory.Q.obj (((tensorRight ((constantSheaf J (ModuleCat.{u + 1} R)).obj
          (ModuleCat.of R (R ⧸ I)))).mapHomologicalComplex
            _).obj P)) := by
  let ρ := Sheaf.quotSMulTop J I
  let P' := (ρ.mapHomologicalComplex (.up ℤ)).obj P
  have hGE : CochainComplex.IsStrictlyGE P' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun n hn ↦ ρ.map_isZero (P.isZero_of_isStrictlyGE a n hn)
  have hLE : CochainComplex.IsStrictlyLE P' b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn ↦ ρ.map_isZero (P.isZero_of_isStrictlyLE b n hn)
  have hflat (n : ℤ) : ObjectProperty.flat (P'.X n) := Sheaf.flat_quotSMulTop_obj I (hP n)
  refine ⟨hGE, hLE, hflat, DerivedCategory.torAmplitudeIn_Q_obj_of_flat P' a b hflat, ⟨?_⟩⟩
  let ι := Sheaf.restrictScalars J (Ideal.Quotient.mk I)
  let c := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I))
  have e₁ : ι.mapDerivedCategory.obj (DerivedCategory.Q.obj P') ≅
      DerivedCategory.Q.obj ((ι.mapHomologicalComplex _).obj P') :=
    ι.mapDerivedCategoryFactors.app P'
  have e₂ : (ι.mapHomologicalComplex _).obj P' ≅ ((tensorRight c).mapHomologicalComplex _).obj P :=
    (Functor.mapHomologicalComplexCompIso (Sheaf.quotSMulTopCompRestrictScalarsIso I) (.up ℤ)).app P
  exact e₁ ≪≫ DerivedCategory.Q.mapIso e₂

end CategoryTheory
