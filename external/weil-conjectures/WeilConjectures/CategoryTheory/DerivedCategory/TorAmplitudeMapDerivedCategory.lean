/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# Tor amplitude under an exact monoidal functor

Let `F : C ⥤ D` be an exact, faithful, strong monoidal functor between closed braided monoidal
Grothendieck abelian categories with functorial flat resolutions, which sends flat objects to
flat objects. This file shows that the induced functor `D(F) : D(C) ⥤ D(D)` preserves and
reflects Tor amplitude: an object `K` of `D(C)` has Tor amplitude in `[a, b]` if and only if
`D(F) K` has.

* `D(F)` preserves Tor amplitude: it sends a flat model of `K` in degrees `[a, b]` to a flat
  model of `D(F) K` in the same degrees.
* `D(F)` reflects Tor amplitude: testing `D(F) K` against the unit shows that `K` is
  concentrated in `[a, b]`, since `F` reflects the vanishing of homology. So `K` has a bounded
  above flat model `P`, whose image `F(P)` is a bounded above flat model of `D(F) K`. For an
  object `N` of `C`, the complex `F(P ⊗ N) ≅ F(P) ⊗ F(N)` computes
  `D(F)(K ⊗ᴸ N[0]) ≅ D(F) K ⊗ᴸ F(N)[0]`, which is concentrated in `[a, b]` by hypothesis; as `F`
  reflects the vanishing of homology, so is `K ⊗ᴸ N[0]`.

The application is the comparison functor `ν^*` from étale to pro-étale sheaves
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`).

## Main results

- `DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff`: `D(F)` preserves and reflects
  Tor amplitude.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [IsGrothendieckAbelian.{v₁} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [IsGrothendieckAbelian.{v₂} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  [F.PreservesFlat]

/-- An exact functor sending flat objects to flat objects preserves Tor amplitude: it sends a
flat model in degrees `[a, b]` to a flat model in degrees `[a, b]`. -/
lemma torAmplitudeIn_mapDerivedCategory_obj
    {a b : ℤ} {K : DerivedCategory C} (hK : torAmplitudeIn C a b K) :
    torAmplitudeIn D a b (F.mapDerivedCategory.obj K) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := (torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).1 hK
  exact (torAmplitudeIn_iff_exists_iso_Q_obj_flat a b _).2
    ⟨(F.mapHomologicalComplex _).obj P, inferInstance, inferInstance,
      fun n ↦ Functor.PreservesFlat.flat_obj (hP n),
      ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e⟩⟩

variable [F.Monoidal]

/-- For a strong monoidal additive functor `F`, the complex `F(P ⊗ N)` obtained by applying `F`
termwise to `P ⊗ N` is isomorphic to `F(P) ⊗ F(N)`. -/
noncomputable def mapHomologicalComplexTensorRightIso (P : CochainComplex C ℤ) (N : C) :
    (F.mapHomologicalComplex _).obj (((tensorRight N).mapHomologicalComplex _).obj P) ≅
      ((tensorRight (F.obj N)).mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (Functor.OplaxMonoidal.δ F (P.X n) N))
    (fun i j _ ↦ by
      dsimp
      exact Functor.OplaxMonoidal.δ_natural_left F (P.d i j) N)

/-- An exact, faithful, strong monoidal functor sending flat objects to flat objects reflects
Tor amplitude. -/
lemma torAmplitudeIn_of_torAmplitudeIn_mapDerivedCategory_obj [F.Faithful]
    {a b : ℤ} {K : DerivedCategory C} (hK : torAmplitudeIn D a b (F.mapDerivedCategory.obj K)) :
    torAmplitudeIn C a b K := by
  -- `K` is concentrated in `[a, b]`, so it has a bounded above flat model `P`
  obtain ⟨-, hLE⟩ := F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    (homologyConcentratedIn_of_torAmplitudeIn hK)
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _, π, _, hP⟩ := L.exists_quasiIso_flat_of_isStrictlyLE b
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let e' : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP
  -- its termwise image is a bounded above flat model of `D(F) K`
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  have : CochainComplex.IsStrictlyLE P' b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ _ b).2 inferInstance
  have hP'k := CochainComplex.kFlat_of_isStrictlyLE_of_flat P' b
    (fun n ↦ Functor.PreservesFlat.flat_obj (hP n))
  let e'' : Q.obj P' ≅ F.mapDerivedCategory.obj K :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e'
  intro N
  -- `D(F)(K ⊗ᴸ N[0]) ≅ D(F) K ⊗ᴸ F(N)[0]`
  let i : F.mapDerivedCategory.obj K ⊗ (singleFunctor D 0).obj (F.obj N) ≅
      F.mapDerivedCategory.obj (K ⊗ (singleFunctor C 0).obj N) :=
    whiskerRightIso e''.symm _ ≪≫ QObjTensorSingleFunctorObjIso P' hP'k _ ≪≫
      Q.mapIso (mapHomologicalComplexTensorRightIso F P N).symm ≪≫
      (F.mapDerivedCategoryFactors.app _).symm ≪≫
      F.mapDerivedCategory.mapIso
        ((QObjTensorSingleFunctorObjIso P hPk N).symm ≪≫ whiskerRightIso e' _)
  exact F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    ((homologyConcentratedIn a b).prop_of_iso i (hK (F.obj N)))

/-- **Tor amplitude under an exact monoidal functor.** An exact, faithful, strong monoidal
functor sending flat objects to flat objects preserves and reflects Tor amplitude: `K` has Tor
amplitude in `[a, b]` if and only if `D(F) K` has. -/
lemma torAmplitudeIn_mapDerivedCategory_obj_iff [F.Faithful]
    (a b : ℤ) (K : DerivedCategory C) :
    torAmplitudeIn D a b (F.mapDerivedCategory.obj K) ↔ torAmplitudeIn C a b K :=
  ⟨torAmplitudeIn_of_torAmplitudeIn_mapDerivedCategory_obj F,
    torAmplitudeIn_mapDerivedCategory_obj F⟩

end DerivedCategory
