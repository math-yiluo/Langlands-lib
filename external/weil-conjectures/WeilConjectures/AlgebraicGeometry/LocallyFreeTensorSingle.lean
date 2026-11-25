/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-! # Tensoring a locally finite free sheaf with a sheaf in degree zero

Source: Bhatt--Scholze, Proposition 6.8.11(3), the finite free local calculation.
(a step of blueprint `proposition-six-operations-dctf--14`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def sumCopiesIso {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
    (A : C) (m n : ℕ) :
    (⨁ fun _ : Fin m ↦ A) ⊞ (⨁ fun _ : Fin n ↦ A) ≅ ⨁ fun _ : Fin (m + n) ↦ A where
  hom := biprod.desc
    (biproduct.desc fun i ↦ biproduct.ι (fun _ : Fin (m + n) ↦ A) (Fin.castAdd n i))
    (biproduct.desc fun j ↦ biproduct.ι (fun _ : Fin (m + n) ↦ A) (Fin.natAdd m j))
  inv := biproduct.desc (Fin.addCases
    (fun i ↦ biproduct.ι (fun _ : Fin m ↦ A) i ≫ biprod.inl)
    (fun j ↦ biproduct.ι (fun _ : Fin n ↦ A) j ≫ biprod.inr))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro i <;> simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

private lemma lfp_sum {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hG : IsLocallyFinitelyPresented R G) (n : ℕ) :
    IsLocallyFinitelyPresented R (⨁ fun _ : Fin n ↦ G) := by
  induction n with
  | zero =>
    apply isLocallyFinitelyPresented_of_isZero
    apply (IsZero.iff_id_eq_zero _).2
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    let e : (⨁ fun _ : Fin (n + 1) ↦ G) ≅ (⨁ fun _ : Fin n ↦ G) ⊞ G :=
      (sumCopiesIso G n 1).symm ≪≫
        biprod.mapIso (Iso.refl _) (biproductUniqueIso (fun _ : Fin 1 ↦ G))
    apply localFinitePresentation_of_iso e.symm
    exact lfp_extension _ (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact ih hG

private noncomputable def freeTensorSingleIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (n : ℕ) (e : F ≅ Mod.finiteFree (condensedRingObj Λ X) n) :
    (DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj G ≅
      (DerivedCategory.singleFunctor _ 0).obj (⨁ fun _ : Fin n ↦ G) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let S := DerivedCategory.singleFunctor C 0
  exact tensorIso (S.mapIso e) (Iso.refl _) ≪≫
    whiskerRightIso (S.mapBiproduct (fun _ : Fin n ↦ Mod.regular _)) _ ≪≫
    (tensorRight (S.obj G)).mapBiproduct (fun _ : Fin n ↦ S.obj (Mod.regular _)) ≪≫
    biproduct.mapIso (fun _ ↦
      whiskerRightIso (DerivedCategory.singleFunctorObjUnitIso C) _ ≪≫ λ_ (S.obj G)) ≪≫
    (S.mapBiproduct (fun _ : Fin n ↦ G)).symm

private lemma zero_of_cover {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsZero (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    IsZero M := by
  have (i : U.I₀) : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ (.mk i)
  have hX : IsZero M.X := by
    have : IsIso (0 : M.X ⟶ 0) := by
      refine ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1}
        (0 : M.X ⟶ 0) U.f U.mem₀ fun i ↦ ?_
      let e := ProEtale.upperStarIsoLocalizationRestriction
        Ab.{u + 1} (U.f i) inferInstance
      exact isIso_of_source_target_iso_zero _
        (((Mod.forget _).map_isZero (h i)).of_iso (e.app M.X).symm).isoZero
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).map_isZero
          (isZero_zero _)).of_iso (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : M.X ⟶ 0))
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (hX.eq_of_src _ _))

/-- Tensoring a locally finite free coefficient module with a locally finitely presented
module has no negative cohomology, and all its cohomology is locally finitely presented.
Source: Bhatt--Scholze, Proposition 6.8.11(3), the finite free local calculation.
Proof: on a cover trivializing the first factor, the derived tensor is a finite sum of
copies of the second factor in degree zero. Exact inverse image and monoidal pullback
identify the restricted cohomology. Covering detection descends vanishing; binding the
covers of finite presentations descends local finite presentation. Finite sums preserve
local finite presentation by the split short exact sequences, including the empty sum.
(a step of blueprint `proposition-six-operations-dctf--14`) -/
theorem locallyFree_tensor_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj F))
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE 0 ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)) := by
  classical
  let R := condensedRingObj Λ X
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨U, hU⟩ := hF
  let H (i : U.I₀) := upperStar Λ (U.f i)
  have hfree (i : U.I₀) : Mod.IsFree (condensedRingObj Λ (U.X i)) ((H i).obj F) := by
    exact free_of_iso (free_comap (inv (condensedPullbackHom Λ (U.f i))) (hU i))
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (U.f i))).app _).symm
  have hg (i : U.I₀) : IsLocallyFinitelyPresented (condensedRingObj Λ (U.X i))
      ((H i).obj G) := by
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (U.f i))).app _).symm
      (localFinitePresentation_comap _ (localFinitePresentation_pullback (U.f i) hG))
  let e (i : U.I₀) : (H i).leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H i).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H i).obj G) :=
    (Functor.Monoidal.μIso (H i).leftDerivedFunctor _ _).symm ≪≫
      tensorIso ((H i).singleFunctorCompLeftDerivedFunctorIso.app F)
        ((H i).singleFunctorCompLeftDerivedFunctorIso.app G)
  have localCalc (i : U.I₀) :
      ((H i).leftDerivedFunctor.obj K).IsGE 0 ∧
      ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ (U.X i))
        ((DerivedCategory.homologyFunctor _ n).obj ((H i).leftDerivedFunctor.obj K)) := by
    obtain ⟨r, ⟨er⟩⟩ := hfree i
    let ei := e i ≪≫ freeTensorSingleIso Λ (U.X i) _ _ r er
    have hge := DerivedCategory.TStructure.t.isGE_of_iso ei.symm 0
    have hle := DerivedCategory.TStructure.t.isLE_of_iso ei.symm 0
    refine ⟨hge, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst n
      exact localFinitePresentation_of_iso
        (((DerivedCategory.homologyFunctor _ 0).mapIso ei) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
        (lfp_sum _ _ (hg i) r)
    · apply isLocallyFinitelyPresented_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  have raw (n : ℤ) (i : U.I₀) :
      IsLocallyFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj
          ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (U.f i)))
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (U.f i))).app _)
    exact localFinitePresentation_of_iso
      (((H i).leftDerivedFunctorHomologyFunctorIso n).app K).symm ((localCalc i).2 n)
  constructor
  · apply (DerivedCategory.isGE_iff K 0).2
    intro n hn
    apply zero_of_cover R _ U
    intro i
    let ei := (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (U.f i))).app
      (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj
        ((DerivedCategory.homologyFunctor _ n).obj K))
    have := (localCalc i).1
    have hz := DerivedCategory.isZero_of_isGE ((H i).leftDerivedFunctor.obj K) 0 n hn
    have hz' := hz.of_iso (((H i).leftDerivedFunctorHomologyFunctorIso n).app K)
    have hz'' := hz'.of_iso ei.symm
    apply (IsZero.iff_id_eq_zero _).2
    apply Mod.hom_ext
    exact ((Mod.forget _).map_isZero hz'').eq_of_src _ _
  · intro n
    choose V hV using raw n
    refine ⟨U.bind V, fun ij ↦ ?_⟩
    rcases ij with ⟨i, j⟩
    exact (fp_pullback_comp_iff ((V i).f j) (U.f i) _).mpr (hV i j)

end AlgebraicGeometry.ProEtale.CondensedRing
