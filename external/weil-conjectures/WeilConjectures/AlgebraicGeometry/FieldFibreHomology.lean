/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flat_of_finiteLocallyFree {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsFiniteLocallyFree] : SheafOfModules.IsFlat M := by
  obtain ⟨hlim, hcolim⟩ := finiteLocallyFree_tensorLeft_exact M
  let := hlim
  let := hcolim
  change exactFunctor _ _ (MonoidalCategory.tensorRight M)
  exact ⟨preservesFiniteLimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight M),
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flat_complex_pullback_iso {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.X n))
    (hf : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    Nonempty ((DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
      (((pullback g).mapHomologicalComplex _).obj K) ≅
      (AlgebraicGeometry.derivedPullback g).obj (DerivedCategory.Q.obj K)) := by
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  obtain ⟨F, hF, hFmap, hFadd, _, _, ⟨e, _⟩⟩ :=
    flatComplexDerivedPullback g K hb hf
  have h : F = tensorPullback g := CategoryTheory.Functor.ext hF (fun M N f ↦ hFmap f)
  subst F
  let := hFadd
  let eF : tensorPullback g ≅ pullback g :=
    (nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (pullbackPushforwardAdjunction g)
  refine ⟨(DerivedCategory.Q (C := B)).mapIso
    ((NatIso.mapHomologicalComplex eF (ComplexShape.up ℤ)).app K).symm ≪≫
    ((DerivedCategory.quotientCompQhIso B).app _).symm ≪≫
    ((DerivedCategory.Qh (C := B)).mapIso
      (((tensorPullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).symm ≪≫
    e ≪≫ (AlgebraicGeometry.derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso A).app K)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flat_single_pullback_iso {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)
    (hM : SheafOfModules.IsFlat M) :
    Nonempty ((AlgebraicGeometry.derivedPullback g).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj
          ((pullback g).obj M)) := by
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let K := (CochainComplex.singleFunctor A n).obj M
  let := SheafOfModules.monoidalCategory S.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed S.sheaf
  let := hpreadd
  have hb : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (K.X q) := by
    refine ⟨n, fun q hq ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hf : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q) := by
    intro q
    by_cases hq : q = n
    · subst q
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hM
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).2
  obtain ⟨e⟩ := flat_complex_pullback_iso g K hb hf
  refine ⟨(AlgebraicGeometry.derivedPullback g).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ A n).app M) ≪≫ e.symm ≪≫
    (DerivedCategory.Q (C := B)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (pullback g)
        (ComplexShape.up ℤ) n).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ B n).app ((pullback g).obj M)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback to a field preserves the specified single cohomology condition.
Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: new-field-fibre-homology). -/
theorem single_field_fibre_homology
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r)
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ Y) :
      let Q := ((Modules.pullback f).mapHomologicalComplex _).obj P
      (∀ q : ℕ, q ≠ i → IsZero (Q.homology q)) ∧
        (Q.homology i).IsFiniteLocallyFreeOfRank r := by
  -- The argument works for arbitrary scheme maps; no flatness of f is assumed.
  have _ := hR
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
  let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.standard A
  let : HasDerivedCategory.{u + 1} B := HasDerivedCategory.standard B
  let E := (DerivedCategory.Q (C := A)).obj P
  let Q := ((pullback f).mapHomologicalComplex _).obj P
  have := hge
  have := hle
  -- Nonnegative support supplies the negative-degree vanishing missing from hzero.
  have hz (n : ℤ) (hn : n ≠ (i : ℤ)) :
      IsZero ((DerivedCategory.homologyFunctor A n).obj E) := by
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors A n).app P)
    by_cases hlt : n < 0
    · exact P.isZero_of_isGE 0 n hlt
    · have hnat : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      have hneq : n.toNat ≠ i := by omega
      have hh := hzero n.toNat hneq
      rw [hnat] at hh
      exact hh
  have : E.IsGE (i : ℤ) := (DerivedCategory.isGE_iff E i).mpr
    (fun n hn ↦ hz n (by omega))
  have : E.IsLE (i : ℤ) := (DerivedCategory.isLE_iff E i).mpr
    (fun n hn ↦ hz n (by omega))
  -- Truncation identifies E with its sole cohomology sheaf in degree i.
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E i
  let eM : M ≅ P.homology i :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso A (i : ℤ)).app M).symm ≪≫
      (DerivedCategory.homologyFunctor A (i : ℤ)).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors A (i : ℤ)).app P
  have := hrank
  have hMrank : M.IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eM.symm
  let := hMrank
  have hMfin := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  let := hMfin
  have hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n) :=
    ⟨d, fun n hn ↦ P.isZero_of_isStrictlyLE d n hn⟩
  have hf : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    obtain ⟨s, ⟨es⟩⟩ := hfree n
    have hnr : (P.X n).IsFiniteLocallyFreeOfRank s :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso es.symm
    let := hnr
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (P.X n) s
    exact flat_of_finiteLocallyFree (P.X n)
  -- Both P and the flat single complex compute derived pullback termwise.
  obtain ⟨eP⟩ := flat_complex_pullback_iso f P hb hf
  obtain ⟨eS⟩ := flat_single_pullback_iso f M (i : ℤ) (flat_of_finiteLocallyFree M)
  let eQ : (DerivedCategory.Q (C := B)).obj Q ≅
      (DerivedCategory.singleFunctor B (i : ℤ)).obj ((pullback f).obj M) :=
    eP ≪≫ (AlgebraicGeometry.derivedPullback f).mapIso e ≪≫ eS
  let eH (n : ℤ) : Q.homology n ≅
      (((CochainComplex.singleFunctor B (i : ℤ)).obj ((pullback f).obj M)).homology n) :=
    ((DerivedCategory.homologyFunctorFactors B n).app Q).symm ≪≫
      (DerivedCategory.homologyFunctor B n).mapIso eQ ≪≫
      (DerivedCategory.homologyFunctor B n).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ B (i : ℤ)).app ((pullback f).obj M)) ≪≫
      (DerivedCategory.homologyFunctorFactors B n).app _
  constructor
  · intro q hq
    exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (i : ℤ)
      ((pullback f).obj M) (q : ℤ) (by exact_mod_cast hq)).of_iso (eH q)
  · exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (eH i ≪≫ HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (i : ℤ) ((pullback f).obj M)).symm

end AlgebraicGeometry.Scheme.Modules
