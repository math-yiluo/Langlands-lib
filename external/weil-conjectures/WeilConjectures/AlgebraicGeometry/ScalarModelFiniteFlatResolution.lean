/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.Double
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Finite free resolutions of scalar models

Source: Weil conjectures blueprint, main-20261015, chap-The-pro-etale-site,
ctf-equals-bc proof, Local models; Stacks Tags 03EI, 06YQ, 06YS, 06YP and 06YU
(auxiliary; not a blueprint node).

## Main definitions

- `CategoryTheory.siteConstantModuleFunctorIndependent`: constant modules at independent
  coefficient universe, preserving the existing dependency interface by import.
- `CategoryTheory.commutativeConstantModuleIndependent`: its commutative-ring presentation.

## Main statements

- `scalarModel_finite_flat_resolution_dvr`: the DVR resolution and tensor computation.
- `scalarModel_finite_free_field`: the field case without flatness of the algebra sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (J : GrothendieckTopology C) [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J RingCat.{r}] [HasSheafify J CommRingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}]
  [J.WEqualsLocallyBijective CommRingCat.{r}]

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

variable [EssentiallySmall.{r} C]

/-- The two-term complex is Mathlib's double complex in precisely degrees -1 and 0.
Source: blueprint Local models (auxiliary; not a blueprint node). -/
abbrev scalarModelTwoTerm {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    [HasZeroObject A] {X Y : A} (f : X ⟶ Y) : CochainComplex A ℤ :=
  HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

variable [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]

section ScalarModelProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open HomologicalComplex
open scoped ChangeOfRings

/-- The two-term complex of a short exact sequence resolves its cokernel. -/
private theorem twoTerm_augmentation {A : Type uA} [Category.{vA} A] [Abelian A]
    (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ ε : scalarModelTwoTerm S.f ⟶ (CochainComplex.singleFunctor A 0).obj S.X₃,
      QuasiIso ε := by
  classical
  let K := scalarModelTwoTerm S.f
  let L := (CochainComplex.singleFunctor A 0).obj S.X₃
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₃
  let em := HomologicalComplex.doubleXIso₀ S.f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
  let en := HomologicalComplex.doubleXIso₁ S.f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
    (by decide : (-1 : ℤ) ≠ 0)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X _ _ i hm h0
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 S.X₃ i hi
  let ε : K ⟶ L := HomologicalComplex.mkHomFromDouble _ (by decide) 0 (S.g ≫ e.inv)
    (by rw [zero_comp, ← Category.assoc, S.zero, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = en.hom ≫ S.g := by simp [ε, en]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono (K.d (-1) 0) := by
    dsimp [K, scalarModelTwoTerm]
    rw [HomologicalComplex.double_d _ _ (by decide)]
    infer_instance
  refine ⟨ε, ?_⟩
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
    apply (ShortComplex.quasiIso_iff_of_zeros' _
      ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
      ((hL (-1) (by omega)).eq_of_src _ _)
      ((hL 1 (by omega)).eq_of_tgt _ _)).2
    have heq : K.d (-1) 0 ≫ ε.f 0 = 0 := by
      rw [← ε.comm]
      simp [hεi (-1) (by omega)]
    let T := ShortComplex.mk (K.d (-1) 0) (ε.f 0) heq
    let iso : T ≅ S := ShortComplex.isoMk em en e
      (by dsimp [T, K, em, en, scalarModelTwoTerm]
          rw [HomologicalComplex.double_d _ _ (by decide)]; simp) hε0.symm
    have hs : T.Exact := (ShortComplex.exact_iff_of_iso iso).2 hS.exact
    have : Epi (ε.f 0) := by
      have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
      exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
    exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
  · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
    rw [quasiIsoAt_iff_exactAt' ε i hLex]
    by_cases hm : i = -1
    · subst i
      rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
      exact hmono
    · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)

end ScalarModelProof

end SheafOfModules
