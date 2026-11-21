import Langlands.Automorphic.TranslatedBlockLeviOperators
import Langlands.Automorphic.HeckeTwist.DifferentialMultiplier
import Langlands.Automorphic.CuspidalAdmissible.CasimirAnnihilator
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Uniform finite levels and Casimir bounds for translated Levi slices -/

noncomputable section

universe u
open NumberField Polynomial
open scoped Classical
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance uniformSliceRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance uniformSliceContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance uniformSliceSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance uniformSliceFormsGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance uniformSliceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance uniformSliceSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "T" => TranslatedBlockConstantTerms F B S
local notation "M" => AdelicBlockParabolic.FullLevi F B

variable (i : Fin B.length)

local notation "d" => B.size i
local notation "V" => FiniteSmoothRationalFunctions F (B.size i)
local notation "slice" => translatedBlockLeviSlice F B S i

/-- A level common to all the slices in one block of a translated-period vector. -/
def IsCommonBlockSliceLevel (v : T) (K : OpenSubgroup (FiniteAdelicGL F d)) : Prop :=
  ∀ (m : M) (a : K), finiteSmoothFiniteRightAction F d a.val (slice m v) = slice m v

set_option maxHeartbeats 850000 in
/-- For a fixed vector, one open subgroup fixes the slices at every Levi argument. -/
theorem exists_translatedBlockLeviSlice_commonLevel (v : T) :
    ∃ K : OpenSubgroup (FiniteAdelicGL F d), IsCommonBlockSliceLevel F B S i v K := by
  obtain ⟨L, hL⟩ := translatedBlockTerm_finiteSmooth F B S v
  let j := blockShapeFiniteBlockEmbedding F B i
  let K : OpenSubgroup (FiniteAdelicGL F d) := L.comap j.toMonoidHom j.continuous
  refine ⟨K, fun m a => ?_⟩
  have h : translatedBlockTermFiniteAction F B S (j a.val) v = v := hL ⟨j a.val, a.property⟩
  exact (translatedBlockLeviSlice_finite F B S i m a.val v).symm.trans (congrArg (slice m) h)

private theorem exists_monic_aeval_mem_ideal {Z : Type*} [CommRing Z] [Algebra ℂ Z]
    (J : Ideal Z) (hfin : Module.Finite ℂ (Z ⧸ J.restrictScalars ℂ)) (z : Z) :
    ∃ p : ℂ[X], p.Monic ∧ aeval z p ∈ J := by
  let q := Ideal.Quotient.mkₐ ℂ J
  have hfinite : Module.Finite ℂ (Z ⧸ J) := hfin
  obtain ⟨p, hp, hq⟩ := @IsIntegral.of_finite ℂ (Z ⧸ J) _ _ _ hfinite (q z)
  exact ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.mp ((aeval_algHom_apply q z p).symm.trans hq)⟩

set_option maxHeartbeats 850000 in
/-- Every element of a block enveloping centre has a common polynomial on all slices of one vector. -/
theorem exists_translatedBlockLeviSlice_centralPolynomial (v : T) (z : EnvelopingCenter F d) :
    ∃ q : ℂ[X], q.Monic ∧ ∀ m : M, finiteSmoothCenterAction F d (aeval z q) (slice m v) = 0 := by
  obtain ⟨f, hf⟩ := exists_translatedBlockLeviSlice_eq_original F B S v
  let g := S.ambient f
  let J := blockShapeLeviSliceCenterAnnihilator F B i g
  have hfin : Module.Finite ℂ (EnvelopingCenter F d ⧸ J.restrictScalars ℂ) :=
    blockShapeLeviSliceCenterAnnihilator_finiteQuotient F B i g (S.isAutomorphicForm_ambient f).2.2.1
  obtain ⟨q, hq, hqJ⟩ := exists_monic_aeval_mem_ideal J hfin z
  refine ⟨q, hq, fun m => ?_⟩
  calc
    _ = finiteSmoothCenterAction F d (aeval z q) (blockShapeLeviSliceFactorLinearMap F B i m g) :=
      congrArg (finiteSmoothCenterAction F d (aeval z q)) (hf i m)
    _ = 0 := blockShapeLeviSliceCenterAnnihilator_kills F B i g hqJ m

set_option maxHeartbeats 850000 in
/-- The matrix Casimir also has one common annihilating polynomial after any Hecke determinant twist. -/
theorem exists_translatedBlockLeviSlice_twistedCasimirPolynomial (v : T) (μ : HeckeCharacter F) :
    ∃ q : ℂ[X], q ≠ 0 ∧ ∀ m : M,
      aeval (finiteSmoothEnvelopingAction F d (matrixCasimir F d)) q
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier d μ (slice m v)) = 0 := by
  let z₀ := matrixCentralCasimir F d
  let z := heckeCenterShift d μ z₀
  let A := finiteSmoothCenterAction F d
  let D : V →ₗ[ℂ] V := (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier d μ).toLinearMap
  obtain ⟨q, hq, hkill⟩ := exists_translatedBlockLeviSlice_centralPolynomial F B S i v z
  refine ⟨q, hq.ne_zero, fun m => ?_⟩
  have hD (f : V) : D (A z f) = A z₀ (D f) :=
    (finiteSmoothCenterAction_heckeDeterminantMultiplier d μ z₀ f).symm
  have hz : aeval (A z) q (slice m v) = 0 :=
    (LinearMap.congr_fun (aeval_algHom_apply A z q) (slice m v)).trans (hkill m)
  calc
    _ = D (aeval (A z) q (slice m v)) :=
      (CuspidalAdmissible.aeval_intertwine D hD q (slice m v)).symm
    _ = 0 := (congrArg D hz).trans D.map_zero

end Langlands.Automorphic
