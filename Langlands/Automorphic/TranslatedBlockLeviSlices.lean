import Langlands.Automorphic.TranslatedBlockTermLeviImage
import Langlands.Automorphic.TranslatedBlockTermAction
import Langlands.Automorphic.BlockShapeCuspidalLeviSlice

/-! # The actual one-block automorphic slices of a translated term -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance translatedLeviSliceRationalAddCommGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance translatedLeviSliceContinuousAddCommGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance translatedLeviSliceFiniteSmoothAddCommGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance translatedLeviSliceFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance translatedLeviSliceStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedLeviSliceRealizationAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "T" => TranslatedBlockConstantTerms F B S
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "ev" => translatedFunctionEmbedding β φ
local notation "σ" => translatedFunctionAction β φ
local notation "Q" => translatedBlockLeviRestriction F B S
local notation "Lemb" => B.leviEmbedding (Adeles F)

/-- The faithful evaluation of a finite-smooth function as a complex function. -/
def finiteSmoothFunctionEvaluation (d : ℕ) : FiniteSmoothRationalFunctions F d →ₗ[ℂ] (AdelicGL F d → ℂ) where
  toFun f := ContinuousRationalFunctions.evaluate F d f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteSmoothFunctionEvaluation_injective (d : ℕ) :
    Function.Injective (finiteSmoothFunctionEvaluation F d) := by
  intro f g h
  apply Subtype.ext
  apply ContinuousRationalFunctions.toContinuousMap_injective F d
  ext x
  exact congrFun h x

variable (i : Fin B.length)

local notation "d" => B.size i
local notation "V" => FiniteSmoothRationalFunctions F (B.size i)
local notation "e" => finiteSmoothFunctionEvaluation F (B.size i)

private def translatedBlockSliceFunction (m : M) : T →ₗ[ℂ] (AdelicGL F d → ℂ) where
  toFun v x := Q v (Function.update m i x)
  map_add' v w := funext fun x => congrFun ((Q).map_add v w) (Function.update m i x)
  map_smul' c v := funext fun x => congrFun ((Q).map_smul c v) (Function.update m i x)

set_option maxHeartbeats 450000 in
private theorem translatedBlockSliceFunction_mem_range (m : M) (v : T) :
    translatedBlockSliceFunction F B S i m v ∈ LinearMap.range (e) := by
  have hv : ∃ f : S.Space, realizedBlockLeviRestriction F B S f = Q v :=
    translatedBlockLeviRestriction_mem_range F B S v
  obtain ⟨f, hf⟩ := hv
  refine ⟨blockShapeLeviSliceFactorLinearMap F B i m (S.ambient f), ?_⟩
  funext x
  exact congrArg (fun h : M → ℂ => h (Function.update m i x)) hf

/-- Holding the other actual Levi blocks fixed gives a finite-smooth function in the remaining block. -/
def translatedBlockLeviSlice (m : M) : T →ₗ[ℂ] V :=
  (LinearEquiv.ofInjective (e) (finiteSmoothFunctionEvaluation_injective F d)).symm.toLinearMap.comp
    ((translatedBlockSliceFunction F B S i m).codRestrict (LinearMap.range (e))
      (translatedBlockSliceFunction_mem_range F B S i m))

@[simp]
theorem translatedBlockLeviSlice_evaluation (m : M) (v : T) (x : AdelicGL F d) :
    e (translatedBlockLeviSlice F B S i m v) x = Q v (Function.update m i x) := by
  let j := LinearEquiv.ofInjective (e) (finiteSmoothFunctionEvaluation_injective F d)
  let y : LinearMap.range (e) := ⟨translatedBlockSliceFunction F B S i m v,
    translatedBlockSliceFunction_mem_range F B S i m v⟩
  exact congrFun (congrArg Subtype.val (j.apply_symm_apply y)) x

set_option maxHeartbeats 450000 in
/-- One original realized form determines all one-block slices of a fixed quotient vector. -/
theorem exists_translatedBlockLeviSlice_eq_original (v : T) :
    ∃ f : S.Space, ∀ (i : Fin B.length) (m : M), translatedBlockLeviSlice F B S i m v =
      blockShapeLeviSliceFactorLinearMap F B i m (S.ambient f) := by
  have hv : ∃ f : S.Space, realizedBlockLeviRestriction F B S f = Q v :=
    translatedBlockLeviRestriction_mem_range F B S v
  obtain ⟨f, hf⟩ := hv
  refine ⟨f, fun i m => ?_⟩
  apply finiteSmoothFunctionEvaluation_injective F (B.size i)
  funext x
  rw [translatedBlockLeviSlice_evaluation]
  exact (congrArg (fun h : M → ℂ => h (Function.update m i x)) hf).symm

set_option maxHeartbeats 450000 in
/-- Every translated Levi block slice satisfies the original automorphic conditions. -/
theorem translatedBlockLeviSlice_isAutomorphic (m : M) (v : T) :
    IsAutomorphicForm F d (finiteSmoothInclusion F d (translatedBlockLeviSlice F B S i m v)) := by
  obtain ⟨f, hf⟩ := exists_translatedBlockLeviSlice_eq_original F B S v
  rw [hf i m]
  let a := S.ambient f
  let g := blockShapeLeviSliceFactorLinearMap F B i m a
  have ha := S.isAutomorphicForm_ambient f
  refine ⟨(hasFiniteLevel_iff_mem_finiteSmooth F d g.val).mpr g.property.2, ?_, ?_, ?_⟩
  · have hp : AdelicGL.pair F n 1 1 = 1 := (AdelicGL.split F n).symm.map_one
    have h := blockShapeLeviSliceFactor_isInfiniteFinite_of_form B F (S.formInclusion f) 1 1 m i
    rw [Subgroup.coe_one, hp] at h
    exact h
  · exact blockShapeLeviSliceFactor_isCenterFinite F B i a ha.2.2.1 m
  · exact blockShapeLeviSliceFactor_hasPolynomialGrowth F B i a ha.2.2.2 1 m

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 450000 in
/-- Under strict-refinement vanishing, all translated block slices are cuspidal. -/
theorem translatedBlockLeviSlice_isCuspidal
    (hf : ∀ (f : S.Space) (t : Finset (Fin (n - 1))), B.cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight t) (S.ambient f) = 0)
    (m : M) (v : T) : IsCuspidal F d (translatedBlockLeviSlice F B S i m v).val := by
  obtain ⟨f, hv⟩ := exists_translatedBlockLeviSlice_eq_original F B S v
  rw [hv i m]
  exact isCuspidal_blockShapeLeviSliceFactor F B (S.ambient f) (hf f) 1 m i

omit [CompactSpace (AdeleQuotient F)] in
/-- Multiplication in the selected coordinate is multiplication by a one-block Levi element. -/
theorem blockLevi_update_mulSingle (m : M) (x a : AdelicGL F d) :
    Function.update m i (x * a) = Function.update m i x * Pi.mulSingle i a := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same]
  · simp only [Function.update_of_ne hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, mul_one]

omit [CompactSpace (AdeleQuotient F)] in
set_option maxHeartbeats 450000 in
/-- The character of a block slice is the restriction of the selected centre character to that block. -/
theorem translatedBlockLeviSlice_scalar (χ : Cen →* ℂˣ) (v : T)
    (hv : ∀ z : Cen, σ z v = (χ z : ℂ) • v) (m : M) (z : Ideles F) (x : AdelicGL F d) :
    e (translatedBlockLeviSlice F B S i m v) (x * AdelicGL.scalar F d z) =
      (χ (Pi.mulSingle i z) : ℂ) * e (translatedBlockLeviSlice F B S i m v) x := by
  let a : Cen := Pi.mulSingle i z
  let j := Function.update m i x
  have h : Q (σ a v) j = (χ a : ℂ) * Q v j := by
    have h₁ : Q (σ a v) = (χ a : ℂ) • Q v :=
      (congrArg (Q) (hv a)).trans ((Q).map_smul (χ a : ℂ) v)
    exact congrArg (fun w : M → ℂ => w j) h₁
  have he : Q (σ a v) j = ev v (Lemb (blockLeviScalars F B a) * Lemb j) :=
    congrFun (translatedFunctionEmbedding_action β φ a v) (Lemb j)
  have hx : Function.update m i (x * AdelicGL.scalar F d z) = blockLeviScalars F B a * j :=
    (blockLevi_update_mulSingle F B i m x (AdelicGL.scalar F d z)).trans
      ((congrArg (fun w : M => j * w) (blockLeviScalars_mulSingle F B i z).symm).trans
        (blockLeviScalars_commute F B a j).eq.symm)
  calc
    _ = Q v (Function.update m i (x * AdelicGL.scalar F d z)) :=
      translatedBlockLeviSlice_evaluation F B S i m v _
    _ = Q v (blockLeviScalars F B a * j) := congrArg (Q v) hx
    _ = ev v (Lemb (blockLeviScalars F B a) * Lemb j) :=
      congrArg (ev v) ((Lemb).map_mul (blockLeviScalars F B a) j)
    _ = Q (σ a v) j := he.symm
    _ = (χ a : ℂ) * Q v j := h
    _ = _ := congrArg ((χ a : ℂ) * ·) (translatedBlockLeviSlice_evaluation F B S i m v x).symm

end Langlands.Automorphic
