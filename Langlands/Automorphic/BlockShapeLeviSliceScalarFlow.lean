import Langlands.Automorphic.BlockShapeLeviSliceCenterFinite
import Langlands.Analysis.FiniteFunctionFlow

/-! # Scalar one-parameter subgroups on the finite Levi centre orbit -/

noncomputable section

universe u

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField Langlands.Algebra Langlands.Archimedean.Kostant Langlands.GeneralLinear
  Langlands.Global Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance leviSliceFlowRationalAddCommGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance leviSliceFlowContinuousAddCommGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviSliceFlowFiniteSmoothAddCommGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _

local notation "Λ" => ComplexLieMatrixPlace F
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "Z" => Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (blockRanks B Λ)))
local notation "J" => LieEnvelopingEquiv.map (AlgHom.toLieHom (blockMatrixInclusion B (ι := Λ)))
local notation "A" => finiteSmoothMatrixEnvelopingAction F (n := n)
local notation "θ" => blockLeviCenterOrbitMap F B

/-- The original Levi slice is in the orbit of the full enveloping centre. -/
theorem blockLeviTermRestriction_mem_centerOrbit (f : V) :
    blockLeviTermRestriction F B f ∈ LinearMap.range (θ f) := by
  refine ⟨1, ?_⟩
  change blockLeviTermRestriction F B (A (J (1 : Z).val) f) = _
  rw [show (1 : Z).val = 1 from rfl, map_one, map_one, Module.End.one_apply]

variable (i : Fin B.length)

/-- Insert a real Lie one-parameter subgroup in a single Levi block. -/
def blockLeviOneParameter (X : RealLieAlgebra F (B.size i)) (t : ℝ) : M :=
  Pi.mulSingle i (AdelicGL.ofInfinite F (B.size i) (infiniteOneParameter F (B.size i) X t))

@[simp]
theorem blockLeviOneParameter_zero (X : RealLieAlgebra F (B.size i)) :
    blockLeviOneParameter F B i X 0 = 1 := by
  simp only [blockLeviOneParameter, infiniteOneParameter_zero, map_one, Pi.mulSingle_one]

private theorem blockLeviOneParameter_mul (X : RealLieAlgebra F (B.size i)) (m : M) (t : ℝ) :
    m * blockLeviOneParameter F B i X t =
      Function.update m i (m i * AdelicGL.ofInfinite F (B.size i)
        (infiniteOneParameter F (B.size i) X t)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [blockLeviOneParameter, Pi.mul_apply, Pi.mulSingle_eq_same, Function.update_self]
  · simp only [blockLeviOneParameter, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj,
      mul_one, Function.update_of_ne hj]

private theorem blockLeviCenterOrbitMap_mul (f : V) (z w : Z) :
    θ f (z * w) = θ (A (J w.val) f) z := by
  change blockLeviTermRestriction F B (A (J (z.val * w.val)) f) = _
  rw [map_mul, map_mul, Module.End.mul_apply]
  rfl

private theorem hasDerivAt_blockSlice_oneParameter (d : ℕ) (X : RealLieAlgebra F d)
    (v : FiniteSmoothRationalFunctions F d) (x : AdelicGL F d) (t : ℝ) :
    HasDerivAt (fun s => ContinuousRationalFunctions.evaluate F d v.val
      (x * AdelicGL.ofInfinite F d (infiniteOneParameter F d X s)))
      (ContinuousRationalFunctions.evaluate F d
        (finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)) v).val
        (x * AdelicGL.ofInfinite F d (infiniteOneParameter F d X t))) t := by
  have hd := hasDerivAt_smooth_oneParameter F d (finiteSmoothSlice F d (AdelicGL.finite F d x) v)
    X (AdelicGL.infinite F d x) t
  rw [← envelopingAction_real_generator, ← finiteSmoothSlice_envelopingAction] at hd
  simpa only [finiteSmoothSlice_apply, ← OperatorRealization.mul_ofInfinite_eq_pair] using hd

set_option maxHeartbeats 300000 in
private theorem hasDerivAt_blockLeviCenterOrbitMap (f : V) (X : RealLieAlgebra F (B.size i))
    (z : EnvelopingCenter F (B.size i))
    (hz : z.val = envelopingGenerator F (B.size i) (complexify F (B.size i) X))
    (w : Z) (m : M) (t : ℝ) :
    HasDerivAt (fun s => θ f w (m * blockLeviOneParameter F B i X s))
      (θ f (singleBlockCenterToMatrixLevi F B i z * w)
        (m * blockLeviOneParameter F B i X t)) t := by
  let d := B.size i
  let f' := A (J w.val) f
  let v := blockShapeLeviSliceFactorLinearMap F B i m f'
  let x := m i
  let a (s : ℝ) := x * AdelicGL.ofInfinite F d (infiniteOneParameter F d X s)
  have he (s : ℝ) : θ f w (m * blockLeviOneParameter F B i X s) =
      ContinuousRationalFunctions.evaluate F d v.val (a s) := by
    rw [blockLeviOneParameter_mul]
    change blockLeviTermRestriction F B f' (Function.update m i (a s)) = _
    show blockShapeLeviSlice F B f' 1 (Function.update m i (a s)) = _
    rfl
  have hd' : HasDerivAt (fun s => ContinuousRationalFunctions.evaluate F d v.val (a s))
      (ContinuousRationalFunctions.evaluate F d (finiteSmoothCenterAction F d z v).val (a t)) t := by
    have hz' : finiteSmoothCenterAction F d z =
        finiteSmoothEnvelopingAction F d (envelopingGenerator F d (complexify F d X)) := by
      change finiteSmoothEnvelopingAction F d z.val = _
      rw [hz]
    rw [hz']
    exact hasDerivAt_blockSlice_oneParameter F d X v x t
  rw [show (fun s => θ f w (m * blockLeviOneParameter F B i X s)) = _ from funext he,
    blockLeviOneParameter_mul, blockLeviCenterOrbitMap_mul]
  change HasDerivAt _ (blockShapeLeviSliceCenterOrbitMap F B i f' z (Function.update m i (a t))) t
  rw [blockShapeLeviSliceCenterOrbitMap_update]
  exact hd'

/-- Every real one-parameter subgroup with central enveloping generator preserves the
finite-dimensional full Levi centre orbit. -/
theorem blockLeviCenterOrbit_range_mul_oneParameter (f : V)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) (X : RealLieAlgebra F (B.size i))
    (z : EnvelopingCenter F (B.size i))
    (hz : z.val = envelopingGenerator F (B.size i) (complexify F (B.size i) X))
    (g : LinearMap.range (θ f)) (t : ℝ) :
    (fun m => g.val (m * blockLeviOneParameter F B i X t)) ∈ LinearMap.range (θ f) := by
  let ψ := θ f
  let P := LinearMap.range ψ
  let q : Module.End ℂ Z := LinearMap.mulLeft ℂ (singleBlockCenterToMatrixLevi F B i z)
  let c (m : M) (s : ℝ) := m * blockLeviOneParameter F B i X s
  have hzero (m : M) : c m 0 = m := by simp only [c, blockLeviOneParameter_zero, mul_one]
  have hd (w : Z) (m : M) (s : ℝ) :
      HasDerivAt (fun a => ψ w (c m a)) (ψ (q w) (c m s)) s :=
    hasDerivAt_blockLeviCenterOrbitMap F B i f X z hz w m s
  have hker : LinearMap.ker ψ ≤ (LinearMap.ker ψ).comap q := by
    intro w hw
    change ψ (q w) = 0
    change ψ w = 0 at hw
    funext m
    have h := hd w m 0
    rw [hw, hzero] at h
    exact h.unique (hasDerivAt_const 0 (0 : ℂ))
  let Q := (LinearMap.ker ψ).mapQ (LinearMap.ker ψ) q hker
  let E := ψ.quotKerEquivRange
  let D : Module.End ℂ P := E.toLinearMap ∘ₗ Q ∘ₗ E.symm.toLinearMap
  have hD (m : M) (s : ℝ) (b : P) :
      HasDerivAt (fun a => b.val (c m a)) ((D b).val (c m s)) s := by
    obtain ⟨w, hw⟩ := b.property
    have hb : E (Submodule.Quotient.mk w) = b := Subtype.ext hw
    rw [← hb]
    have hDw : (D (E (Submodule.Quotient.mk w))).val = ψ (q w) := by
      change ((E (Q (E.symm (E (Submodule.Quotient.mk w))))) : M → ℂ) = _
      rw [LinearEquiv.symm_apply_apply, Submodule.mapQ_apply]
      exact ψ.quotKerEquivRange_apply_mk _
    rw [hDw]
    exact hd w m s
  let : Module.Finite ℂ P := blockLeviCenterOrbitMap_finite F B f hf
  exact Langlands.Analysis.function_comp_flow_mem P (Module.finBasis ℂ P) D c hzero hD g t

end Langlands.Automorphic
