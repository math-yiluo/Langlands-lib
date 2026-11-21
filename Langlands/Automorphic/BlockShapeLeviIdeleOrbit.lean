import Langlands.Automorphic.BlockConstantTermScalarAction
import Langlands.Automorphic.BlockShapeLeviSliceScalarFlow
import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Global.ArchimedeanScalarFlow
import Langlands.Global.IdeleFiniteLevelRepresentatives
import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.Algebra.BigOperators.Pi

/-! # Finite-dimensional block idele centre orbits on the Levi -/

noncomputable section

universe u

open NumberField IsDedekindDomain
open scoped Classical BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGL

variable (F : Type u) [Field F] [NumberField F] (d : ℕ)

@[simp]
theorem scalar_infiniteIdelesInclusion (x : (InfiniteAdeles F)ˣ) :
    scalar F d (infiniteIdelesInclusion F x) =
      ofInfinite F d (Matrix.GeneralLinearGroup.scalar (Fin d) x) := by
  apply ext_infinite_finite F d
  · rw [infinite_ofInfinite]
    change Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F))
      (Matrix.GeneralLinearGroup.scalar (Fin d) (infiniteIdelesInclusion F x)) = _
    rw [Matrix.GeneralLinearGroup.map_scalar]
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin d))
      (congrArg Prod.fst ((ideleProductEquiv F).apply_symm_apply (x, 1)))
  · rw [finite_ofInfinite]
    change Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F))
      (Matrix.GeneralLinearGroup.scalar (Fin d) (infiniteIdelesInclusion F x)) = _
    rw [Matrix.GeneralLinearGroup.map_scalar]
    exact (congrArg (Matrix.GeneralLinearGroup.scalar (Fin d))
      (congrArg Prod.snd ((ideleProductEquiv F).apply_symm_apply (x, 1)))).trans (map_one _)

@[simp]
theorem infinite_scalar_finiteIdelesInclusion (x : FiniteIdeles F) :
    infinite F d (scalar F d (finiteIdelesInclusion F x)) = 1 := by
  change Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F))
    (Matrix.GeneralLinearGroup.scalar (Fin d) (finiteIdelesInclusion F x)) = _
  rw [Matrix.GeneralLinearGroup.map_scalar]
  exact (congrArg (Matrix.GeneralLinearGroup.scalar (Fin d))
    (congrArg Prod.fst ((ideleProductEquiv F).apply_symm_apply (1, x)))).trans (map_one _)

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance leviIdeleOrbitRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance leviIdeleOrbitContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance leviIdeleOrbitFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local notation "I" => Fin B.length
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "V" => FiniteSmoothRationalFunctions F n

/-- The action of the block idele centre on functions on the actual Levi. -/
def blockLeviScalarAction : Representation ℂ Cen (M → ℂ) where
  toFun z :=
    { toFun g m := g (m * blockLeviScalars F B z)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := LinearMap.ext fun g => funext fun m => by simp only [map_one, mul_one]; rfl
  map_mul' z w := LinearMap.ext fun g => funext fun m => by
    change g (m * blockLeviScalars F B (z * w)) =
      g (m * blockLeviScalars F B z * blockLeviScalars F B w)
    rw [map_mul, mul_assoc]

@[simp]
theorem blockLeviScalarAction_apply (z : Cen) (g : M → ℂ) (m : M) :
    blockLeviScalarAction F B z g m = g (m * blockLeviScalars F B z) := rfl

/-- Principal block scalars fix the Levi restriction. -/
theorem blockLeviScalarAction_principal (f : V) (a : I → Fˣ) :
    blockLeviScalarAction F B (fun i => diagonalUnits F (a i)) (blockLeviTermRestriction F B f) =
      blockLeviTermRestriction F B f := by
  funext m
  let q : B.Levi F := fun i => Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) (a i)
  rw [blockLeviScalarAction_apply, ← (blockLeviScalars_commute F B _ m).eq]
  have hq : blockLeviScalars F B (fun i => diagonalUnits F (a i)) =
      fun i => AdelicGL.rational F (B.size i) (q i) :=
    funext fun i => AdelicGL.scalar_diagonalUnits F (B.size i) (a i)
  rw [hq]
  exact blockShapeLeviSlice_rational_mul B F f 1 q m

private def singleFiniteIdele (i : I) : FiniteIdeles F →ₜ* Cen where
  toMonoidHom := (MonoidHom.mulSingle (fun _ : I => Ideles F) i).comp
    (finiteIdelesInclusion F).toMonoidHom
  continuous_toFun := (continuous_mulSingle (A := fun _ : I => Ideles F) i).comp
    (finiteIdelesInclusion F).continuous

private def finiteBlockScalarDirection (i : I) : FiniteIdeles F →ₜ* FiniteAdelicGL F n :=
  (AdelicGL.finite F n).comp ((B.leviEmbeddingContinuous (Adeles F)).comp
    ((blockLeviScalars F B).comp (singleFiniteIdele F B i)))

private theorem ofFinite_finiteBlockScalarDirection (i : I) (z : FiniteIdeles F) :
    AdelicGL.ofFinite F n (finiteBlockScalarDirection F B i z) =
      B.leviEmbedding (Adeles F) (blockLeviScalars F B (singleFiniteIdele F B i z)) := by
  let m := blockLeviScalars F B (singleFiniteIdele F B i z)
  apply AdelicGL.ext_infinite_finite F n
  · rw [AdelicGL.infinite_ofFinite]
    have he := congrArg Subtype.val (AdelicBlockParabolic.infinite_leviInParabolic F B m)
    change AdelicGL.infinite F n (B.leviEmbedding (Adeles F) m) =
      B.leviEmbedding (InfiniteAdeles F) (AdelicBlockParabolic.leviInfinite F B m) at he
    have hm : AdelicBlockParabolic.leviInfinite F B m = 1 := by
      funext j
      change AdelicGL.infinite F (B.size j) (AdelicGL.scalar F (B.size j)
        ((Pi.mulSingle i (finiteIdelesInclusion F z) : Cen) j)) = 1
      by_cases hj : j = i
      · subst j
        rw [Pi.mulSingle_eq_same, AdelicGL.infinite_scalar_finiteIdelesInclusion]
      · rw [Pi.mulSingle_eq_of_ne hj, map_one, map_one]
    rw [he, hm, map_one]
  · rw [AdelicGL.finite_ofFinite]
    rfl

private theorem exists_singleFiniteLevel_stabilizer (f : V) (i : I) :
    ∃ U : OpenSubgroup (FiniteIdeles F), ∀ z ∈ U,
      singleFiniteIdele F B i z ∈ (blockLeviScalarAction F B).stabilizer (blockLeviTermRestriction F B f) := by
  obtain ⟨L, hL⟩ := f.property.2
  let d := finiteBlockScalarDirection F B i
  refine ⟨L.comap d.toMonoidHom d.continuous, fun z hz => ?_⟩
  let w := B.leviEmbedding (Adeles F) (blockLeviScalars F B (singleFiniteIdele F B i z))
  have hfix : finiteSmoothRightAction F n w f = f := by
    rw [show w = AdelicGL.ofFinite F n (d z) from (ofFinite_finiteBlockScalarDirection F B i z).symm]
    exact Subtype.ext (hL ⟨d z, hz⟩)
  apply Representation.mem_stabilizer.mpr
  funext m
  change blockShapeLeviSlice F B f 1 (m * blockLeviScalars F B (singleFiniteIdele F B i z)) = _
  calc
    _ = blockShapeLeviSlice F B f w m := by
      unfold blockShapeLeviSlice
      rw [map_mul, mul_one]
    _ = blockShapeLeviSlice F B (finiteSmoothRightAction F n w f) 1 m := by
      rw [blockShapeLeviSlice_rightAction, one_mul]
    _ = _ := congrArg (fun g : V => blockShapeLeviSlice F B g 1 m) hfix

set_option maxHeartbeats 400000 in
private theorem finiteLevel_stabilizes (f : V) (U : I → OpenSubgroup (FiniteIdeles F))
    (hU : ∀ i z, z ∈ U i → singleFiniteIdele F B i z ∈
      (blockLeviScalarAction F B).stabilizer (blockLeviTermRestriction F B f))
    (z : I → FiniteIdeles F) (hz : ∀ i, z i ∈ U i) :
    (fun i => finiteIdelesInclusion F (z i)) ∈
      (blockLeviScalarAction F B).stabilizer (blockLeviTermRestriction F B f) := by
  let Q := (blockLeviScalarAction F B).stabilizer (blockLeviTermRestriction F B f)
  change (fun i => finiteIdelesInclusion F (z i)) ∈ Q
  rw [← Finset.univ_prod_mulSingle (fun i : I => finiteIdelesInclusion F (z i) : Cen)]
  apply Q.prod_mem
  intro i _
  exact hU i (z i) (hz i)

private def preservesLeviOrbit (f : V) : Submonoid Cen where
  carrier := {z | ∀ g ∈ LinearMap.range (blockLeviCenterOrbitMap F B f),
    blockLeviScalarAction F B z g ∈ LinearMap.range (blockLeviCenterOrbitMap F B f)}
  one_mem' := by
    intro g hg
    simpa only [map_one, Module.End.one_apply] using hg
  mul_mem' {z w} hz hw := by
    intro g hg
    rw [map_mul, Module.End.mul_apply]
    exact hz _ (hw _ hg)

private theorem blockLeviScalars_single_exp (i : I) (x : mixedEmbedding.mixedSpace F) :
    blockLeviScalars F B (Pi.mulSingle i (infiniteIdelesInclusion F
      (mixedUnitToInfinite F (banachExpUnit x)))) =
      blockLeviOneParameter F B i (scalarDirection F (B.size i) x) 1 := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [blockLeviScalars_apply, Pi.mulSingle_eq_same, blockLeviOneParameter,
      AdelicGL.scalar_infiniteIdelesInclusion, infiniteOneParameter_scalarDirection, one_smul]
  · simp only [blockLeviScalars_apply, blockLeviOneParameter, Pi.mulSingle_eq_of_ne hj, map_one]

private theorem exps_preserveLeviOrbit (f : V)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) (x : I → mixedEmbedding.mixedSpace F) :
    (fun i => infiniteIdelesInclusion F (mixedUnitToInfinite F (banachExpUnit (x i)))) ∈
      preservesLeviOrbit F B f := by
  rw [← Finset.univ_prod_mulSingle (fun i : I => infiniteIdelesInclusion F
    (mixedUnitToInfinite F (banachExpUnit (x i))) : Cen)]
  apply Submonoid.prod_mem
  intro i _ g hg
  change (fun m => g (m * blockLeviScalars F B _)) ∈ LinearMap.range (blockLeviCenterOrbitMap F B f)
  rw [blockLeviScalars_single_exp]
  exact blockLeviCenterOrbit_range_mul_oneParameter F B i f hf (scalarDirection F (B.size i) (x i))
    (scalarDirectionCenter F (B.size i) (x i)) rfl ⟨g, hg⟩ 1

set_option maxHeartbeats 600000 in
/-- The actual identity-argument Levi slice has a finite-dimensional orbit under
translations by all block scalar ideles. -/
theorem blockLeviTermRestriction_isFiniteVector (f : V)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) :
    FiniteVectors.IsFiniteVector (blockLeviScalarAction F B) (blockLeviTermRestriction F B f) := by
  choose U hU using exists_singleFiniteLevel_stabilizer F B f
  let φ := blockLeviTermRestriction F B f
  let P := LinearMap.range (blockLeviCenterOrbitMap F B f)
  let ρ := blockLeviScalarAction F B
  let S := {w : NumberField.InfinitePlace F // w.IsReal} → Bool
  let K := ∀ i : I, (finiteIdeleLevelRepresentatives F (U i)) × S
  let : Fintype K := by dsimp [K, S]; infer_instance
  let r (k : K) : Cen := fun i => (k i).1.val * infiniteIdelesInclusion F
    (mixedUnitToInfinite F (mixedRealSignUnit F (k i).2))
  let W : Submodule ℂ (M → ℂ) := ⨆ k : K, P.map (ρ (r k))
  let : Module.Finite ℂ P := blockLeviCenterOrbitMap_finite F B f hf
  have : Module.Finite ℂ W := Submodule.finite_iSup _
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  change ρ z φ ∈ W
  choose q hq a b v hv hz using fun i : I => finiteIdeleLevelRepresentatives_spec F (U i) (z i)
  choose s x hs using fun i : I => exists_sign_mul_expUnit F ((mixedUnitToInfinite F).symm (b i))
  let k : K := fun i => (⟨q i, hq i⟩, s i)
  let p : Cen := fun i => diagonalUnits F (a i)
  let l : Cen := fun i => finiteIdelesInclusion F (v i)
  let e : Cen := fun i => infiniteIdelesInclusion F (mixedUnitToInfinite F (banachExpUnit (x i)))
  have heq : z = r k * e * (p * l) := by
    funext i
    have hb : b i = mixedUnitToInfinite F (mixedRealSignUnit F (s i) * banachExpUnit (x i)) := by
      rw [← hs i, MulEquiv.apply_symm_apply]
    change z i = (q i * infiniteIdelesInclusion F (mixedUnitToInfinite F
      (mixedRealSignUnit F (s i)))) * e i * (p i * l i)
    rw [hz i, hb, map_mul, map_mul]
    dsimp [p, e, l]
    ac_rfl
  have hfix : ρ (p * l) φ = φ := by
    have hl : ρ l φ = φ := Representation.mem_stabilizer.mp (finiteLevel_stabilizes F B f U hU v hv)
    rw [map_mul, Module.End.mul_apply, hl]
    exact blockLeviScalarAction_principal F B f a
  have hP : ρ e φ ∈ P :=
    (exps_preserveLeviOrbit F B f hf x) φ (blockLeviTermRestriction_mem_centerOrbit F B f)
  rw [heq, map_mul ρ (r k * e) (p * l), Module.End.mul_apply, hfix,
    map_mul ρ (r k) e, Module.End.mul_apply]
  exact Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem hP)

end Langlands.Automorphic
