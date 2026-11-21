import Langlands.Automorphic.BlockShapeLeviSliceCompactFinite
import Langlands.Global.Factors.CuspidalSupportIdentityEvaluation

/-! # Compact Levi embeddings for the place evaluations of a block period -/

noncomputable section

open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 650000

universe u

namespace Langlands.Global.ArchimedeanGL

open Langlands.Automorphic Langlands.GeneralLinear NumberField

variable (F : Type u) [Field F] {n : ℕ} (B : BlockShape n)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "I" => InfiniteAdeleRing F
local notation "coord" => archimedeanGLCoordinates F

private theorem mapMatrix_blockLevi {R : Type*} [CommRing R] (φ : I →+* R) (m : B.Levi I) :
    φ.mapMatrix (B.leviEmbedding I m).val =
      Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' (fun i => φ.mapMatrix (m i).val)) := by
  change Matrix.reindex B.indexEquiv B.indexEquiv
    ((Matrix.blockDiagonal' (fun i => (m i).val)).map φ) = _
  rw [Matrix.blockDiagonal'_map _ _ (map_zero φ)]
  rfl

private theorem realMatrix_blockLevi (m : B.Levi I) (v : RP) :
    realMatrix F n (coord n (B.leviEmbedding I m)) v =
      Matrix.reindex B.indexEquiv B.indexEquiv
        (Matrix.blockDiagonal' (fun i => realMatrix F (B.size i) (coord (B.size i) (m i)) v)) :=
  mapMatrix_blockLevi F B
    ((PrimitiveAdelicHeight.realCoord v).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) m

private theorem complexMatrix_blockLevi (m : B.Levi I) (v : CP) :
    complexMatrix F n (coord n (B.leviEmbedding I m)) v =
      Matrix.reindex B.indexEquiv B.indexEquiv
        (Matrix.blockDiagonal' (fun i => complexMatrix F (B.size i) (coord (B.size i) (m i)) v)) :=
  mapMatrix_blockLevi F B
    ((PrimitiveAdelicHeight.complexCoord v).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) m

private theorem compactEmbedding_ext (g h : InfiniteAdelicGL F n)
    (hr : ∀ v : RP, realMatrix F n (coord n g) v = realMatrix F n (coord n h) v)
    (hc : ∀ v : CP, complexMatrix F n (coord n g) v = complexMatrix F n (coord n h) v) : g = h := by
  apply (coord n).injective
  apply Units.ext
  refine Matrix.ext fun a b => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact congrFun (congrFun (hr v) a) b
  · exact congrFun (congrFun (hc v) a) b

private theorem blockDiagonal_ones {R : Type*} [CommRing R] :
    Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' (fun i => (1 : Matrix (Fin (B.size i)) (Fin (B.size i)) R))) = 1 := by
  change Matrix.reindexRingEquiv R B.indexEquiv
    (Matrix.blockDiagonal' (1 : ∀ i, Matrix (Fin (B.size i)) (Fin (B.size i)) R)) = 1
  rw [Matrix.blockDiagonal'_one, map_one]

/-- Inserting a real compact Levi at one place agrees with the global Levi
embedding of its inserted block factors. -/
theorem realPlaceCompactInclusion_leviEmbedding_val (v : RP) (k : B.CompactLevi ℝ) :
    (realPlaceCompactInclusion F n v (B.compactLeviEmbedding ℝ k)).val =
      B.leviEmbedding I (fun i => (realPlaceCompactInclusion F (B.size i) v (k i)).val) := by
  classical
  apply compactEmbedding_ext
  · intro w
    rw [realMatrix_blockLevi]
    simp only [realMatrix_realPlaceCompactInclusion]
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hw, OneMemClass.coe_one, blockDiagonal_ones]
  · intro w
    rw [complexMatrix_blockLevi]
    simp only [complexMatrix_realPlaceCompactInclusion, blockDiagonal_ones]

/-- The same Levi compatibility holds at a complex compact place. -/
theorem complexPlaceCompactInclusion_leviEmbedding_val (v : CP) (k : B.CompactLevi ℂ) :
    (complexPlaceCompactInclusion F n v (B.compactLeviEmbedding ℂ k)).val =
      B.leviEmbedding I (fun i => (complexPlaceCompactInclusion F (B.size i) v (k i)).val) := by
  classical
  apply compactEmbedding_ext
  · intro w
    rw [realMatrix_blockLevi]
    simp only [realMatrix_complexPlaceCompactInclusion, blockDiagonal_ones]
  · intro w
    rw [complexMatrix_blockLevi]
    simp only [complexMatrix_complexPlaceCompactInclusion]
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hw, OneMemClass.coe_one, blockDiagonal_ones]

/-- The compact action on one block at a real place is the corresponding
single-block operator on the global period. -/
theorem realPlaceCompactInclusion_levi_single (v : RP) (i : Fin B.length)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℝ) :
    realPlaceCompactInclusion F n v (B.compactLeviEmbedding ℝ (Pi.mulSingle i k)) =
      blockShapeInfiniteCompactEmbedding B F i (realPlaceCompactInclusion F (B.size i) v k) := by
  apply Subtype.ext
  rw [realPlaceCompactInclusion_leviEmbedding_val]
  change B.leviEmbedding I _ = B.leviEmbedding I
    (Pi.mulSingle i (realPlaceCompactInclusion F (B.size i) v k).val)
  apply congrArg (B.leviEmbedding I)
  funext j
  by_cases hj : j = i
  · subst j
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one, OneMemClass.coe_one]

/-- The corresponding complex compact block gives the same global block operator. -/
theorem complexPlaceCompactInclusion_levi_single (v : CP) (i : Fin B.length)
    (k : Matrix.unitaryGroup (Fin (B.size i)) ℂ) :
    complexPlaceCompactInclusion F n v (B.compactLeviEmbedding ℂ (Pi.mulSingle i k)) =
      blockShapeInfiniteCompactEmbedding B F i (complexPlaceCompactInclusion F (B.size i) v k) := by
  apply Subtype.ext
  rw [complexPlaceCompactInclusion_leviEmbedding_val]
  change B.leviEmbedding I _ = B.leviEmbedding I
    (Pi.mulSingle i (complexPlaceCompactInclusion F (B.size i) v k).val)
  apply congrArg (B.leviEmbedding I)
  funext j
  by_cases hj : j = i
  · subst j
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one, OneMemClass.coe_one]

end Langlands.Global.ArchimedeanGL

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL

variable {F : Type u} [Field F] {n : ℕ} (B : BlockShape n)
  {W : Type u} [AddCommGroup W] [Module ℂ W]
  {V : Fin B.length → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Compact translation in a single global block acts on the corresponding
slot of the evaluated tensor. -/
def IsBlockPeriodCompactEvaluation
    (κ : Representation ℂ (standardInfiniteCompact F n) W)
    (ρ : ∀ i, Representation ℂ (standardInfiniteCompact F (B.size i)) (V i))
    (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), V i)) : Prop :=
  ∀ (i : Fin B.length) (k : standardInfiniteCompact F (B.size i)) (w : W),
    ev (κ (blockShapeInfiniteCompactEmbedding B F i k) w) =
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (ρ i k)) (ev w)

private theorem isBlockCompactEvaluation_of_single
    {R : Type*} [RCLike R]
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) R) W)
    (ρ : ∀ i, Representation ℂ (Matrix.unitaryGroup (Fin (B.size i)) R) (V i))
    (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), V i))
    (h : ∀ i (k : Matrix.unitaryGroup (Fin (B.size i)) R) w,
      ev (κ (B.compactLeviEmbedding R (Pi.mulSingle i k)) w) =
        PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i (ρ i k)) (ev w)) :
    IsBlockCompactEvaluation (B := B) κ ρ ev := by
  let α := κ.comp (B.compactLeviEmbedding R)
  let β := FiniteTensor.external ρ
  let equivariant : Submonoid (B.CompactLevi R) :=
    { carrier := {k | ∀ w, ev (α k w) = β k (ev w)}
      one_mem' := by intro w; simp only [map_one, Module.End.one_apply]
      mul_mem' := by
        intro k l hk hl w
        change ∀ w, ev (α k w) = β k (ev w) at hk
        change ∀ w, ev (α l w) = β l (ev w) at hl
        change ev (α (k * l) w) = β (k * l) (ev w)
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk, hl] }
  intro k
  change k ∈ equivariant
  refine Submonoid.pi_mem_of_mulSingle_mem k (fun i w => ?_)
  have hi : (fun j => ρ j ((Pi.mulSingle i (k i) : B.CompactLevi R) j)) =
      Function.update (fun _ => LinearMap.id) i (ρ i (k i)) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Function.update_self]
    · simp only [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj, map_one, Module.End.one_eq_id]
  change ev (κ (B.compactLeviEmbedding R (Pi.mulSingle i (k i))) w) =
    PiTensorProduct.map (fun j => ρ j ((Pi.mulSingle i (k i) : B.CompactLevi R) j)) (ev w)
  rw [hi]
  exact h i (k i) w

variable (κ : Representation ℂ (standardInfiniteCompact F n) W)
  (ρ : ∀ i, Representation ℂ (standardInfiniteCompact F (B.size i)) (V i))
  (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), V i))

/-- The global single-block compact equations give the full real-place Levi equation. -/
theorem isBlockCompactEvaluation_real_of_period
    (v : {v : NumberField.InfinitePlace F // v.IsReal})
    (h : IsBlockPeriodCompactEvaluation B κ ρ ev) :
    IsBlockCompactEvaluation (B := B) (κ.comp (realPlaceCompactInclusion F n v).toMonoidHom)
      (fun i => (ρ i).comp (realPlaceCompactInclusion F (B.size i) v).toMonoidHom) ev := by
  apply isBlockCompactEvaluation_of_single
  intro i k w
  have hk := realPlaceCompactInclusion_levi_single F B v i k
  change ev (κ (realPlaceCompactInclusion F n v (B.compactLeviEmbedding ℝ (Pi.mulSingle i k))) w) =
    PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
      (ρ i (realPlaceCompactInclusion F (B.size i) v k))) (ev w)
  rw [hk]
  exact h i (realPlaceCompactInclusion F (B.size i) v k) w

/-- The global single-block compact equations give the full complex-place Levi equation. -/
theorem isBlockCompactEvaluation_complex_of_period
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (h : IsBlockPeriodCompactEvaluation B κ ρ ev) :
    IsBlockCompactEvaluation (B := B) (κ.comp (complexPlaceCompactInclusion F n v).toMonoidHom)
      (fun i => (ρ i).comp (complexPlaceCompactInclusion F (B.size i) v).toMonoidHom) ev := by
  apply isBlockCompactEvaluation_of_single
  intro i k w
  have hk := complexPlaceCompactInclusion_levi_single F B v i k
  change ev (κ (complexPlaceCompactInclusion F n v (B.compactLeviEmbedding ℂ (Pi.mulSingle i k))) w) =
    PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
      (ρ i (complexPlaceCompactInclusion F (B.size i) v k))) (ev w)
  rw [hk]
  exact h i (complexPlaceCompactInclusion F (B.size i) v k) w

end Langlands.Global
