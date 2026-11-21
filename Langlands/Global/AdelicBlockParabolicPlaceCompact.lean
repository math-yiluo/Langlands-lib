import Langlands.Global.AdelicBlockParabolicPlaceNorm
import Langlands.Representation.Archimedean.RealJacquetReduction
import Langlands.Representation.Archimedean.RealLeviSlices

/-! # The compact Levi at one archimedean place -/

noncomputable section

open scoped BigOperators Matrix

namespace Langlands.GeneralLinear.BlockShape

open Langlands.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uR u

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [RCLike R]

local notation "K" => Matrix.unitaryGroup (Fin n) R

/-- The product of the standard compact groups of the Levi blocks. -/
abbrev CompactLevi := ∀ i : Fin B.length, Matrix.unitaryGroup (Fin (B.size i)) R

private theorem leviEmbedding_mem_unitary (k : B.CompactLevi R) :
    (B.leviEmbedding R (fun i => Unitary.toUnits (k i))).val ∈ K := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  let d := Matrix.blockDiagonal' (fun i => (k i).val)
  let e := Matrix.reindexRingEquiv R B.indexEquiv
  have hc : (e d)ᴴ = e (dᴴ) := rfl
  change (e d) * (e d)ᴴ = 1
  rw [hc, ← map_mul, ← map_one e]
  congr 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  congr 1
  funext i
  exact Matrix.mem_unitaryGroup_iff.mp (k i).property

/-- The actual block Levi embedding restricts to the product of its compact subgroups. -/
def compactLeviEmbedding : B.CompactLevi R →* K where
  toFun k := ⟨(B.leviEmbedding R (fun i => Unitary.toUnits (k i))).val,
    leviEmbedding_mem_unitary B R k⟩
  map_one' := by
    apply Subtype.ext
    change (B.leviEmbedding R (fun i => Unitary.toUnits ((1 : B.CompactLevi R) i))).val = 1
    have h : (fun i => Unitary.toUnits ((1 : B.CompactLevi R) i)) = (1 : B.Levi R) := by
      funext i
      exact Unitary.toUnits.map_one
    rw [h, map_one, Units.val_one]
  map_mul' k l := by
    apply Subtype.ext
    change (B.leviEmbedding R (fun i => Unitary.toUnits ((k * l) i))).val =
      ((B.leviEmbedding R (fun i => Unitary.toUnits (k i))) *
        (B.leviEmbedding R (fun i => Unitary.toUnits (l i)))).val
    rw [← map_mul]
    congr 2
    funext i
    exact Unitary.toUnits.map_mul (k i) (l i)

@[simp]
theorem toUnits_compactLeviEmbedding (k : B.CompactLevi R) :
    Unitary.toUnits (B.compactLeviEmbedding R k) =
      B.leviEmbedding R (fun i => Unitary.toUnits (k i)) := Units.ext rfl

/-- A reflection in one Levi coordinate is the ambient reflection in that
coordinate under consecutive block numbering. -/
theorem compactLeviEmbedding_signReflection (i : Fin B.length) (a : Fin (B.size i)) :
    B.compactLeviEmbedding ℝ (Pi.mulSingle i (signReflection (B.size i) a)) =
      signReflection n (B.index i a) := by
  classical
  apply Subtype.ext
  ext p q
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective p
  obtain ⟨⟨l, c⟩, rfl⟩ := B.indexEquiv.surjective q
  let k : ∀ j : Fin B.length, Matrix.unitaryGroup (Fin (B.size j)) ℝ :=
    Pi.mulSingle i (signReflection (B.size i) a)
  change B.leviEmbedding ℝ (fun j => Unitary.toUnits (k j)) (B.index j b) (B.index l c) =
    Matrix.diagonal (fun x => if x = B.index i a then (-1 : ℝ) else 1)
      (B.index j b) (B.index l c)
  by_cases hjl : j = l
  · subst l
    rw [B.leviEmbedding_apply_same]
    by_cases hji : j = i
    · subst j
      simp [k, signReflection, Matrix.diagonal_apply, (B.index i).injective.eq_iff]
    · have hbi : B.index j b ≠ B.index i a :=
        fun h => hji (congrArg Sigma.fst (B.indexEquiv.injective h))
      simp [k, Pi.mulSingle_eq_of_ne hji, Matrix.diagonal_apply, Matrix.one_apply,
        (B.index j).injective.eq_iff, hbi]
  · have hbc : B.index j b ≠ B.index l c :=
      fun h => hjl (congrArg Sigma.fst (B.indexEquiv.injective h))
    rw [B.leviEmbedding_apply_ne ℝ _ b c hjl, Matrix.diagonal_apply_ne _ hbc]

/-- For the real compact Levi, the actual single-slot inclusion agrees with
the inclusion used for the compact block slices of real standard modules. -/
theorem compactLeviEmbedding_real_single {c : ℕ} (sz : Fin c → ℕ) (hs : ∀ i, 0 < sz i)
    (i : Fin c) (k : Matrix.unitaryGroup (Fin (sz i)) ℝ) :
    (⟨c, sz, hs, rfl⟩ : BlockShape (∑ j, sz j)).compactLeviEmbedding ℝ (Pi.mulSingle i k) =
      RealLeviSlices.embK sz i k := by
  classical
  apply Subtype.ext
  let l : ∀ j : Fin c, Matrix.unitaryGroup (Fin (sz j)) ℝ := Pi.mulSingle i k
  change RealLeviChart.blockDiagHom sz (fun j => (l j).val) =
    RealLeviChart.blockDiagHom sz (Pi.mulSingle i k.val)
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp [l]
  · simp [l, Pi.mulSingle_eq_of_ne hj]

private theorem norm_det_unitary (d : ℕ) (k : Matrix.unitaryGroup (Fin d) R) :
    ‖k.val.det‖ = 1 := by
  have hd := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp k.property)
  rw [Matrix.star_eq_conjTranspose, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
  have hn := congrArg norm hd
  rw [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg k.val.det]

open Langlands.Global
open AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F]

/-- The actual adelic half-modulus is one on the embedded real compact Levi. -/
theorem parabolicHalfCharacter_realPlace_compactLevi
    (v : {v : NumberField.InfinitePlace F // v.IsReal})
    (k : ∀ i : Fin B.length, Matrix.unitaryGroup (Fin (B.size i)) ℝ) :
    (parabolicHalfCharacter F B (AdelicBlockParabolic.realPlaceInclusion F B v
      (B.leviInParabolic ℝ (fun i => Unitary.toUnits (k i)))) : ℂ) = 1 := by
  rw [coe_parabolicHalfCharacter_realPlace]
  simp [realPlaceModulusValue, ← Real.norm_eq_abs, norm_det_unitary]

/-- The actual adelic half-modulus is one on the embedded complex compact Levi. -/
theorem parabolicHalfCharacter_complexPlace_compactLevi
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (k : ∀ i : Fin B.length, Matrix.unitaryGroup (Fin (B.size i)) ℂ) :
    (parabolicHalfCharacter F B (AdelicBlockParabolic.complexPlaceInclusion F B v
      (B.leviInParabolic ℂ (fun i => Unitary.toUnits (k i)))) : ℂ) = 1 := by
  rw [coe_parabolicHalfCharacter_complexPlace]
  simp [complexPlaceModulusValue, norm_det_unitary]

end Langlands.GeneralLinear.BlockShape
