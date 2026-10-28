import Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra
import Langlands.Representation.RankinSelberg.RankOneExtensionStableJacquetData

/-!
# Lower-parabolic covariance of the rank-one extension sections

The lower block `B(m, x, a) = [m, 0; x, a]` lies in the opposite parabolic of the lower
shape `(t + 1, 1)`, with Levi part `(m, a)`. The scalar coefficient of an actual lower
induced section therefore satisfies
`c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, where
`δ(m, a) = |det m| / |a|^(t + 1)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Matrix HarmonicAnalysis
open scoped NNReal

universe uF uW

section Algebra

variable {K : Type uF} [Field K] {t : ℕ}

/-- The large block `t + 1` of the lower shape. -/
abbrev rankOneExtensionLowerLargeBlock (t : ℕ) : Fin (rankOneExtensionLowerShape t).length :=
  ⟨0, Nat.zero_lt_two⟩

/-- The scalar block `1` of the lower shape. -/
abbrev rankOneExtensionLowerScalarBlock (t : ℕ) : Fin (rankOneExtensionLowerShape t).length :=
  ⟨1, Nat.one_lt_two⟩

theorem rankOneExtensionLowerShape_index_val (j : Fin (rankOneExtensionLowerShape t).length)
    (b : Fin ((rankOneExtensionLowerShape t).size j)) :
    ((rankOneExtensionLowerShape t).index j b).val = (if j.val = 0 then 0 else t + 1) + b.val := by
  change ((rankOneExtensionLowerShape t).indexEquiv ⟨j, b⟩).val = _
  rw [GeneralLinear.BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  fin_cases j <;> simp

theorem rankOneExtensionLowerBlock_mem_oppositeParabolic (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    rankOneExtensionLowerBlock t m x a ∈ (rankOneExtensionLowerShape t).oppositeParabolic K := by
  rw [GeneralLinear.BlockShape.mem_oppositeParabolic_iff]
  intro i j b c hij
  rw [rankOneExtensionLowerBlock_entry, rankOneExtensionLowerShape_index_val,
    rankOneExtensionLowerShape_index_val]
  have hj2 : j.val < 2 := j.isLt
  rw [Fin.lt_def] at hij
  have hi : i.val = 0 := by omega
  have hj : j.val = 1 := by omega
  have hi' : i = rankOneExtensionLowerLargeBlock t := Fin.ext hi
  have hj' : j = rankOneExtensionLowerScalarBlock t := Fin.ext hj
  subst hi' hj'
  have hb : b.val < t + 1 := b.isLt
  simp only [rankOneExtensionLowerLargeBlock, rankOneExtensionLowerScalarBlock]
  simp [hb]
  intro h
  exact absurd h (by omega)

/-- The lower block as an element of the actual opposite parabolic. -/
def rankOneExtensionLowerBlockParabolic (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) : (rankOneExtensionLowerShape t).oppositeParabolic K :=
  ⟨rankOneExtensionLowerBlock t m x a, rankOneExtensionLowerBlock_mem_oppositeParabolic m x a⟩

@[simp] theorem rankOneExtensionLowerBlockParabolic_val (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    (rankOneExtensionLowerBlockParabolic m x a :
      Langlands.GeneralLinear (1 + (t + 1)) K) = rankOneExtensionLowerBlock t m x a :=
  rfl

/-- The large Levi component of `B(m, x, a)` is `m`. -/
theorem oppositeLeviProjection_lowerBlock_large (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    (rankOneExtensionLowerShape t).oppositeLeviProjection K
      (rankOneExtensionLowerBlockParabolic m x a) (rankOneExtensionLowerLargeBlock t) = m := by
  apply Units.ext
  ext b c
  rw [GeneralLinear.BlockShape.oppositeLeviProjection_apply,
    rankOneExtensionLowerBlockParabolic_val, rankOneExtensionLowerBlock_entry,
    rankOneExtensionLowerShape_index_val, rankOneExtensionLowerShape_index_val]
  have hb : b.val < t + 1 := b.isLt
  have hc : c.val < t + 1 := c.isLt
  simp [hb, hc]
  rfl

/-- The scalar Levi component of `B(m, x, a)` has determinant `a`. -/
theorem oppositeLeviProjection_lowerBlock_scalar_det (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    GeneralLinear.determinant ((rankOneExtensionLowerShape t).oppositeLeviProjection K
      (rankOneExtensionLowerBlockParabolic m x a) (rankOneExtensionLowerScalarBlock t)) = a := by
  apply Units.ext
  have h1 : ∀ M : Langlands.GeneralLinear 1 K,
      ((GeneralLinear.determinant M : Kˣ) : K) = M.val 0 0 := fun M => Matrix.det_fin_one _
  refine (h1 _).trans ?_
  change rankOneExtensionLowerBlock t m x a
    ((rankOneExtensionLowerShape t).index (rankOneExtensionLowerScalarBlock t) ⟨0, Nat.one_pos⟩)
    ((rankOneExtensionLowerShape t).index (rankOneExtensionLowerScalarBlock t)
      ⟨0, Nat.one_pos⟩) = _
  rw [rankOneExtensionLowerBlock_entry, rankOneExtensionLowerShape_index_val]
  simp

end Algebra

section TensorExt

/-- A linear identity `φ₁ ∘ A = c • φ₂` on a tensor product of modules follows from the
same identity on pure tensors. -/
theorem piTensorProduct_comp_apply_eq_mul {ι : Type*} {s : ι → Type*}
    [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    (A : PiTensorProduct ℂ s →ₗ[ℂ] PiTensorProduct ℂ s) (φ₁ φ₂ : PiTensorProduct ℂ s →ₗ[ℂ] ℂ)
    (c : ℂ) (h : ∀ v : ∀ i, s i,
      φ₁ (A (PiTensorProduct.tprod ℂ v)) = c * φ₂ (PiTensorProduct.tprod ℂ v))
    (T : PiTensorProduct ℂ s) : φ₁ (A T) = c * φ₂ T := by
  have hlin : φ₁ ∘ₗ A = c • φ₂ :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  simpa using LinearMap.congr_fun hlin T

end TensorExt

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

local instance : ∀ i : Fin 2,
    AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instAddCommGroup i.rev

local instance : ∀ i : Fin 2,
    Module ℂ (rankOneExtensionLowerCarrier (W := W) i) :=
  fun i => Shahidi.pairCarrier.instModule ℂ i.rev

/-- Contraction of an arbitrary pure tensor in the reversed carrier. -/
theorem rankOneExtensionTensorContraction_tprod (ℓ : W →ₗ[ℂ] ℂ)
    (v : ∀ i : Fin 2, rankOneExtensionLowerCarrier (W := W) i) :
    rankOneExtensionTensorContraction ℓ (PiTensorProduct.tprod ℂ v) =
      ℓ (v 0) * (v 1 : ULift.{uW} ℂ).down := by
  have h : PiTensorProduct.tprod ℂ v =
      PiTensorProduct.reindex ℂ (Shahidi.pairCarrier (ULift.{uW} ℂ) W) Fin.revPerm
        (PiTensorProduct.tprod ℂ (Shahidi.pairVector (v 1) (v 0))) := by
    rw [PiTensorProduct.reindex_tprod]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact rankOneExtensionTensorContraction_pure ℓ (v 0) (v 1)

/-- The lower Levi modulus is `|det m| / |a| ^ (t + 1)`. -/
theorem rankOneExtensionLowerShape_leviModulus
    (L : (rankOneExtensionLowerShape t).Levi F.Carrier) :
    F.canonicalTopologicalData.leviModulus (rankOneExtensionLowerShape t) L =
      F.canonicalTopologicalData.determinantNorm (t + 1) (L (rankOneExtensionLowerLargeBlock t)) /
        F.canonicalTopologicalData.determinantNorm 1
          (L (rankOneExtensionLowerScalarBlock t)) ^ (t + 1) := by
  rw [PadicField.TopologicalData.leviModulus_apply]
  simp only [Finset.prod_filter]
  erw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  simp
  rfl

/-- The coefficient formula
`c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, with
`δ(m, a) = |det m| / |a| ^ (t + 1)`. -/
theorem rankOneExtensionLowerSectionCoefficient_lowerBlock_mul
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ)
    (m : Langlands.GeneralLinear (t + 1) F.Carrier) (x : Fin (t + 1) → F.Carrier)
    (a : F.Carrierˣ) (g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) :
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t m x a * g) =
      (((NNReal.sqrt ((F.canonicalTopologicalData.determinantNorm (t + 1) m /
          F.canonicalTopologicalData.normalizedAbsUnits a ^ (t + 1) : ℝ≥0ˣ) : ℝ≥0) : ℝ) :
            ℂ))⁻¹ * ((χ a : ℂˣ) : ℂ) *
        rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ m)
          (rankOneExtensionLowerSectionEval F t χ σ f g) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  set L := (rankOneExtensionLowerShape t).oppositeLeviProjection F.Carrier
    (rankOneExtensionLowerBlockParabolic m x a) with hL
  have hLm : L (rankOneExtensionLowerLargeBlock t) = m :=
    oppositeLeviProjection_lowerBlock_large m x a
  have hLa : GeneralLinear.determinant (L (rankOneExtensionLowerScalarBlock t)) = a :=
    oppositeLeviProjection_lowerBlock_scalar_det m x a
  have hcov := F.canonicalTopologicalData.normalizedOppositeParabolicInduced_covariant _ _ f
    (rankOneExtensionLowerBlockParabolic m x a) g
  have key : ∀ T : rankOneExtensionLowerTensor (W := W),
      rankOneExtensionTensorContraction ℓ.val
        ((rankOneExtensionLowerShape t).blockTensor (V := rankOneExtensionLowerCarrier (W := W))
          (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ) L T) =
        ((χ a : ℂˣ) : ℂ) * rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ m) T := by
    refine piTensorProduct_comp_apply_eq_mul _ _ _ _ fun v => ?_
    erw [GeneralLinear.BlockShape.blockTensor_tprod]
    erw [rankOneExtensionTensorContraction_tprod, rankOneExtensionTensorContraction_tprod]
    change ℓ.val (σ (L (rankOneExtensionLowerLargeBlock t)) (v 0)) *
          (((χ (GeneralLinear.determinant (L (rankOneExtensionLowerScalarBlock t))) : ℂˣ) : ℂ) *
            (v 1 : ULift.{uW} ℂ).down) =
        ((χ a : ℂˣ) : ℂ) * (ℓ.val (σ m (v 0)) * (v 1 : ULift.{uW} ℂ).down)
    rw [hLm, hLa]
    ring
  have hδ : F.canonicalTopologicalData.leviModulus (rankOneExtensionLowerShape t) L =
      F.canonicalTopologicalData.determinantNorm (t + 1) m /
        F.canonicalTopologicalData.normalizedAbsUnits a ^ (t + 1) := by
    rw [rankOneExtensionLowerShape_leviModulus, hLm]
    congr 2
    exact congrArg F.canonicalTopologicalData.normalizedAbsUnits hLa
  change rankOneExtensionTensorContraction ℓ.val
      (Induction.eval _ _ f (rankOneExtensionLowerBlock t m x a * g)) = _
  erw [hcov]
  rw [map_smul, smul_eq_mul]
  erw [key]
  rw [hδ, mul_assoc]
  rfl

end Padic

end Langlands.RankinSelberg
