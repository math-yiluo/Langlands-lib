import Langlands.Representation.RankinSelberg.UnimodularityStatement
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.BigOperators.Pi

/-!
# Right invariance of normalized general linear Haar measure

The modular character is trivial by scalar centrality, permutation symmetry
of diagonal matrices, and conjugacy of every transvection to its inverse.
Regular Haar uniqueness then applies to the existing normalized measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Matrix MeasureTheory
open scoped NNReal

universe uF uI

namespace GeneralLinearUnimodularity

variable {F : Type uF} [Field F] {ι : Type uI} [Fintype ι] [DecidableEq ι]

private def diagonalUnits : (ι → Fˣ) →* GeneralLinearGroup ι F where
  toFun d :=
    { val := diagonal (fun i => (d i : F))
      inv := diagonal (fun i => ((d i)⁻¹ : Fˣ))
      val_inv := by simp [diagonal_mul_diagonal]
      inv_val := by simp [diagonal_mul_diagonal] }
  map_one' := by apply Units.ext; simp
  map_mul' d e := by apply Units.ext; simp [diagonal_mul_diagonal]

private def permutationUnit (σ : Equiv.Perm ι) : GeneralLinearGroup ι F where
  val := (1 : Matrix ι ι F).submatrix σ id
  inv := (1 : Matrix ι ι F).submatrix σ.symm id
  val_inv := by simp
  inv_val := by simp

private theorem character_eq_of_intertwine (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (g h p : GeneralLinearGroup ι F) (hp : p * g = h * p) : χ g = χ h := by
  have hn : χ p ≠ 0 := ((Group.isUnit p).map χ).ne_zero
  apply mul_left_cancel₀ hn
  simpa only [map_mul, mul_comm (χ h)] using congrArg χ hp

private theorem character_diagonal_permute (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (d : ι → Fˣ) (σ : Equiv.Perm ι) :
    χ (diagonalUnits d) = χ (diagonalUnits (d ∘ σ)) := by
  apply character_eq_of_intertwine χ _ _ (permutationUnit σ)
  apply Units.ext
  change (1 : Matrix ι ι F).submatrix σ id * diagonal (fun i => (d i : F)) =
    diagonal (fun i => (d (σ i) : F)) * (1 : Matrix ι ι F).submatrix σ id
  ext i j
  simp [mul_diagonal, diagonal_mul, submatrix, one_apply]
  split_ifs with h
  · simp [h]
  · simp

private theorem character_diagonal_single (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (hscalar : ∀ a : Fˣ, χ (GeneralLinearGroup.scalar ι a) = 1)
    (i : ι) (a : Fˣ) : χ (diagonalUnits (Pi.mulSingle i a)) = 1 := by
  have heq (j : ι) : χ (diagonalUnits (Pi.mulSingle j a)) =
      χ (diagonalUnits (Pi.mulSingle i a)) := by
    convert character_diagonal_permute χ (Pi.mulSingle j a) (Equiv.swap i j) using 1
    congr 2
    funext k
    simp only [Function.comp_apply, Pi.mulSingle_apply]
    have he : Equiv.swap i j k = j ↔ k = i := by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    simp [he]
  have hp : χ (diagonalUnits (Pi.mulSingle i a)) ^ Fintype.card ι = 1 := by
    calc
      _ = ∏ j : ι, χ (diagonalUnits (Pi.mulSingle j a)) := by simp [heq]
      _ = χ (diagonalUnits (fun _ : ι => a)) := by
        change (∏ j : ι, (χ.comp diagonalUnits) (Pi.mulSingle j a)) =
          (χ.comp diagonalUnits) (fun _ : ι => a)
        rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = 1 := hscalar a
  exact (pow_eq_one_iff_of_nonneg (zero_le) (ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))).mp hp

private theorem character_diagonal (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (hscalar : ∀ a : Fˣ, χ (GeneralLinearGroup.scalar ι a) = 1)
    (d : ι → Fˣ) : χ (diagonalUnits d) = 1 := by
  change (χ.comp diagonalUnits) d = 1
  rw [← Finset.univ_prod_mulSingle d, map_prod]
  exact Finset.prod_eq_one fun i _ => character_diagonal_single χ hscalar i (d i)

private def transvectionUnit (t : TransvectionStruct ι F) : GeneralLinearGroup ι F :=
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

private theorem character_transvection (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (t : TransvectionStruct ι F) : χ (transvectionUnit t) = 1 := by
  let d : ι → Fˣ := Pi.mulSingle t.i (-1)
  have heq : χ (transvectionUnit t) = χ (transvectionUnit t.inv) := by
    apply character_eq_of_intertwine χ _ _ (diagonalUnits d)
    apply Units.ext
    change diagonal (fun i => (d i : F)) * t.toMatrix =
      t.inv.toMatrix * diagonal (fun i => (d i : F))
    ext i j
    simp only [diagonal_mul, mul_diagonal, TransvectionStruct.toMatrix,
      TransvectionStruct.inv_i, TransvectionStruct.inv_j, TransvectionStruct.inv_c,
      transvection, Matrix.add_apply, one_apply, Matrix.single_apply]
    by_cases hi : i = t.i <;> by_cases hj : j = t.j <;> by_cases hij : i = j
      <;> simp_all [d, Pi.mulSingle_apply, t.hij, t.hij.symm, eq_comm]
  have hm : transvectionUnit t * transvectionUnit t.inv = 1 := by
    apply Units.ext
    exact t.mul_inv
  have hp : χ (transvectionUnit t) ^ 2 = 1 := by
    simpa only [map_mul, map_one, ← heq, pow_two] using congrArg χ hm
  exact (pow_eq_one_iff_of_nonneg (zero_le) (by decide : 2 ≠ 0)).mp hp

private theorem character_eq_one (χ : GeneralLinearGroup ι F →* ℝ≥0)
    (hscalar : ∀ a : Fˣ, χ (GeneralLinearGroup.scalar ι a) = 1)
    (g : GeneralLinearGroup ι F) : χ g = 1 := by
  let P : Matrix ι ι F → Prop := fun A =>
    ∀ u : GeneralLinearGroup ι F, u.val = A → χ u = 1
  apply diagonal_transvection_induction_of_det_ne_zero P g.val g.det_ne_zero
    (hdiag := ?_) (htransvec := ?_) (hmul := ?_) g rfl
  · intro d hd u hu
    have hd' : ∀ i, d i ≠ 0 := by
      simpa only [det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies] using hd
    let du : ι → Fˣ := fun i => Units.mk0 (d i) (hd' i)
    have he : u = diagonalUnits du := Units.ext hu
    rw [he]
    exact character_diagonal χ hscalar du
  · intro t u hu
    have he : u = transvectionUnit t := Units.ext hu
    rw [he]
    exact character_transvection χ t
  · intro A B hA hB hPA hPB u hu
    let a := GeneralLinearGroup.mkOfDetNeZero A hA
    let b := GeneralLinearGroup.mkOfDetNeZero B hB
    have he : u = a * b := Units.ext hu
    rw [he, map_mul, hPA a rfl, hPB b rfl, mul_one]

end GeneralLinearUnimodularity

/-- The existing integral-subgroup-normalized Haar measure on `GL_(n+1)` is
right invariant in every rank and every field universe. -/
theorem generalLinearHaarRightInvariant
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    GeneralLinearHaarRightInvariantStatement F n := by
  have : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F))
  let G := Matrix.GeneralLinearGroup (Fin (n + 1)) F
  have hscalar (a : Fˣ) :
      Measure.modularCharacter (GeneralLinearGroup.scalar (Fin (n + 1)) a) = 1 := by
    change Measure.modularCharacterFun _ = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (generalLinearHaar F n)]
    have he : (fun x : G => x * GeneralLinearGroup.scalar (Fin (n + 1)) a) =
        (fun x : G => GeneralLinearGroup.scalar (Fin (n + 1)) a * x) := by
      funext x
      exact (GeneralLinearGroup.scalar_commute a x).symm
    have hmap : Measure.map (fun x : G => x * GeneralLinearGroup.scalar (Fin (n + 1)) a)
        (generalLinearHaar F n) = generalLinearHaar F n := by
      rw [he, map_mul_left_eq_self]
    have hf (ν : Measure G) [ν.IsHaarMeasure] (hν : ν = generalLinearHaar F n) :
        Measure.haarScalarFactor ν (generalLinearHaar F n) = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self _
    exact hf _ hmap
  have htrivial (g : G) : Measure.modularCharacterFun g = 1 :=
    GeneralLinearUnimodularity.character_eq_one Measure.modularCharacter hscalar g
  refine ⟨fun g => ?_⟩
  have : (Measure.map (fun x : G => x * g) (generalLinearHaar F n)).Regular :=
    Measure.Regular.map (μ := generalLinearHaar F n) (Homeomorph.mulRight g)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x : G => x * g) (generalLinearHaar F n)) (generalLinearHaar F n),
    ← Measure.modularCharacterFun_eq_haarScalarFactor, htrivial, one_smul]

instance generalLinearHaar_isMulRightInvariant
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    Measure.IsMulRightInvariant (generalLinearHaar F n) :=
  generalLinearHaarRightInvariant F n

-- Check the complete outer telescope, including the order of all instances.
example : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)],
    GeneralLinearHaarRightInvariantStatement F n :=
  @generalLinearHaarRightInvariant

end Langlands.RankinSelberg
