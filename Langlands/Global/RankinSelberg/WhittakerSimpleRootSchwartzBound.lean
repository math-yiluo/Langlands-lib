import Langlands.Global.RankinSelberg.AdelicRowMajorant
import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.WhittakerSimpleRootDecay
import Langlands.Global.RankinSelberg.WhittakerSimpleRootFiniteSupport

/-! # Schwartz--Bruhat bounds on diagonal Whittaker families -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.GroupScheme.GeneralLinear
open Langlands.Automorphic.CuspidalWhittaker

local instance rootSchwartzSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The mixed archimedean projection on units. -/
def rootArchUnit : Ideles F →* (mixedEmbedding.mixedSpace F)ˣ :=
  Units.map (((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F))).toMonoidHom)

/-- The finite projection on units. -/
def rootFiniteUnit : Ideles F →* (FiniteAdeles F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F)).toMonoidHom

theorem archCoord_gaugeDiagonalPoint (n : ℕ) (d : Fin n → Ideles F) :
    archCoord F (gaugeDiagonalPoint F n d) =
      diagonalMatrixUnits (mixedEmbedding.mixedSpace F) (fun i => rootArchUnit F (d i)) := by
  simp only [archCoord, gaugeDiagonalPoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  apply Matrix.ext
  intro i j
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((diagonalMatrixUnits (Adeles F) d : Matrix (Fin n) (Fin n) (Adeles F)) i j).1 = _
  by_cases hij : i = j
  · subst j
    simp only [diagonalMatrixUnits_val, Matrix.diagonal_apply_eq]
    rfl
  · simp only [diagonalMatrixUnits_val, Matrix.diagonal_apply_ne _ hij]
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem finCoord_gaugeDiagonalPoint (n : ℕ) (d : Fin n → Ideles F) :
    finCoord F (gaugeDiagonalPoint F n d) =
      diagonalMatrixUnits (FiniteAdeles F) (fun i => rootFiniteUnit F (d i)) := by
  simp only [finCoord, gaugeDiagonalPoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  apply Matrix.ext
  intro i j
  change ((diagonalMatrixUnits (Adeles F) d : Matrix (Fin n) (Fin n) (Adeles F)) i j).2 = _
  by_cases hij : i = j
  · subst j
    simp only [diagonalMatrixUnits_val, Matrix.diagonal_apply_eq]
    rfl
  · simp [diagonalMatrixUnits_val, Matrix.diagonal_apply_ne _ hij]

theorem archimedeanCoordinates_gaugeSimpleRootRow (r : ℕ)
    (d : Fin (r + 1) → Ideles F) :
    archimedeanCoordinates F r (gaugeSimpleRootRow F r d) =
      fun i : Fin r => (rootArchUnit F (d i.castSucc) : mixedEmbedding.mixedSpace F) *
        ((rootArchUnit F (d i.succ))⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) := by
  funext i
  change (rootArchUnit F (d i.castSucc / d i.succ) : mixedEmbedding.mixedSpace F) = _
  rw [map_div, div_eq_mul_inv, Units.val_mul]

theorem finiteCoordinates_gaugeSimpleRootRow (r : ℕ)
    (d : Fin (r + 1) → Ideles F) :
    finiteCoordinates F r (gaugeSimpleRootRow F r d) =
      fun i : Fin r => (rootFiniteUnit F (d i.castSucc) : FiniteAdeles F) *
        ((rootFiniteUnit F (d i.succ))⁻¹ : (FiniteAdeles F)ˣ) := by
  funext i
  change (rootFiniteUnit F (d i.castSucc / d i.succ) : FiniteAdeles F) = _
  rw [map_div, div_eq_mul_inv, Units.val_mul]

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

set_option maxHeartbeats 800000 in
/-- A common determinant power and the analytic decay hypotheses give a
Schwartz--Bruhat bound in the simple roots, uniformly over compact right factors.
The bounding test function retains coordinate-magnitude symmetries. -/
theorem exists_simpleRoot_schwartzBruhat_bound
    [CompactSpace (AdeleQuotient F)]
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (hβ : ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (f : V)
    {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ (c : F) (Φ : RowVector F r → ℂ), c ≠ 0 ∧ Φ ∈ schwartzBruhat F r ∧
      (∀ (d : Fin (r + 1) → Ideles F) (k : Points F (r + 1)), k ∈ C →
        ‖whittaker F r ψ f (gaugeDiagonalPoint F (r + 1) d * k)‖ ≤
          detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d * k) ^ β *
            ‖Φ (gaugeSimpleRootRow F r d)‖) ∧
      ∀ x y,
        (∀ i a, ‖(archimedeanCoordinates F r x i).1 a‖ =
          ‖(archimedeanCoordinates F r y i).1 a‖) →
        (∀ i b, ‖(archimedeanCoordinates F r x i).2 b‖ =
          ‖(archimedeanCoordinates F r y i).2 b‖) →
        (∀ i, (algebraMap F (FiniteAdeles F) c * finiteCoordinates F r x i ∈
            integralFiniteAdeles F ↔
          algebraMap F (FiniteAdeles F) c * finiteCoordinates F r y i ∈
            integralFiniteAdeles F)) → Φ x = Φ y := by
  let J := (Fin (r + 1) → Ideles F) × C
  let z : J → RowVector F r := fun j => gaugeSimpleRootRow F r j.1
  let a : J → Points F (r + 1) := fun j => gaugeDiagonalPoint F (r + 1) j.1 * j.2
  let w : J → ℝ := fun j =>
    ‖whittaker F r ψ f (a j)‖ / detNorm F (r + 1) (a j) ^ β
  have hD : ∀ j, 0 < detNorm F (r + 1) (a j) ^ β :=
    fun j => Real.rpow_pos_of_pos (detNorm_pos F (r + 1) (a j)) β
  have hw : ∀ j, 0 ≤ w j := fun j => div_nonneg (norm_nonneg _) (hD j).le
  have hrapid : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      (1 + ‖archimedeanCoordinates F r (z j)‖) ^ N * w j ≤ B := by
    intro N
    obtain ⟨B, hB, hbound⟩ :=
      exists_simpleRoot_row_decay_of_detPower F hV β hβ ψ hψ N f hC
    refine ⟨B, hB, fun j => ?_⟩
    dsimp only [w]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (hD j)).mpr
    simpa only [z, archimedeanCoordinates_gaugeSimpleRootRow, a] using
      hbound (gaugeDiagonalPoint F (r + 1) j.1) (fun i => rootArchUnit F (j.1 i))
        (archCoord_gaugeDiagonalPoint F _ _) j.2 j.2.property
  obtain ⟨c, hc, hden⟩ := exists_simpleRoot_finite_denominator F hV ψ hψ f hC
  have hsupp : ∀ j, w j ≠ 0 →
      finiteCoordinates F r (z j) ∈ SchwartzMajorant.denominatorRows F r c := by
    intro j hj
    have hW : whittaker F r ψ f (a j) ≠ 0 := by
      intro h
      apply hj
      simp only [w, h, norm_zero, zero_div]
    intro i
    simpa only [z, finiteCoordinates_gaugeSimpleRootRow] using
      hden (gaugeDiagonalPoint F (r + 1) j.1) (fun i => rootFiniteUnit F (j.1 i))
        (finCoord_gaugeDiagonalPoint F _ _) j.2 j.2.property hW i
  obtain ⟨Φ, hΦ, hbound, hsymm⟩ :=
    SchwartzMajorant.exists_schwartzBruhat_majorant F z w hw hrapid c hc hsupp
  refine ⟨c, Φ, hc, hΦ, ?_, hsymm⟩
  intro d k hk
  have h := (div_le_iff₀ (hD (d, ⟨k, hk⟩))).mp (hbound (d, ⟨k, hk⟩))
  simpa only [w, a, z, mul_comm] using h

end Langlands.Global.RankinSelbergGlobal.Unfolding
