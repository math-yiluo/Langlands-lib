import Langlands.Global.AdelicIwasawaOrbitHeight
import Langlands.Global.ProjectiveHeightSummability

/-! # Summable inverse powers of adelic height on rational points -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

/-- The normalized adelic height of a positive-rank closed matrix realization has a
summable inverse power on the rational points of the group. -/
def RationalAdelicHeightSummabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)),
    0 < N → IsClosedSubgroup rho →
    ∃ d : ℕ, Summable (fun q : RationalGroupPoints F G =>
      (adelicHeight F G rho (rational F G q) ^ d)⁻¹)

private theorem mulHeight_matrixChart_le {F : Type u} [Field F] [NumberField F]
    {n m : ℕ} (hn : 0 < n) (e : Fin m ≃ Option (Fin n × Fin n)) (g : RationalGL F n) :
    let v (i : Fin m) : F := (e i).elim 1 (fun p => g p.1 p.2)
    Height.mulHeight v ≤ AdelicMatrixHeight.height F n (AdelicGL.rational F n g) := by
  intro v
  let w := PrimitiveAdelicHeight.rational F m v
  have hv : v ≠ 0 := by
    intro hz
    have h := congrFun hz (e.symm none)
    simp [v] at h
  rw [← PrimitiveAdelicHeight.height_rational_eq_mulHeight F hv]
  let a := AdelicGL.rational F n g
  change PrimitiveAdelicHeight.height F m w ≤ AdelicMatrixHeight.height F n a
  have hentry (k : Fin m) : w k = (e k).elim 1 (fun p => a p.1 p.2) := by
    cases h : e k <;> simp [w, v, a, h, PrimitiveAdelicHeight.rational, AdelicGL.rational_apply]
  have hfin (p : FinitePlace F) : PrimitiveAdelicHeight.finiteNorm F m w p ≤
      AdelicMatrixHeight.finiteLocal F n a p := by
    apply (pi_norm_le_iff_of_nonneg (MatrixInverseHeight.localMaximum_nonneg _ _)).mpr
    intro k
    rw [hentry]
    cases h : e k with
    | none =>
      simpa [AdelicMatrixHeight.finiteLocal] using
        AdelicMatrixHeight.one_le_finiteLocal F n hn a p
    | some i =>
      simpa only [Option.elim_some] using
        MatrixInverseHeight.entry_le_localMaximum (finiteProjection F p) a i.1 i.2
  have harch (p : InfinitePlace F) : PrimitiveAdelicHeight.infiniteNorm F m w p ≤
      (n : ℝ) * AdelicMatrixHeight.infiniteLocal F n a p := by
    have hb := MatrixInverseHeight.one_le_nat_mul_localMaximum (infiniteProjection F p) hn a
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hb)).mpr
    intro k
    rw [hentry]
    cases h : e k with
    | none => simpa using hb
    | some i =>
      simp only [Option.elim_some]
      exact (MatrixInverseHeight.entry_le_localMaximum (infiniteProjection F p) a i.1 i.2).trans
        (le_mul_of_one_le_left (MatrixInverseHeight.localMaximum_nonneg _ _)
          (by exact_mod_cast Nat.succ_le_of_lt hn))
  have hw : PrimitiveAdelicHeight.IsPrimitive F m w :=
    ⟨1, v, hv, by simp [w]⟩
  exact mul_le_mul
    (Finset.prod_le_prod₀ (fun p _ => pow_nonneg (norm_nonneg _) _) (fun p _ =>
      pow_le_pow_left₀ (norm_nonneg _) (harch p) _))
    (finprod_le_finprod₀ (hw.hasFiniteMulSupport F m) (fun _ => norm_nonneg _)
      (AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal F n hn a) hfin)
    (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun p _ => pow_nonneg (zero_le_one.trans
      (MatrixInverseHeight.one_le_nat_mul_localMaximum (infiniteProjection F p) hn a)) _)

set_option maxHeartbeats 700000 in
/-- Use the affine projective chart whose distinguished coordinate is one, with
all rational representation entries as the other coordinates. -/
theorem rationalAdelicHeightSummability : RationalAdelicHeightSummabilityStatement.{u} := by
  classical
  intro F _ _ G N rho hN hrho
  let I := Option (Fin N × Fin N)
  let m := Fintype.card I
  let e : Fin m ≃ I := (Fintype.equivFin I).symm
  let v (q : RationalGroupPoints F G) (i : Fin m) : F :=
    (e i).elim 1 (fun p => rationalMatrix F G rho q p.1 p.2)
  have hv (q : RationalGroupPoints F G) : v q ≠ 0 := by
    intro hz
    have h := congrFun hz (e.symm none)
    simp [v] at h
  let E (q : RationalGroupPoints F G) := Projectivization.mk F (v q) (hv q)
  have hE : Function.Injective E := by
    intro x y h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp h
    have hc₁ : c = 1 := by
      have h' := congrFun hc (e.symm none)
      simpa [v, Pi.smul_apply, smul_eq_mul] using h'
    rw [hc₁, one_smul] at hc
    have hmat : rationalMatrix F G rho x = rationalMatrix F G rho y := by
      apply Units.ext
      ext i j
      have h' := congrFun hc (e.symm (some (i, j)))
      simpa [v] using h'.symm
    let : IsClosedImmersion rho.hom.hom.left := hrho
    let : Mono rho.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono rho.hom.hom).mp
    exact (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of F) (CommAlgCat.of F F)).injective
      hmat
  obtain ⟨b, _, hs⟩ := summable_projectivization_mulHeight_rpow F (Fin m)
  obtain ⟨d, hd⟩ := exists_nat_ge b
  have hsum : Summable (fun q : RationalGroupPoints F G => (E q).mulHeight ^ (-(d : ℝ))) :=
    (hs d hd).comp_injective hE
  have hpos (q : RationalGroupPoints F G) : 0 < adelicHeight F G rho (rational F G q) :=
    zero_lt_one.trans_le (one_le_adelicHeight F G rho hN _)
  refine ⟨d, Summable.of_nonneg_of_le (fun q => inv_nonneg.mpr (pow_nonneg (hpos q).le _)) ?_ hsum⟩
  · intro q
    have h : Height.mulHeight (v q) ≤ adelicHeight F G rho (rational F G q) := by
      rw [adelicHeight, adelicMatrix_rational]
      exact mulHeight_matrixChart_le hN e (rationalMatrix F G rho q)
    change _ ≤ (E q).mulHeight ^ (-(d : ℝ))
    rw [Real.rpow_neg (Projectivization.mulHeight_pos _).le, Real.rpow_natCast]
    apply (inv_le_inv₀ (pow_pos (hpos q) _) (pow_pos (Projectivization.mulHeight_pos _) _)).mpr
    rw [show (E q).mulHeight = Height.mulHeight (v q) from Projectivization.mulHeight_mk _]
    exact pow_le_pow_left₀ (Height.mulHeight_pos _).le h _

end Langlands.Global.RepresentationGrowth
