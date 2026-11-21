import Langlands.Global.AdelicInducedPrincipalSeries
import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.ArchimedeanBlockCompactLevi
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible

/-! # Normalized tensor evaluation along an archimedean parabolic -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean
open GeneralLinear
open Archimedean.RealLeviChart (pos)
open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_tprod)
open AdelicParabolicInduction (orderedBlockShape borelParabolic borelBlockUnipotent
  leviProjection_borelParabolic)

universe u v

variable (𝕜 : Type u) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)

/-- The positive local half modulus on the block Levi. The real dimension of
the field gives the normalization of the determinant norm. -/
def localLeviHalf (m : B.Levi 𝕜) : ℂ :=
  (Real.sqrt (∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (‖(m i).val.det‖ ^ Module.finrank ℝ 𝕜) ^ B.size j /
      (‖(m j).val.det‖ ^ Module.finrank ℝ 𝕜) ^ B.size i) : ℂ)

private theorem norm_det_eq_one {g : Langlands.GeneralLinear n 𝕜}
    (hg : g ∈ unitaryCompact 𝕜 n) : ‖g.val.det‖ = 1 := by
  have h := congrArg Matrix.det ((mem_unitaryCompact_iff 𝕜 n g).mp hg)
  rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg g.val.det]

omit B in
private theorem det_upperUnipotent (w : Langlands.GeneralLinear.upperUnipotent n 𝕜) :
    w.val.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular w.2.1]
  simp only [w.2.2, Finset.prod_const_one]

omit B in
/-- Normalized evaluation in stages, determined by the compact block tensor.
For a parabolic element use ambient Iwasawa and extract the compact Levi
coordinates of its compact factor. -/
theorem principalSeries_parabolic_tensorValue
    {c : ℕ} (size : Fin c → ℕ) (hsize : ∀ i, 0 < size i)
    (χ : ℕ → 𝕜ˣ → ℂ) (χi : Fin c → ℕ → 𝕜ˣ → ℂ)
    (hχ : ∀ i (j : Fin (size i)), χ (pos size i j) = χi i j)
    {V : Fin c → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (e : ∀ i, V i →ₗ[ℂ] (Langlands.GeneralLinear (size i) 𝕜 → ℂ))
    (he : ∀ i x, e i x ∈ principalSeries 𝕜 (size i) (χi i))
    {f : Langlands.GeneralLinear (∑ i, size i) 𝕜 → ℂ}
    (hf : f ∈ principalSeries 𝕜 (∑ i, size i) χ)
    (k : Langlands.GeneralLinear (∑ i, size i) 𝕜) (t : ⨂[ℂ] i, V i)
    (ht : ∀ q : ∀ i, unitaryCompact 𝕜 (size i),
      indexedEvaluation e t (fun i => (q i).val) =
        f ((compactLeviEmbedding 𝕜 (orderedBlockShape size hsize) q).val * k))
    (p : (orderedBlockShape size hsize).parabolic 𝕜) :
    f (p.val * k) =
      localLeviHalf 𝕜 (orderedBlockShape size hsize)
        ((orderedBlockShape size hsize).leviProjection 𝕜 p) *
        indexedEvaluation e t ((orderedBlockShape size hsize).leviProjection 𝕜 p) := by
  let S := orderedBlockShape size hsize
  obtain ⟨a, w, κ, hκ, hp⟩ := PrincipalSeries.exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact p.val
  let b : S.parabolic 𝕜 := borelParabolic size hsize 𝕜 a w
  have hb : b.val = Iwasawa.diagonalUnits a * w.val := rfl
  have hκp : κ ∈ S.parabolic 𝕜 := by
    have h : b.val⁻¹ * p.val ∈ S.parabolic 𝕜 := mul_mem (inv_mem b.property) p.property
    rwa [hp, ← hb, inv_mul_cancel_left] at h
  let q := compactLeviProjection 𝕜 S ⟨κ, hκp⟩ hκ
  have hq : (compactLeviEmbedding 𝕜 S q).val = κ :=
    congrArg Subtype.val (compactLeviEmbedding_projection 𝕜 S ⟨κ, hκp⟩ hκ)
  have hmul : p = b * ⟨κ, hκp⟩ := Subtype.ext (hp.trans (congrArg (· * κ) hb.symm))
  have hμ (i : Fin c) : S.leviProjection 𝕜 p i =
      Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
        (borelBlockUnipotent size hsize 𝕜 w i).val * (q i).val := by
    rw [hmul, map_mul, Pi.mul_apply]
    rw [show S.leviProjection 𝕜 b i = _ from leviProjection_borelParabolic size hsize 𝕜 a w i]
    rfl
  have hnorm (i : Fin c) :
      ‖(S.leviProjection 𝕜 p i).val.det‖ ^ Module.finrank ℝ 𝕜 = blockDiagonalAbs size 𝕜 a i := by
    rw [hμ i, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      det_upperUnipotent, mul_one, norm_mul, norm_det_eq_one 𝕜 (q i).property, mul_one]
    rfl
  let C := ∏ i, principalSeriesCharacter 𝕜 (size i) (χi i) (fun j => a (pos size i j))
  let E := indexedEvaluation e
  let L := (LinearMap.proj (S.leviProjection 𝕜 p)).comp E
  let R := C • (LinearMap.proj (fun i => (q i).val)).comp E
  have hLR : L = R := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change E (PiTensorProduct.tprod ℂ x) (S.leviProjection 𝕜 p) =
      C * E (PiTensorProduct.tprod ℂ x) (fun i => (q i).val)
    rw [indexedEvaluation_tprod, indexedEvaluation_tprod]
    unfold C
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hμ i]
    exact (he i (x i)).2 _ _ _
  have heval : E t (S.leviProjection 𝕜 p) = C * E t (fun i => (q i).val) :=
    LinearMap.congr_fun hLR t
  change f (p.val * k) = localLeviHalf 𝕜 S (S.leviProjection 𝕜 p) * E t (S.leviProjection 𝕜 p)
  rw [hp, mul_assoc, hf.2, principalSeriesCharacter_eq_outerHalf_mul_inner size 𝕜 χ χi hχ,
    mul_assoc, heval, ht q, hq]
  unfold localLeviHalf
  simp only [hnorm]
  rfl

section GlobalNormalization

open NumberField AdelicBlockDeterminantCharacter

variable (F : Type v) [Field F] [NumberField F] {s : ℕ} (S : BlockShape s)

/-- The local real half modulus is the restriction of the adelic half character. -/
theorem localLeviHalf_realPlace (v : {v : InfinitePlace F // v.IsReal})
    (p : S.parabolic ℝ) :
    localLeviHalf ℝ S (S.leviProjection ℝ p) =
      (parabolicHalfCharacter F S (AdelicBlockParabolic.realPlaceInclusion F S v p) : ℂ) := by
  rw [coe_parabolicHalfCharacter_realPlace, localLeviHalf, realPlaceModulusValue]
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]

/-- The local complex half modulus is the restriction of the adelic half character. -/
theorem localLeviHalf_complexPlace (v : {v : InfinitePlace F // v.IsComplex})
    (p : S.parabolic ℂ) :
    localLeviHalf ℂ S (S.leviProjection ℂ p) =
      (parabolicHalfCharacter F S (AdelicBlockParabolic.complexPlaceInclusion F S v p) : ℂ) := by
  rw [coe_parabolicHalfCharacter_complexPlace, localLeviHalf, complexPlaceModulusValue]
  simp only [Complex.finrank_real_complex]

end GlobalNormalization

end Langlands.Global.ArchimedeanCompactBlocks
