import Langlands.GroupScheme.Examples.HermitianSignedDeterminant

/-! # Completing an even Hermitian hyperbolic decomposition -/

noncomputable section

namespace Langlands.GroupScheme.HermitianRoot.HyperbolicDecomposition

open SU3Root MultiHyperbolic
open _root_.Algebra
open HermitianMatrix (Form det_adjoint)

universe u

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [IsQuadraticExtension F L] [Algebra.IsSeparable F L] {n r : ℕ}

local notation "c" => fieldInvolution F L
local notation "bar" => RingInvolution.bar (fieldInvolution F L)

private theorem exists_complete (H : Form c (Fin n))
    (D : HyperbolicDecomposition H.linearFirst r) (hD : D.middleDimension ≤ 2)
    (hn : Even n) {b : L} (hb : bar b * b = H.signedDeterminant) :
    ∃ U : HyperbolicDecomposition H.linearFirst (n / 2), U.middleDimension = 0 := by
  classical
  have hd : n = D.middleDimension + 2 * r := by simpa using D.finrank_eq
  have heven : 2 * (n / 2) = n := by obtain ⟨m, hm⟩ := hn; omega
  by_cases hm₀ : D.middleDimension = 0
  · have hr : r = n / 2 := by omega
    subst r
    exact ⟨D, hm₀⟩
  have hm : D.middleDimension = 2 := by omega
  let P := coordinateMatrix D.basisCoordinates
  let δ := ((P : Matrix (Fin n) (Fin n) L)).det
  have hgram :
      HermitianMatrix.adjoint c (P : Matrix (Fin n) (Fin n) L) *
          (H.gram : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) =
        (MultiHyperbolic.gram D.middleGram).submatrix D.indexEquiv D.indexEquiv :=
    D.gram_congruence H.gram H.linearFirst_eq_dotProduct
  have hdet : (-1 : L) ^ r * D.middleGram.det =
      bar δ * (H.gram : Matrix (Fin n) (Fin n) L).det * δ := by
    have h := congrArg Matrix.det hgram
    rw [Matrix.det_submatrix_equiv_self D.indexEquiv, det_gram, Fintype.card_fin,
      Matrix.det_mul, Matrix.det_mul, det_adjoint] at h
    exact h.symm
  have hne : D.middleGram.det ≠ 0 := by
    intro hz
    have hδ : δ ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero P
    have hz' := hdet.symm
    rw [hz, mul_zero] at hz'
    exact (mul_ne_zero (mul_ne_zero ((map_ne_zero bar).2 hδ)
      (Matrix.GeneralLinearGroup.det_ne_zero H.gram)) hδ) hz'
  let e : Fin D.middleDimension ≃ Fin 2 := finCongr hm
  let G := D.middleGram.submatrix e.symm e.symm
  have hGdet : G.det = D.middleGram.det := Matrix.det_submatrix_equiv_self e.symm _
  have hG : HermitianMatrix.adjoint c G = G := by
    ext i j
    change bar (D.middleGram (e.symm j) (e.symm i)) = D.middleGram (e.symm i) (e.symm j)
    exact H.bar_linearFirst _ _
  let J : Form c (Fin 2) := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G (hGdet ▸ hne), hG⟩
  have hJ : bar (b * δ) * (b * δ) = J.signedDeterminant := by
    have hsign : (-1 : L) ^ (n / 2) * (-1) ^ r = -1 := by
      rw [← pow_add, show n / 2 + r = 2 * r + 1 by omega, pow_succ, pow_mul,
        neg_one_sq, one_pow, one_mul]
    calc
      _ = (bar b * b) * (bar δ * δ) := by rw [map_mul]; ring
      _ = (-1) ^ (n / 2) * (bar δ * (H.gram : Matrix (Fin n) (Fin n) L).det * δ) := by
        rw [hb, Form.signedDeterminant]
        ring
      _ = J.signedDeterminant := by
        rw [← hdet, ← mul_assoc, hsign]
        change -1 * D.middleGram.det = (-1 : L) ^ (2 / 2) * G.det
        simp [hGdet]
  obtain ⟨x, hx, hxx⟩ := J.exists_isotropic_of_signedDeterminant hJ
  let T : (Fin 2 → L) ≃ₗ[L] (Fin D.middleDimension → L) :=
    LinearEquiv.piCongrLeft' L (fun _ => L) e.symm
  have hT (i : Fin 2) : T (Pi.single i 1) = Pi.single (e.symm i) 1 := by
    ext j
    simp [T, Pi.single_apply, ← e.eq_symm_apply]
  let f : (Fin 2 → L) →ₗ[L] (Fin n → L) :=
    { toFun := fun z => D.coordinates.symm (0, (T z, 0))
      map_add' := by
        intro a b
        rw [← D.coordinates.symm.map_add]
        simp
      map_smul' := by
        intro a z
        rw [← D.coordinates.symm.map_smul]
        simp }
  have hf : J.linearFirst = (H.linearFirst.compl₂ f).comp f := by
    apply (Pi.basisFun L (Fin 2)).ext
    intro i
    apply (Pi.basisFun L (Fin 2)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
    rw [J.linearFirst_eq_dotProduct]
    change dotProduct (fun i' => bar ((Pi.single j (1 : L) : Fin 2 → L) i'))
        (G.mulVec (Pi.single i 1)) =
      H.linearFirst (D.coordinates.symm (0, (T (Pi.single i 1), 0)))
        (D.coordinates.symm (0, (T (Pi.single j 1), 0)))
    rw [hT, hT]
    simp [G, HyperbolicDecomposition.middleGram, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hmiddle (a b : L) : D.middlePairing (a • T x) (b • T x) = 0 := by
    have hz : H.linearFirst (f (a • x)) (f (b • x)) = 0 := by
      change ((H.linearFirst.compl₂ f).comp f) (a • x) (b • x) = 0
      rw [← hf]
      rw [J.linearFirst.map_smul a x, LinearMap.smul_apply,
        (J.linearFirst x).map_smulₛₗ b x, hxx, smul_zero, smul_zero]
    rw [D.pairing_eq] at hz
    simpa [f] using hz
  let g : ((Fin r → L) × L) →ₗ[L] (Fin n → L) :=
    { toFun := fun z => D.coordinates.symm (z.1, (z.2 • T x, 0))
      map_add' := by
        intro a b
        rw [← D.coordinates.symm.map_add]
        simp [add_smul]
      map_smul' := by
        intro a z
        rw [← D.coordinates.symm.map_smul]
        simp [mul_smul] }
  have hg : Function.Injective g := by
    intro z w he
    have hh : (z.1, (z.2 • T x, (0 : Fin r → L))) = (w.1, (w.2 • T x, 0)) :=
      D.coordinates.symm.injective he
    have hmid : z.2 • T x = w.2 • T x := congrArg (fun v => v.2.1) hh
    have hs : (z.2 - w.2) • T x = 0 := by
      rw [sub_smul, hmid, sub_self]
    have hTx : T x ≠ 0 := fun h => hx (T.injective (h.trans T.map_zero.symm))
    have hleft : z.1 = w.1 :=
      congrArg (fun v : (Fin r → L) × ((Fin D.middleDimension → L) × (Fin r → L)) => v.1) hh
    exact Prod.ext hleft (sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hTx))
  have hrange : Module.finrank L g.range = n / 2 := by
    rw [← (LinearEquiv.ofInjective g hg).finrank_eq, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Module.finrank_self]
    omega
  have hiso (z w : g.range) : H.linearFirst (z : Fin n → L) w = 0 := by
    obtain ⟨a, ha⟩ := z.property
    obtain ⟨b, hb⟩ := w.property
    rw [← ha, ← hb, D.pairing_eq]
    simp [g, hmiddle]
  obtain ⟨U⟩ := nonempty_hyperbolicDecomposition_of_totallyIsotropic H.linearFirst
    H.bar_linearFirst H.linearFirst_nondegenerate g.range hiso
  rw [hrange] at U
  have hU : n = U.middleDimension + 2 * (n / 2) := by simpa using U.finrank_eq
  exact ⟨U, by omega⟩

/-- An even Hermitian form with signed determinant in the norm image
has a full hyperbolic decomposition if it has one with at most two middle coordinates. -/
def completeOfSignedDeterminant (H : Form c (Fin n))
    (D : HyperbolicDecomposition H.linearFirst r) (hD : D.middleDimension ≤ 2)
    (hn : Even n) {b : L} (hb : bar b * b = H.signedDeterminant) :
    {U : HyperbolicDecomposition H.linearFirst (n / 2) // U.middleDimension = 0} :=
  ⟨(exists_complete H D hD hn hb).choose, (exists_complete H D hD hn hb).choose_spec⟩

end Langlands.GroupScheme.HermitianRoot.HyperbolicDecomposition
