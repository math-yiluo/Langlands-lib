import Langlands.GroupScheme.Rational.NumberFieldSkewProjectiveComplement
import Langlands.GroupScheme.Rational.NumberFieldSkewValueApproximation
import Langlands.GroupScheme.Rational.NumberFieldBalancedBinarySkew
import Langlands.GroupScheme.Quaternionic.QuaternionicOppositeSkewValues
import Langlands.GroupScheme.Quaternionic.SkewHermitianTensorBasis

/-! # Isotropy of higher-rank skew-hermitian quaternion forms -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

section OrthogonalBasis

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module F V] [Module D V] [IsScalarTower F D V] [FiniteDimensional D V]
  (B : AntihermitianForm τ V)

private theorem orthogonalBasis_with_two_lines (hτ : ∃ a, τ a ≠ a)
    (hB : B.toBilin.SeparatingLeft) (e z : V) (he : B e e ≠ 0) (hz : B z z ≠ 0)
    (hez : B e z = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin 2 ⊕ Fin n) D V),
      Module.finrank D V = 2 + n ∧ b (.inl 0) = e ∧ b (.inl 1) = z ∧
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧ (∀ i, B (b i) (b i) ≠ 0) := by
  let W := B.orthogonalLine e
  let zW : W := ⟨z, by rw [B.mem_orthogonalLine, B.skew e z, hez, τ.map_zero, neg_zero]⟩
  let C := B.pullback W.subtype
  let U := C.orthogonalLine zW
  let n := Module.finrank D U
  have hzW : C zW zW ≠ 0 := hz
  have hC := B.orthogonalLine_separatingLeft hB e he
  obtain ⟨c, hc, hcdiag⟩ := AntihermitianForm.orthogonalBasis F D τ U (C.pullback U.subtype)
    hτ (C.orthogonalLine_separatingLeft hC zW hzW)
  let d₁ := Module.Basis.singleton (Fin 1) D
  let d₂ := (d₁.prod c).map (C.splitLine zW hzW)
  let d := (d₁.prod d₂).map (B.splitLine e he)
  let p : Fin 2 ⊕ Fin n ≃ Fin 1 ⊕ (Fin 1 ⊕ Fin n) :=
    ((finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm.sumCongr (Equiv.refl (Fin n))).trans
      (Equiv.sumAssoc (Fin 1) (Fin 1) (Fin n))
  let b := d.reindex p.symm
  have hd₁ (i : Fin 1) : d (.inl i) = e := by
    simp [d, d₁]
    change (1 : D) • e + ((0 : W) : V) = e
    rw [one_smul, Submodule.coe_zero, add_zero]
  have hd₂ (i : Fin 1 ⊕ Fin n) : d (.inr i) = (d₂ i : V) := by
    simp [d]
    change (0 : D) • e + (d₂ i : V) = (d₂ i : V)
    rw [zero_smul, zero_add]
  have dz (i : Fin 1) : d₂ (.inl i) = zW := by
    simp [d₂, d₁]
    change (1 : D) • zW + ((0 : U) : W) = zW
    rw [one_smul, Submodule.coe_zero, add_zero]
  have dc (i : Fin n) : d₂ (.inr i) = (c i : W) := by
    simp [d₂]
    change (0 : D) • zW + (c i : W) = (c i : W)
    rw [zero_smul, zero_add]
  have dorth (i j : Fin 1 ⊕ (Fin 1 ⊕ Fin n)) (h : i ≠ j) : B (d i) (d j) = 0 := by
    rcases i with i | i <;> rcases j with j | j
    · exact (h (congrArg Sum.inl (Subsingleton.elim i j))).elim
    · have hje : B (d₂ j : V) e = 0 := (d₂ j).property
      rw [hd₁, hd₂, B.skew (d₂ j : V) e, hje, τ.map_zero, neg_zero]
    · rw [hd₂, hd₁]
      exact (d₂ i).property
    · rw [hd₂, hd₂]
      change C (d₂ i) (d₂ j) = 0
      rcases i with i | i <;> rcases j with j | j
      · exact (h (by rw [Subsingleton.elim i j])).elim
      · have hjz : C (c j : W) zW = 0 := (c j).property
        rw [dz, dc, C.skew (c j : W) zW, hjz, τ.map_zero, neg_zero]
      · rw [dc, dz]
        exact (c i).property
      · rw [dc, dc]
        exact hc i j (fun h' => h (by rw [h']))
  have ddiag (i : Fin 1 ⊕ (Fin 1 ⊕ Fin n)) : B (d i) (d i) ≠ 0 := by
    rcases i with i | (i | i)
    · rwa [hd₁]
    · rw [hd₂, dz]
      exact hz
    · rw [hd₂, dc]
      exact hcdiag i
  have hb (i : Fin 2 ⊕ Fin n) : b i = d (p i) := by
    rw [show b = d.reindex p.symm from rfl, Module.Basis.reindex_apply, Equiv.symm_symm]
  refine ⟨n, b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  · rw [hb, show p (.inl 0) = .inl 0 from rfl, hd₁]
  · rw [hb, show p (.inl 1) = .inr (.inl 0) from rfl, hd₂, dz]
  · intro i j h
    simpa only [hb] using dorth (p i) (p j) (fun h' => h (p.injective h'))
  · intro i
    rw [hb]
    exact ddiag (p i)

end OrthogonalBasis

section BlockPairing

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module F V] [Module D V] [IsScalarTower F D V]
  {I L : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  (B : AntihermitianForm τ V) (b : Module.Basis (I ⊕ L) D V)
  (horth : ∀ i j, i ≠ j → B (b i) (b j) = 0)
  (R : Type u) [Field R] [Algebra F R]

private theorem matrixSesqBilin_diagonal_tmul {J : Type} [Fintype J] [DecidableEq J]
    (d : J → D) (x y : J → R ⊗[F] D) :
    (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] Matrix.diagonal d)) x y =
      ∑ i, x i * ((1 : R) ⊗ₜ[F] d i) * τ.baseChange R (y i) := by
  rw [FirstKindInvolution.matrixSesqBilin_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i, coefficientEquiv_tmul, Matrix.diagonal_apply_eq]
  · intro j _ hij
    rw [coefficientEquiv_tmul, Matrix.diagonal_apply_ne _ (Ne.symm hij),
      TensorProduct.tmul_zero, mul_zero, zero_mul]
  · exact fun hi => (hi (Finset.mem_univ i)).elim

include horth in
private theorem tensor_pairing_in_diagonal_blocks (x y : R ⊗[F] V) :
    let H := Matrix.diagonal (fun i : I => B (b (.inl i)) (b (.inl i)))
    let G := Matrix.diagonal (fun j : L => B (b (.inr j)) (b (.inr j)))
    let c := AntihermitianForm.tensorBasisCoordinates (F := F) b R
    let τR := τ.baseChange R
    LinearMap.BilinMap.baseChange R B.toBilin x y =
      τR.matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H))
        (fun i => c x (.inl i)) (fun i => c y (.inl i)) +
      τR.matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G))
        (fun i => c x (.inr i)) (fun i => c y (.inr i)) := by
  dsimp only
  rw [matrixSesqBilin_diagonal_tmul R, matrixSesqBilin_diagonal_tmul R, B.tensor_pairing_in_basis b R]
  let c := AntihermitianForm.tensorBasisCoordinates (F := F) b R
  have h (i : I ⊕ L) : (∑ j, c x i * ((1 : R) ⊗ₜ[F] B (b i) (b j)) * τ.baseChange R (c y j)) =
      c x i * ((1 : R) ⊗ₜ[F] B (b i) (b i)) * τ.baseChange R (c y i) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hij
      rw [horth i j (Ne.symm hij), TensorProduct.tmul_zero, mul_zero, zero_mul]
    · exact fun hi => (hi (Finset.mem_univ i)).elim
  change (∑ i, ∑ j, c x i * ((1 : R) ⊗ₜ[F] B (b i) (b j)) * τ.baseChange R (c y j)) = _
  simp_rw [h]
  exact Fintype.sum_sum_type _

private theorem matrixSesqBilin_tmul {J : Type} [Fintype J] [DecidableEq J]
    (H : Matrix J J D) (x y : J → D) :
    (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H))
      (fun i => (1 : R) ⊗ₜ[F] x i) (fun i => (1 : R) ⊗ₜ[F] y i) =
      (1 : R) ⊗ₜ[F] τ.sesqForm H x y := by
  simp only [FirstKindInvolution.matrixSesqBilin_apply, coefficientEquiv_tmul,
    FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    FirstKindInvolution.sesqForm, TensorProduct.tmul_sum]

include horth in
private theorem pairing_in_diagonal_blocks (x y : I → D) (z t : L → D) :
    let H := Matrix.diagonal (fun i : I => B (b (.inl i)) (b (.inl i)))
    let G := Matrix.diagonal (fun j : L => B (b (.inr j)) (b (.inr j)))
    B (b.equivFun.symm (Sum.elim x z)) (b.equivFun.symm (Sum.elim y t)) =
      τ.sesqForm H x y + τ.sesqForm G z t := by
  intro H G
  let r := b.equivFun.symm (Sum.elim x z)
  let s := b.equivFun.symm (Sum.elim y t)
  let c := AntihermitianForm.tensorBasisCoordinates (F := F) b F
  have hr (i : I ⊕ L) : c ((1 : F) ⊗ₜ[F] r) i = (1 : F) ⊗ₜ[F] Sum.elim x z i := by
    rw [AntihermitianForm.tensorBasisCoordinates_tmul]
    exact congrArg ((1 : F) ⊗ₜ[F] ·) (congrFun (b.equivFun.apply_symm_apply (Sum.elim x z)) i)
  have hs (i : I ⊕ L) : c ((1 : F) ⊗ₜ[F] s) i = (1 : F) ⊗ₜ[F] Sum.elim y t i := by
    rw [AntihermitianForm.tensorBasisCoordinates_tmul]
    exact congrArg ((1 : F) ⊗ₜ[F] ·) (congrFun (b.equivFun.apply_symm_apply (Sum.elim y t)) i)
  have h := tensor_pairing_in_diagonal_blocks B b horth F ((1 : F) ⊗ₜ[F] r) ((1 : F) ⊗ₜ[F] s)
  dsimp only at h
  change LinearMap.BilinMap.baseChange F B.toBilin ((1 : F) ⊗ₜ[F] r) ((1 : F) ⊗ₜ[F] s) =
    (τ.baseChange F).matrixSesqBilin (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] H))
      (fun i => c ((1 : F) ⊗ₜ[F] r) (.inl i)) (fun i => c ((1 : F) ⊗ₜ[F] s) (.inl i)) +
    (τ.baseChange F).matrixSesqBilin (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] G))
      (fun i => c ((1 : F) ⊗ₜ[F] r) (.inr i)) (fun i => c ((1 : F) ⊗ₜ[F] s) (.inr i)) at h
  simp only [LinearMap.BilinMap.baseChange_tmul, mul_one, hr, hs, Sum.elim_inl,
    Sum.elim_inr, matrixSesqBilin_tmul, ← TensorProduct.tmul_add] at h
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective h

end BlockPairing

section LocalBlocks

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] [Field R] [Algebra F R]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I D}

local notation "τ" => σ.quaternionConjugation hdim hsym

private theorem oppositeUnitValues_in_basis
    (hH : (τ).IsAntihermitian H) (hu : IsUnit H) {n : ℕ} [Nonempty (Fin n)]
    (b : Module.Basis (Fin 2 ⊕ Fin n) D (I → D))
    (horth : ∀ i j, i ≠ j → (AntihermitianForm.ofMatrix hH) (b i) (b j) = 0)
    {H₁ : Matrix (Fin 2) (Fin 2) D} {G : Matrix (Fin n) (Fin n) D}
    (h₁ : H₁ = Matrix.diagonal (fun i => (AntihermitianForm.ofMatrix hH) (b (.inl i)) (b (.inl i))))
    (h₂ : G = Matrix.diagonal (fun j => (AntihermitianForm.ofMatrix hH) (b (.inr j)) (b (.inr j))))
    (hH₁ : (τ).IsAntihermitian H₁) (hG : (τ).IsAntihermitian G) (hu₁ : IsUnit H₁) (huG : IsUnit G)
    (h : let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
      ∃ (x : I → R ⊗[F] D) (i : I), IsUnit (x i) ∧
        ∑ j, ∑ k, x j * M j k * (τ).baseChange R (x k) = 0) :
    FirstKindInvolution.HasOppositeUnitValues (R := R) τ H₁ G := by
  obtain ⟨x, i, hi, hx⟩ := h
  let B := AntihermitianForm.ofMatrix hH
  let c := AntihermitianForm.tensorBasisCoordinates (F := F) b R
  obtain ⟨t, s, ht, hts⟩ := (τ).tensorGram_exists_isotropic_with_partner hH R hu hi hx
  have hp := tensor_pairing_in_diagonal_blocks B b horth R t t
  have hq := tensor_pairing_in_diagonal_blocks B b horth R t s
  dsimp only at hp hq
  rw [← h₁, ← h₂] at hp hq
  have ht' := hp.symm.trans ht
  have hs' := hq.symm.trans hts
  have vH := (τ).matrix_coefficientEquiv_tmul_eq_neg (R := R) hH₁.1
  have vG := (τ).matrix_coefficientEquiv_tmul_eq_neg (R := R) hG.1
  obtain ⟨r, a, ha, hr⟩ := σ.quaternionic_exists_opposite_unit_values hdim hsym vH vG
    (FirstKindInvolution.isUnit_coefficientEquiv_tmul (R := R) hu₁)
    (FirstKindInvolution.isUnit_coefficientEquiv_tmul (R := R) huG)
    (fun i => c t (.inl i)) (fun i => c s (.inl i)) (fun i => c t (.inr i)) (fun i => c s (.inr i))
    ht' hs'
  exact ⟨a, r, ha, hr⟩

end LocalBlocks

private theorem diagonal_skew_regular {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
    [Invertible (2 : F)] (τ : FirstKindInvolution F D) {I : Type} [Fintype I] [DecidableEq I]
    (a : I → D) (ha : ∀ i, τ (a i) = -(a i)) (hu : ∀ i, a i ≠ 0) :
    τ.IsAntihermitian (Matrix.diagonal a) ∧ IsUnit (Matrix.diagonal a) := by
  refine ⟨⟨?_, ?_⟩, (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (hu i)).map
    (Matrix.diagonalRingHom I D)⟩
  · ext i j
    rw [FirstKindInvolution.matrix_apply, Matrix.neg_apply]
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using ha i
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), τ.map_zero, neg_zero]
  · intro i
    rw [Matrix.diagonal_apply_eq]
    exact KneserThree.mem_alternatingSubspace_of_neg τ (mul_invOf_self (2 : F)) (ha i)

/-- A skew-hermitian form of rank at least four over a number-field quaternion
  division algebra represents zero nontrivially if it has a nonsingular local
  isotropic row everywhere. -/
def NumberFieldHigherRankSkewIsotropyStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (I : Type) [Fintype I] [DecidableEq I], 4 ≤ Fintype.card I →
    ∀ (H : Matrix I I D), τ.IsAntihermitian H → IsUnit H →
      τ.IsLocallyNonsingularIsotropic H → ∃ x : I → D, x ≠ 0 ∧ τ.sesqForm H x x = 0

theorem numberFieldHigherRankSkewIsotropy : NumberFieldHigherRankSkewIsotropyStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ I _ _ hI H hH hu hl
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let V := I → D
  have hV : Module.finrank D V = Fintype.card I := Module.finrank_fintype_fun_eq_card D
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank D V by omega)
  let B := AntihermitianForm.ofMatrix hH
  have hB := AntihermitianForm.ofMatrix_separatingLeft hH hu
  have hτ : ∃ a : D, τ a ≠ a := by
    let l := σ.quaternionAlternatingUnit hdim hsym
    refine ⟨(l : D), ?_⟩
    intro h
    have heq : τ (l : D) = -(l : D) := KneserThree.Quaternion.conj_ell σ hdim hsym
    rw [heq] at h
    have hz := congrArg (fun a : D => a + l) h
    rw [neg_add_cancel, ← two_smul F] at hz
    exact smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) l.ne_zero hz.symm
  obtain ⟨e, he⟩ := B.exists_self_ne_zero hτ hB
  obtain ⟨z, hz, hez, s, hzs⟩ := numberFieldSkewProjectiveComplement F D σ hdim hsym I H hH hu hl e he
  by_cases hzz : B z z = 0
  · exact ⟨z, hz, hzz⟩
  have hs : s ≠ 0 := by
    intro h
    exact hzz (hzs.trans (by rw [h, zero_smul]))
  obtain ⟨n, b, hdimV, hb₀, hb₁, hb, hdiag⟩ := orthogonalBasis_with_two_lines B hτ hB e z he hzz hez
  change Module.finrank D V = 2 + n at hdimV
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let d (i : Fin 2 ⊕ Fin n) := B (b i) (b i)
  let H₁ := Matrix.diagonal (fun i : Fin 2 => d (.inl i))
  let G := Matrix.diagonal (fun j : Fin n => d (.inr j))
  have ha (i : Fin 2 ⊕ Fin n) : τ (d i) = -(d i) := by
    exact neg_eq_iff_eq_neg.mp (B.skew (b i) (b i)).symm
  have hq : τ (B e e) = -(B e e) := by
    exact neg_eq_iff_eq_neg.mp (B.skew e e).symm
  have hproportional : H₁ = Matrix.diagonal ![B e e, s • B e e] := by
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i
    · change B (b (.inl 0)) (b (.inl 0)) = B e e
      rw [hb₀]
    · change B (b (.inl 1)) (b (.inl 1)) = s • B e e
      rw [hb₁]
      exact hzs
  obtain ⟨hH₁, hu₁⟩ := diagonal_skew_regular τ (fun i : Fin 2 => d (.inl i))
    (fun i => ha (.inl i)) (fun i => hdiag (.inl i))
  obtain ⟨hG, huG⟩ := diagonal_skew_regular τ (fun j : Fin n => d (.inr j))
    (fun j => ha (.inr j)) (fun j => hdiag (.inr j))
  have hloc (v : Global.Place F) :
      FirstKindInvolution.HasOppositeUnitValues (R := Global.placeCompletion F v) τ H₁ G := by
    rcases v with v | v
    · exact oppositeUnitValues_in_basis (R := v.Completion) σ hdim hsym hH hu b hb rfl rfl
        hH₁ hG hu₁ huG (hl (.inl v))
    · exact oppositeUnitValues_in_basis (R := Global.FiniteCompletion F v) σ hdim hsym hH hu b hb rfl rfl
        hH₁ hG hu₁ huG (hl (.inr v))
  have hcof := numberFieldBalancedBinarySkew F D σ hdim hsym (B e e) he hq s hs
  rw [← hproportional] at hcof
  obtain ⟨x, hx, hp, hxp⟩ := FirstKindInvolution.numberFieldSkewValueApproximation F D σ hdim hsym
    n H₁ G hG hloc hcof
  obtain ⟨y, hy⟩ := numberFieldBinarySkewRepresentation F D σ hdim hsym H₁ hH₁ hu₁
    (-(τ.sesqForm G x x)) hp hx hxp
  let r := b.equivFun.symm (Sum.elim y x)
  have hr : B r r = 0 := by
    have eq := pairing_in_diagonal_blocks B b hb y y x x
    change B r r = τ.sesqForm H₁ y y + τ.sesqForm G x x at eq
    rw [eq, hy, neg_add_cancel]
  refine ⟨r, ?_, hr⟩
  intro h
  have h' : Sum.elim y x = 0 := by
    simpa only [r, LinearEquiv.apply_symm_apply, _root_.map_zero] using congrArg b.equivFun h
  have hx' : x = 0 := funext fun i => congrFun h' (.inr i)
  apply hx
  rw [hx']
  simp [FirstKindInvolution.sesqForm]

end Langlands.GroupScheme.Quaternionic
