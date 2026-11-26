import Langlands.Shimura.Unitary.HermitianCoordinates
import Langlands.Shimura.Unitary.HermitianCongruence
import Langlands.GroupScheme.Examples.HermitianLocalIsotropy
import Langlands.GroupScheme.Examples.EvenHermitianDecomposition
import Langlands.GroupScheme.Examples.HermitianHyperbolicGramCoordinates
import Langlands.GroupScheme.Examples.HermitianMatrixNondegenerate
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices
import Mathlib.Topology.Algebra.Valued.WithVal

/-! # Maximal-Witt coordinates over a quadratic extension of a local field -/

noncomputable section

universe u v w

namespace Langlands.Shimura.FiniteUnitary

open Langlands.GroupScheme Langlands.GroupScheme.SU3Root
open Langlands.GroupScheme.HermitianRoot
open ValuativeRel Filter
open scoped Topology

private theorem nhds_basis_vlt (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsValuativeTopology F] (x : F) : (𝓝 x).HasBasis (fun y : F => y ≠ 0)
      (fun y => {z : F | z - x <ᵥ y}) := by
  refine (IsValuativeTopology.hasBasis_nhds' x).to_hasBasis ?_ ?_
  · intro r hr
    obtain ⟨y, hy⟩ := valuation_surjective r
    have hy' : y ≠ 0 := fun h => hr (by simpa [h] using hy.symm)
    exact ⟨y, hy', fun z hz => by
      simpa only [Set.mem_ofPred_eq, (valuation F).vlt_iff_lt, hy] using hz⟩
  · intro y hy
    exact ⟨valuation F y, (Valuation.zero_iff _).not.mpr hy, fun z hz =>
      ((valuation F).vlt_iff_lt).mpr hz⟩

private theorem continuous_of_vlt {P : Type u} {Q : Type v} [Field P] [Field Q]
    [ValuativeRel P] [ValuativeRel Q] [TopologicalSpace P] [TopologicalSpace Q]
    [IsValuativeTopology P] [IsValuativeTopology Q] (g : P ≃+* Q)
    (hg : ∀ x y, x <ᵥ y ↔ g x <ᵥ g y) : Continuous g := by
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  exact ((nhds_basis_vlt P x).tendsto_iff (nhds_basis_vlt Q (g x))).mpr (fun y hy =>
    ⟨g.symm y, fun h => hy (by simpa [h] using (g.apply_symm_apply y).symm), fun z hz => by
      change g z - g x <ᵥ y
      rw [← map_sub, ← g.apply_symm_apply y]
      exact (hg _ _).mp hz⟩)

private theorem withVal_comap_localField {B : Type v} {F : Type u}
    [Field B] [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (e : B ≃+* F) : IsNonarchimedeanLocalField (WithVal ((valuation F).comap e.toRingHom)) := by
  let V := (valuation F).comap e.toRingHom
  let f : WithVal V ≃+* F := (WithVal.equiv V).trans e
  have hv (x y : WithVal V) : (x <ᵥ y) ↔ f x <ᵥ f y := by
    rw [(WithVal.valuation V).vlt_iff_lt, (valuation F).vlt_iff_lt]
    rfl
  let h : WithVal V ≃ₜ F :=
    ⟨f.toEquiv, continuous_of_vlt f hv, continuous_of_vlt f.symm (fun x y => by
      simpa only [RingEquiv.apply_symm_apply] using (hv (f.symm x) (f.symm y)).symm)⟩
  let : LocallyCompactSpace (WithVal V) := h.locallyCompactSpace_iff.mpr inferInstance
  let : ValuativeRel.IsNontrivial (WithVal V) :=
    (isNontrivial_iff_isNontrivial (WithVal.valuation V)).mpr ⟨by
      obtain ⟨x, hx₀, hx₁⟩ :=
        ((isNontrivial_iff_isNontrivial (valuation F)).mp inferInstance).exists_val_nontrivial
      exact ⟨f.symm x, by
        change valuation F (f (f.symm x)) ≠ 0
        rwa [RingEquiv.apply_symm_apply],
        by
          change valuation F (f (f.symm x)) ≠ 1
          rwa [RingEquiv.apply_symm_apply]⟩⟩
  exact ⟨⟩

section Decomposition

variable {F L : Type v} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L] [Algebra.IsSeparable F L]

private theorem exists_hyperbolicDecomposition_aux (d : ℕ) :
    ∀ {V : Type w} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
      (h : V →ₗ[L] V →ₛₗ[(fieldInvolution F L).bar.toRingHom] L)
      (_hbar : ∀ x y, (fieldInvolution F L).bar (h x y) = h y x),
      h.Nondegenerate → Module.finrank L V = d →
      ∃ r, ∃ D : HyperbolicDecomposition h r, D.middleDimension ≤ 2 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro V _ _ _ h hbar hn hd
    by_cases hdim : d ≤ 2
    · exact ⟨0, HyperbolicDecomposition.zero h, by
        change Module.finrank L V ≤ 2
        rwa [hd]⟩
    obtain ⟨x, hx, hxx⟩ := local_exists_isotropic h hbar (by omega)
    obtain ⟨y, hxy, hyx, hyy⟩ := exists_hyperbolic_partner h hbar hn hx hxx
    have hdim' := hyperbolicMiddle_finrank hxx hxy hyx hyy
    obtain ⟨r, D, hD⟩ := ih (Module.finrank L (hyperbolicMiddle h x y)) (by omega)
      (hyperbolicMiddlePairing h x y) (hyperbolicMiddlePairing_bar h hbar x y)
      (hyperbolicMiddlePairing_nondegenerate hbar hxx hxy hyx hyy hn) rfl
    exact ⟨r + 1, D.cons hbar hxx hxy hyx hyy, hD⟩

/-- A local Hermitian space splits into hyperbolic planes and at most two remaining coordinates. -/
theorem exists_local_hyperbolicDecomposition {V : Type w} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (h : V →ₗ[L] V →ₛₗ[(fieldInvolution F L).bar.toRingHom] L)
    (hbar : ∀ x y, (fieldInvolution F L).bar (h x y) = h y x) (hn : h.Nondegenerate) :
    ∃ r, ∃ D : HyperbolicDecomposition h r, D.middleDimension ≤ 2 :=
  exists_hyperbolicDecomposition_aux (Module.finrank L V) h hbar hn rfl

end Decomposition

open MultiHyperbolic

private def blockOrder {r m n : ℕ} (h : r + (m + r) = n) :
    Index (Fin r) (Fin m) ≃ Fin n :=
  ((Equiv.sumCongr (Equiv.refl (Fin r))
    ((Equiv.sumCongr (Equiv.refl (Fin m)) Fin.revPerm).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr h)

@[simp] private theorem blockOrder_top {r m n : ℕ} (h : r + (m + r) = n) (i : Fin r) :
    (blockOrder h (Sum.inl i)).val = i.val := by simp [blockOrder]

@[simp] private theorem blockOrder_middle {r m n : ℕ} (h : r + (m + r) = n) (i : Fin m) :
    (blockOrder h (Sum.inr (Sum.inl i))).val = r + i.val := by simp [blockOrder]

@[simp] private theorem blockOrder_bottom {r m n : ℕ} (h : r + (m + r) = n) (i : Fin r) :
    (blockOrder h (Sum.inr (Sum.inr i))).val = r + (m + (r - (i.val + 1))) := by
  simp [blockOrder, Fin.val_rev]

private theorem maxWittGram_blockOrder (L : Type v) [Field L] {r m n : ℕ}
    (h : r + (m + r) = n) (hm : m ≤ 1) (i j : Index (Fin r) (Fin m)) :
    maxWittGram L n (blockOrder h i) (blockOrder h j) =
      MultiHyperbolic.gram (1 : Matrix (Fin m) (Fin m) L) i j := by
  have hrev (a b : Index (Fin r) (Fin m)) :
      (blockOrder h a).rev = blockOrder h b ↔
        (blockOrder h a).val + (blockOrder h b).val + 1 = n := by
    rw [Fin.ext_iff, Fin.val_rev]
    have ha := (blockOrder h a).isLt
    have hb := (blockOrder h b).isLt
    omega
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp only [maxWittGram, hrev, blockOrder_top, blockOrder_middle, blockOrder_bottom,
      MultiHyperbolic.gram, Matrix.one_apply, Fin.ext_iff] <;>
    split_ifs <;> first | rfl | exfalso; omega

private theorem exists_block_gram_congruence {L : Type v} [Field L]
    {k : RingInvolution L} {n r : ℕ} (H : HermitianMatrix.Form k (Fin n))
    (D : HyperbolicDecomposition H.linearFirst r)
    (order : Index (Fin r) (Fin D.middleDimension) ≃ Fin n) :
    ∃ P : (Matrix (Fin n) (Fin n) L)ˣ,
      HermitianMatrix.adjoint k (P : Matrix (Fin n) (Fin n) L) *
          (H.gram : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) =
        (MultiHyperbolic.gram D.middleGram).submatrix order.symm order.symm := by
  let M := Matrix (Fin n) (Fin n) L
  let f : (Fin n → L) ≃ₗ[L] (Fin n → L) :=
    (LinearEquiv.piCongrLeft' L (fun _ => L) order.symm).trans D.functionCoordinates.symm
  let P : Mˣ := coordinateMatrix f
  have hf (j : Fin n) : f (Pi.single j 1) =
      D.functionCoordinates.symm (Pi.single (order.symm j) 1) := by
    simp only [f, LinearEquiv.trans_apply]
    apply congrArg D.functionCoordinates.symm
    ext i
    simp [Pi.single_apply, order.eq_symm_apply]
  have hP : HermitianMatrix.adjoint k (P : M) * (H.gram : M) * (P : M) =
      (MultiHyperbolic.gram D.middleGram).submatrix order.symm order.symm := by
    apply Matrix.ext
    intro i j
    change ((((P : M).map k.bar).transpose * (H.gram : M) * (P : M)) i j) = _
    rw [coordinateMatrix_congruence_apply, ← H.linearFirst_eq_dotProduct, hf, hf]
    exact D.functionCoordinates_basis_pairing _ _
  exact ⟨P, hP⟩

section Matrices

variable {F : Type u} {L : Type v} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field L] [CharZero L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L] {n : ℕ} (c : AlgebraInvolution F L)

local notation "M" => Matrix (Fin n) (Fin n) L
local notation "θ" => matrixTranspose c n

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero L] [Algebra.IsQuadraticExtension F L] in
private theorem transpose_diagonal (a : Fin n → L) :
    θ (Matrix.diagonal a) = Matrix.diagonal (fun i => c (a i)) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply_ne, h, Ne.symm h]

private theorem of_quadratic_local_model (hc : ∃ x : L, c x ≠ x) {Q : Prop}
    (withModel : ∀ (R : Type v) [Field R] [ValuativeRel R] [TopologicalSpace R]
      [IsNonarchimedeanLocalField R] [Algebra R L] [Algebra.IsQuadraticExtension R L]
      [Algebra.IsSeparable R L],
      (∀ x, (fieldInvolution R L).bar x = c x) → Q) : Q := by
  let B := (⊥ : IntermediateField F L)
  let e := IntermediateField.botEquiv F L
  let V := (valuation F).comap e.toRingEquiv.toRingHom
  let R := WithVal V
  let : IsNonarchimedeanLocalField R := withVal_comap_localField e.toRingEquiv
  let A : R ≃ₐ[F] F := (WithVal.algEquiv F V).trans e
  let : FiniteDimensional F R := A.symm.toLinearEquiv.finiteDimensional
  let : IsScalarTower F R L := IsScalarTower.of_algebraMap_eq' rfl
  have hdeg : Module.finrank R L = 2 := by
    have hF := A.toLinearEquiv.finrank_eq
    rw [Module.finrank_self] at hF
    have h := Module.finrank_mul_finrank F R L
    rwa [hF, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two F L] at h
  let : Algebra.IsQuadraticExtension R L := ⟨hdeg⟩
  let : CharZero R := ⟨fun {i j} h => Nat.cast_injective (R := L) (by
    have hh : algebraMap R L (i : R) = algebraMap R L (j : R) :=
      congrArg (algebraMap R L) h
    rwa [map_natCast, map_natCast] at hh)⟩
  let d : L ≃ₐ[R] L :=
    { toFun := c
      invFun := c
      left_inv := c.apply_apply
      right_inv := c.apply_apply
      map_add' := c.apply_add
      map_mul' := fun a b => (c.apply_mul a b).trans (mul_comm _ _)
      commutes' := fun x => by
        change c (algebraMap B L x.ofVal) = algebraMap B L x.ofVal
        rw [IsScalarTower.algebraMap_apply B F L, c.apply_algebraMap] }
  obtain ⟨x, hx⟩ := hc
  have hd : d ≠ 1 := fun h => hx (congrArg (fun f : L ≃ₐ[R] L => f x) h)
  have hd' := conjugation_unique R L d hd
  have hbar (x : L) : (fieldInvolution R L).bar x = c x :=
    (congrArg (fun f : L ≃ₐ[R] L => f x) hd').symm
  exact withModel R hbar

private theorem exists_odd_gram_congruence (hc : ∃ x : L, c x ≠ x) (hn : Odd n)
    (H : Mˣ) (hH : θ (H : M) = H) :
    ∃ (P : Mˣ) (b : Lˣ),
      θ (P : M) * (H : M) * (P : M) = (b : L) • maxWittGram L n := by
  apply of_quadratic_local_model c hc
  intro R _ _ _ _ _ _ _ hbar
  have hθ (X : M) : θ X = HermitianMatrix.adjoint (fieldInvolution R L) X := by
    apply Matrix.ext
    intro i j
    exact (hbar (X j i)).symm
  let H' : HermitianMatrix.Form (fieldInvolution R L) (Fin n) :=
    ⟨H, (hθ H).symm.trans hH⟩
  obtain ⟨r, D, hD⟩ := exists_local_hyperbolicDecomposition
    H'.linearFirst H'.bar_linearFirst H'.linearFirst_nondegenerate
  have hr := D.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  obtain ⟨k, hk⟩ := hn
  have hm : D.middleDimension = 1 := by omega
  let order := blockOrder (r := r) (m := D.middleDimension) (n := n) (by omega)
  obtain ⟨P, hP'⟩ := exists_block_gram_congruence H' D order
  have hP : θ (P : M) * (H : M) * (P : M) =
      (MultiHyperbolic.gram D.middleGram).submatrix order.symm order.symm := by
    rw [hθ]
    exact hP'
  let i₀ : Fin D.middleDimension := ⟨0, by omega⟩
  let δ := D.middleGram i₀ i₀
  let X := (θ).units P * H * P
  have hX : (X : M) = (MultiHyperbolic.gram D.middleGram).submatrix order.symm order.symm := hP
  have hδ : δ ≠ 0 := by
    intro h
    apply Matrix.GeneralLinearGroup.det_ne_zero X
    apply Matrix.det_eq_zero_of_column_eq_zero (order (Sum.inr (Sum.inl i₀)))
    intro i
    rw [hX]
    change MultiHyperbolic.gram D.middleGram (order.symm i)
      (order.symm (order (Sum.inr (Sum.inl i₀)))) = 0
    rw [Equiv.symm_apply_apply]
    rcases order.symm i with j | j | j <;> simp [MultiHyperbolic.gram]
    · have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
      simpa [hj, δ] using h
  have hX' : θ (X : M) = X := by
    change θ (θ (P : M) * (H : M) * (P : M)) = θ (P : M) * (H : M) * (P : M)
    simp only [AlgebraInvolution.apply_mul, AlgebraInvolution.apply_apply, hH, mul_assoc]
  have hfix : c δ = δ := by
    have he := congrArg (fun Y : M => Y (order (Sum.inr (Sum.inl i₀)))
      (order (Sum.inr (Sum.inl i₀)))) hX'
    simpa only [matrixTranspose_apply, hX, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      MultiHyperbolic.gram, δ] using he
  let b := Units.mk0 δ hδ
  let w : Index (Fin r) (Fin D.middleDimension) → Lˣ := Sum.elim (fun _ => b) (fun _ => 1)
  let Q : Mˣ := GeneralLinear.diagonalMatrixUnits L (fun i => w (order.symm i))
  refine ⟨P * Q, b, ?_⟩
  simp only [Units.val_mul, AlgebraInvolution.apply_mul]
  rw [show θ (Q : M) * θ (P : M) * (H : M) * ((P : M) * (Q : M)) =
    θ (Q : M) * (θ (P : M) * (H : M) * (P : M)) * (Q : M) by simp only [mul_assoc],
    hP, GeneralLinear.diagonalMatrixUnits_val, transpose_diagonal]
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := order.surjective i
  obtain ⟨j, rfl⟩ := order.surjective j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [show maxWittGram L n (order i) (order j) =
    MultiHyperbolic.gram (1 : Matrix (Fin D.middleDimension) (Fin D.middleDimension) L) i j
      from maxWittGram_blockOrder L _ (by omega) i j]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [MultiHyperbolic.gram, w, b, hfix, mul_ite, ite_mul]
  · have hi : i = i₀ := Fin.ext (by have := i.isLt; omega)
    have hj : j = i₀ := Fin.ext (by have := j.isLt; omega)
    subst i
    subst j
    simp [δ]

private theorem exists_even_gram_congruence (hc : ∃ x : L, c x ≠ x) (hn : Even n)
    (H : Mˣ) (hH : θ (H : M) = H) {b : L}
    (hb : c b * b = (-1) ^ (n / 2) * (H : M).det) :
    ∃ P : Mˣ, θ (P : M) * (H : M) * (P : M) = maxWittGram L n := by
  apply of_quadratic_local_model c hc
  intro R _ _ _ _ _ _ _ hbar
  have hθ (X : M) : θ X = HermitianMatrix.adjoint (fieldInvolution R L) X := by
    ext i j
    exact (hbar (X j i)).symm
  let H' : HermitianMatrix.Form (fieldInvolution R L) (Fin n) :=
    ⟨H, (hθ H).symm.trans hH⟩
  have hb' : (fieldInvolution R L).bar b * b = H'.signedDeterminant := by
    rw [hbar]
    exact hb
  obtain ⟨r, D, hD⟩ := exists_local_hyperbolicDecomposition
    H'.linearFirst H'.bar_linearFirst H'.linearFirst_nondegenerate
  let U := D.completeOfSignedDeterminant H' hD hn hb'
  have hm : U.val.middleDimension = 0 := U.property
  have hdim : n = U.val.middleDimension + 2 * (n / 2) := by simpa using U.val.finrank_eq
  let order := blockOrder (r := n / 2) (m := U.val.middleDimension) (n := n) (by omega)
  obtain ⟨P, hP⟩ := exists_block_gram_congruence H' U.val order
  have hmid : U.val.middleGram = 1 := by
    ext i j
    exact False.elim (by have hi := i.isLt; omega)
  refine ⟨P, ?_⟩
  rw [hθ, show (H : M) = (H'.gram : M) by rfl, hP, hmid]
  ext i j
  obtain ⟨i, rfl⟩ := order.surjective i
  obtain ⟨j, rfl⟩ := order.surjective j
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using
    (maxWittGram_blockOrder L _ (by omega) i j).symm

end Matrices

section CM

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped FiniteExtension

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p) {n : ℕ}

local notation "F" => FiniteCompletion E p
local notation "L" => FiniteCompletion K (Subtype.val (placeAbove K p))
local notation "M" => Matrix (Fin n) (Fin n) L
local notation "c" => nonsplitCoefficientInvolution p hp
local notation "θ" => matrixTranspose (nonsplitCoefficientInvolution p hp) n
local notation "C" => nonsplitCompletionCenterEquiv p hp

private theorem mapMatrix_maxWittAdjoint
    (X : Matrix (Fin n) (Fin n) (LocalCenter E K p)) :
    (C).mapMatrix (maxWittAdjoint (localConjugation E K p) n X) =
      maxWittAdjoint c n ((C).mapMatrix X) := by
  have hJ : (C).mapMatrix (maxWittGram (LocalCenter E K p) n) = maxWittGram L n := by
    apply Matrix.ext
    intro i j
    change C (maxWittGram (LocalCenter E K p) n i j) = maxWittGram L n i j
    simp [maxWittGram, apply_ite]
  have hθ : (C).mapMatrix (matrixTranspose (localConjugation E K p) n X) =
      θ ((C).mapMatrix X) := by
    apply Matrix.ext
    intro i j
    change C (localConjugation E K p (X j i)) = c (C (X j i))
    exact (AlgebraInvolution.transport_equiv (localConjugation E K p) C (X j i)).symm
  simp only [maxWittAdjoint_formula, map_mul, hJ, hθ]

private theorem isQuasiSplitAt_of_nonsplit_gram_congruence
    (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)
    (P : Mˣ) (b : Lˣ)
    (hP : θ (P : M) * ((nonsplitHermitianChart p D hn hp hz).gram : M) * (P : M) =
      (b : L) • maxWittGram L n) :
    IsQuasiSplitAt D.toSecondKindInvolution n p := by
  let G := nonsplitHermitianChart p D hn hp hz
  let J : Mˣ := maxWittUnit n
  let U := Units.map (algebraMap L M).toMonoidHom b * J
  have hPU : θ (P : M) * (G.gram : M) * (P : M) = U := by
    rw [hP, Algebra.smul_def]
    rfl
  have hU : θ (U : M) = U := by
    rw [← hPU]
    simp only [AlgebraInvolution.apply_mul, AlgebraInvolution.apply_apply, G.hermitian, mul_assoc]
  let f := (matrixBasisChange (R := L) P).restrictScalars F
  let e := (G.equiv.trans f).trans (C).mapMatrix.symm
  refine ⟨e, ?_, fun x => ?_⟩
  · intro z
    have hG := G.center_eq (C z)
    change G.equiv (localCenterMap E K A p ((C).symm (C z))) = Matrix.scalar (Fin n) (C z) at hG
    rw [(C).symm_apply_apply] at hG
    apply (C).mapMatrix.injective
    change (C).mapMatrix ((C).mapMatrix.symm (f (G.equiv (localCenterMap E K A p z)))) =
      (C).mapMatrix (Matrix.scalar (Fin n) z)
    rw [AlgEquiv.apply_symm_apply, hG]
    change (matrixBasisChange (R := L) P) (algebraMap L M (C z)) =
      (C).mapMatrix (Matrix.scalar (Fin n) z)
    rw [AlgEquiv.commutes]
    apply Matrix.ext
    intro i j
    change Matrix.scalar (Fin n) (C z) i j = C (Matrix.scalar (Fin n) z i j)
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  · apply (C).mapMatrix.injective
    change (C).mapMatrix ((C).mapMatrix.symm (f (G.equiv (localInvolution D.toSecondKindInvolution p x)))) =
      (C).mapMatrix (maxWittAdjoint (localConjugation E K p) n (e x))
    rw [AlgEquiv.apply_symm_apply, G.adjoint_eq, mapMatrix_maxWittAdjoint]
    have hf (X : M) : f X = matrixBasisChange (R := F) P X := rfl
    rw [hf, matrixBasisChange_adjoint θ G.gram U P G.hermitian hU hPU,
      adjoint_apply_of_scalar_gram θ U J hU (maxWittGram_selfAdjoint c n) b rfl]
    change maxWittAdjoint c n (matrixBasisChange (R := F) P (G.equiv x)) =
      maxWittAdjoint c n ((C).mapMatrix (e x))
    rw [← hf]
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

include hp in
private theorem nonsplitCoefficientInvolution_ne : ∃ z, c z ≠ z := by
  obtain ⟨z, hz⟩ := exists_localConjugation_ne (K := K) p
  refine ⟨C z, fun h => hz ((C).injective ?_)⟩
  change (localConjugation E K p).transport C (C z) = C z at h
  rwa [AlgebraInvolution.transport_equiv] at h

include hp in
/-- In odd degree, vanishing Brauer invariants at a nonsplit finite place give
the actual maximal-Witt chart for every second-kind involution. -/
theorem isQuasiSplitAt_of_odd_nonsplit (D : CentralSimpleUnitaryData E K A n) (hn : Odd n)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0) :
    IsQuasiSplitAt D.toSecondKindInvolution n p := by
  let : ValuativeRel F := FiniteCompletion.valuativeRel p
  let : IsNonarchimedeanLocalField F := FiniteCompletion.isNonarchimedeanLocalField p
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hc := nonsplitCoefficientInvolution_ne p hp
  have hn' : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  let G := nonsplitHermitianChart p D hn' hp hz
  obtain ⟨P, b, hP⟩ := exists_odd_gram_congruence c hc hn G.gram G.hermitian
  exact isQuasiSplitAt_of_nonsplit_gram_congruence p hp D hn' hz P b hP

include hp in
/-- Center- and involution-preserving antidiagonal matrix coordinates at a
nonsplit finite place of odd degree and zero upper invariants. -/
def oddNonsplitMaxWittChart (D : CentralSimpleUnitaryData E K A n) (hn : Odd n)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0) :
    {e : LocalAlgebra E A p ≃ₐ[F] Matrix (Fin n) (Fin n) (LocalCenter E K p) //
      (∀ z, e (localCenterMap E K A p z) = Matrix.scalar (Fin n) z) ∧
      (∀ x, e (localInvolution D.toSecondKindInvolution p x) =
        maxWittAdjoint (localConjugation E K p) n (e x))} :=
  let h := isQuasiSplitAt_of_odd_nonsplit p hp D hn hz
  ⟨h.choose, h.choose_spec⟩

include hp in
/-- In positive even degree, a norm witness for the signed determinant of the
nonsplit Hermitian chart gives the actual maximal-Witt chart. -/
theorem isQuasiSplitAt_of_even_nonsplit_signedDeterminant
    (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n) (he : Even n)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)
    (hb : ∃ b : L, c b * b = (-1) ^ (n / 2) *
      ((nonsplitHermitianChart p D hn hp hz).gram : M).det) :
    IsQuasiSplitAt D.toSecondKindInvolution n p := by
  let : ValuativeRel F := FiniteCompletion.valuativeRel p
  let : IsNonarchimedeanLocalField F := FiniteCompletion.isNonarchimedeanLocalField p
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hc := nonsplitCoefficientInvolution_ne p hp
  let G := nonsplitHermitianChart p D hn hp hz
  obtain ⟨b, hb⟩ := hb
  obtain ⟨P, hP⟩ := exists_even_gram_congruence c hc he G.gram G.hermitian hb
  exact isQuasiSplitAt_of_nonsplit_gram_congruence p hp D hn hz P 1 (by simpa using hP)

include hp in
/-- Center- and involution-preserving maximal-Witt coordinates at an even-degree
nonsplit place with zero upper invariants and signed determinant a norm. -/
def evenNonsplitMaxWittChart (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n) (he : Even n)
    (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)
    (hb : ∃ b : L, c b * b = (-1) ^ (n / 2) *
      ((nonsplitHermitianChart p D hn hp hz).gram : M).det) :
    {e : LocalAlgebra E A p ≃ₐ[F] Matrix (Fin n) (Fin n) (LocalCenter E K p) //
      (∀ z, e (localCenterMap E K A p z) = Matrix.scalar (Fin n) z) ∧
      (∀ x, e (localInvolution D.toSecondKindInvolution p x) =
        maxWittAdjoint (localConjugation E K p) n (e x))} :=
  let h := isQuasiSplitAt_of_even_nonsplit_signedDeterminant p hp D hn he hz hb
  ⟨h.choose, h.choose_spec⟩

end CM

end Langlands.Shimura.FiniteUnitary
