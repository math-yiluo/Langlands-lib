import Langlands.Theta.WeilIndex.NormForm
import Langlands.Theta.DualPair.LerayCharacter

/-!
# Gauss integrals of Hermitian quadratic characters

GKT Proposition 11.3 (p. 309) and Corollary 11.4 (p. 315) in Case `3₊`, in the language of Gauss
integrals (the phase of the integral is the Weil index, Corollary 3.12, p. 80). Internal lemmas for
the Leray splitting of `U(ν, ν)`. For an invertible Hermitian `b ∈ M_ν(E)`, the character of
second degree `x ↦ ψ(½ β(x, x b))` on `M_{α×ν}(E)`, `β = hermitianPairing c Q`, has regularized
integral `γ₀ · splittingScalar(det b)⁻¹` with `γ₀` independent of `b` (`hasGauss_herm`).
Diagonalizing `Q` and `b` by congruence (`IsQuadraticInvolution.exists_eq_mul_diagonal_mul`) turns
the character into a product of characters `ψ(t N(z))` of the entries (`pr_diag_norm`), whose Gauss
integrals are those of the norm form (`hasGauss_diag_norm`); the change of variables scales Haar
measure by `|N det|` (`map_mul_mul_addHaar`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis
open LocalClassField (valuationBall isCompact_valuationBall isOpen_valuationBall normSign
  normSign_mul exists_addSubgroup_norm_mem_valuationBall)

namespace Unitary.Internal


theorem hasGauss_diag_norm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : α → ν → Fˣ,
    HasGaussIntegral μ (fun x => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (x i j))) (g * ∏ i, ∏ j,
    (normSign E (t i j) * ((distribHaarChar F (t i j))⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ ψ hψ hn h1 _ _ μ _
  have hfd : FiniteDimensional F E := hE.finite
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : FiniteDimensional F E := hfd
  have := IsModuleTopology.isTopologicalAddGroup F E
  have := locallyCompactSpace_of_finiteDimensional F E
  have := secondCountableTopology_of_finiteDimensional F E
  have := t2Space_of_finiteDimensional F E
  let μE : Measure E := Measure.addHaar
  obtain ⟨g₁, hg₁⟩ := hasGauss_norm_mul F E c δ hE ψ hψ hn h1 μE
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  let T : Matrix α ν E ≃ₜ+ (α × ν → E) :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun y i j => y (i, j)
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j) }
  have : BorelSpace (α × ν → E) := Pi.borelSpace
  have : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hr : μ.map T = (μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) •
      Measure.pi fun _ : α × ν => μE := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(((μ.map T).addHaarScalarFactor (Measure.pi fun _ : α × ν => μE) : ℝ) : ℂ) *
    g₁ ^ Fintype.card (α × ν), fun t => ?_⟩
  have hpi := HasGaussIntegral.pi (μ := μE) (f := fun (p : α × ν) z => ψ
      ((t p.1 p.2 : F) * Algebra.norm F z))
    (γ := fun p => g₁ * (normSign E (t p.1 p.2) * ((distribHaarChar F (t p.1 p.2))⁻¹ : ℝ)))
        (fun p => hg₁ _)
  have hm := HasGaussIntegral.comp_addEquiv T hr hpi
  have hsum : ∀ (s : Finset (α × ν)) (f : α × ν → F), ψ (∑ p ∈ s, f p) = ∏ p ∈ s, ψ (f p) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul,
        ih]
  convert hm using 1
  · funext x
    rw [← Fintype.sum_prod_type', hsum]
    rfl
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_prod_type,
      mul_assoc]




theorem pr_eq_half_trace_mat (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
      (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, hermitianSymplecticForm, hermitianTensor, Fintype.sum_sum_type, fromCols_apply_inl,
      fromCols_apply_inr, hyperbolicForm_eq_fromBlocks,
    fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, mul_apply, transpose_apply,
        map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pr_diag_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α]
    (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E)
    (D' : α → F) (a : Matrix ν ν E) (D : ν → F),
    Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E,
    2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j,
    (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.involutive
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by
      ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E
          (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
        Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul,
        transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map,
          transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
        transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace
      (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by
          simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by
    simp only [Matrix.trace, diag_apply, mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite,
        zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, transpose_apply, map_apply,
      map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.exists_basis
  have : Module.Free F E := Module.Free.of_basis b
  have : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring



namespace GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuadraticInvolution c δ)

def normSignHom : Fˣ →* ℂ where
  toFun := normSign E
  map_one' := by simp only [normSign]; exact ite_eq_left (one_mem _)
  map_mul' s t := normSign_mul hE s t

omit [CharZero
  F] [ValuativeRel
  F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
      [IsModuleTopology F E] in
theorem normSign_inv (t : Fˣ) : normSign E t⁻¹ = normSign E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold normSign
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [ite_eq_left ht, ite_eq_left (h.mpr ht)]
  · rw [ite_eq_right ht, ite_eq_right (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

omit [CharZero
  F] [ValuativeRel
  F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [TopologicalSpace E]
      [IsModuleTopology F E] in
theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) *
        ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det
      (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring

include hE in

theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E)
    (D : ν → Fˣ) :
    splittingScalar F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) *
        ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F)
          (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (normSign E (D j) * ((distribHaarChar F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := sc_basic F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) *
      ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : distribHaarChar F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [distribHaarChar, map_inv]
  have e2 : normSign E (∏ j, D j)⁻¹ = ∏ j, normSign E (D j) := by
    rw [normSign_inv]; exact map_prod (normSignHom c hE) D Finset.univ
  have e3 : distribHaarChar F (∏ j, D j)⁻¹ = ∏ j, (distribHaarChar F (D j))⁻¹ := by
    simp [distribHaarChar, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv,
        transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E,
    (b.map c)ᵀ = b → b.det ≠ 0 → HasGaussIntegral μ (fun x => ψ (2⁻¹ * pr c Q x (x * b)))
    (γ₀ * splittingScalar F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  have : IsTopologicalRing E := hE.isTopologicalRing
  have : FiniteDimensional F E := hE.finite
  obtain ⟨u, D',
      hQd⟩ := hE.exists_eq_mul_diagonal_mul Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := hasGauss_diag_norm F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F)
      (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i,
        (normSign E (s i) * ((distribHaarChar F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := hE.exists_eq_mul_diagonal_mul b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j,
          (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [pr_diag_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := HasGaussIntegral.comp_addEquiv (sandwich U a)
    (map_mul_mul_addHaar (F := F) μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, normSign E (t i j) * (((distribHaarChar F (t i j))⁻¹ : ℝ) : ℂ) =
      (normSign E (s i) * (((distribHaarChar F (s i))⁻¹ : ℝ) : ℂ)) * (normSign E (D j) * (((distribHaarChar F
          (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [normSign_mul hE, map_mul (distribHaarChar F), NNReal.coe_mul, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GaussMain

open GaussMain


end Unitary.Internal

end Langlands.Theta
