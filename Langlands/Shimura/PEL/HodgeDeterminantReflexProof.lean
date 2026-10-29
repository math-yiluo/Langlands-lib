import Langlands.Shimura.PEL.HodgeDeterminantReflexStatement
import Langlands.Shimura.Unitary.GaloisCocharacterEvaluation

/-! # Reflex-field coefficients of the actual regular Hodge determinant: proof -/

noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace Langlands.Shimura.HodgeDeterminant

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Coefficient change of the determinant polynomial is matrix coefficient change. -/
theorem map_polynomial (g : F →+* F) (b b' : Module.Basis κ F M) (f : ι → Module.End F M)
    (h : ∀ i j k, LinearMap.toMatrix b' b' (f i) j k = g (LinearMap.toMatrix b b (f i) j k)) :
    MvPolynomial.map g (polynomial b f) = polynomial b' f := by
  rw [polynomial, polynomial, RingHom.map_det]
  congr 1
  ext j k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matrix, map_sum, map_mul, map_C, map_X, h]

/-- An injective semilinear endomorphism commuting with the family fixes the polynomial. -/
theorem map_polynomial_eq_of_semilinear [Infinite F] (g : F ≃+* F) (Ψ : M →+ M)
    (hΨ : ∀ m, Ψ m = 0 → m = 0) (hsmul : ∀ (c : F) (m : M), Ψ (c • m) = g c • Ψ m)
    (b : Module.Basis κ F M) (f : ι → Module.End F M)
    (hf : ∀ i m, f i (Ψ m) = Ψ (f i m)) :
    MvPolynomial.map (g : F →+* F) (polynomial b f) = polynomial b f := by
  have : FiniteDimensional F M := Module.Finite.of_basis b
  have hli : LinearIndependent F (Ψ ∘ b) :=
    b.linearIndependent.map_of_surjective_injective g Ψ g.surjective hΨ hsmul
  let b' : Module.Basis κ F M := basisOfLinearIndependentOfCardEqFinrank' (Ψ ∘ b) hli
    (Module.finrank_eq_card_basis b).symm
  have hb' : ∀ k, b' k = Ψ (b k) := fun k => by simp [b']
  rw [map_polynomial (g : F →+* F) b b' f, polynomial_basis_independent b' b]
  intro i j k
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hk : f i (b' k) = ∑ j, g (b.repr (f i (b k)) j) • b' j := by
    rw [hb', hf]
    conv_lhs => rw [← b.sum_repr (f i (b k))]
    simp only [map_sum, hsmul, hb']
  rw [hk, b'.repr_sum_self]
  rfl

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.Shimura.RegularHodge

variable {B : Type*} [Ring B] [Algebra ℝ B] {σ : AlgebraInvolution ℝ B}

/-- A Deligne point with split coordinates `(u⁻¹, 1)` has these real-coordinate relations. -/
theorem split_coordinates_of_eq {u : ℂˣ} {w : DeligneTorus.Points ℂ}
    (hw : DeligneTorus.splitPointsEquiv ℂ w = (u⁻¹, 1)) :
    (w : DeligneTorus.Complexification ℂ).re + (w : DeligneTorus.Complexification ℂ).im *
        Complex.I = ((u⁻¹ : ℂˣ) : ℂ) ∧
      (w : DeligneTorus.Complexification ℂ).re - (w : DeligneTorus.Complexification ℂ).im *
        Complex.I = 1 := by
  have h1 := DeligneTorus.splitPointsEquiv_fst ℂ w
  have h2 := DeligneTorus.splitPointsEquiv_snd ℂ w
  rw [hw] at h1 h2
  exact ⟨by simpa using h1.symm, by simpa using h2.symm⟩

/-- Right multiplication by a Deligne value is a combination of `1` and the action of `i`. -/
theorem mul_delignePoints (h : AlgebraInvolution.ComplexHom σ) (w : DeligneTorus.Points ℂ)
    (y : ℂ ⊗[ℝ] B) :
    y * ((h.delignePoints ℂ w).val.1 : ℂ ⊗[ℝ] B) =
      (w : DeligneTorus.Complexification ℂ).re • y +
        (w : DeligneTorus.Complexification ℂ).im • action h.hom Complex.I y := by
  have hs : ∀ (c : ℂ) (b : B), c ⊗ₜ[ℝ] b = c • ((1 : ℂ) ⊗ₜ[ℝ] b) := fun c b => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change y * h.deligneAlgebraMap ℂ (w : DeligneTorus.Complexification ℂ) = _
  rw [h.deligneAlgebraMap_apply, hs, hs _ (h.hom Complex.I), mul_add, mul_smul_comm,
    mul_smul_comm, ← Algebra.TensorProduct.one_def, mul_one, action_apply,
    complexifiedHom_apply]

/-- The Hodge summand is the inverse-weight space of the inverse Deligne values at the
first-factor points `(u, 1)`. -/
theorem mem_submodule_iff_delignePoints (h : AlgebraInvolution.ComplexHom σ)
    (x : ℂ ⊗[ℝ] B) :
    x ∈ submodule h.hom ↔ ∀ u : ℂˣ,
      x * ((((h.delignePoints ℂ ((DeligneTorus.splitPointsEquiv ℂ).symm (u, 1)))⁻¹).val.1 :
        ℂ ⊗[ℝ] B)) = ((u⁻¹ : ℂˣ) : ℂ) • x := by
  have hw : ∀ u : ℂˣ, DeligneTorus.splitPointsEquiv ℂ
      ((DeligneTorus.splitPointsEquiv ℂ).symm (u, 1))⁻¹ = (u⁻¹, 1) := fun u => by
    rw [map_inv, MulEquiv.apply_symm_apply, Prod.inv_mk, inv_one]
  simp only [← map_inv (h.delignePoints ℂ), mul_delignePoints]
  constructor
  · intro hx u
    obtain ⟨h1, -⟩ := split_coordinates_of_eq (hw u)
    rw [(mem_submodule_iff_I h.hom x).mp hx, smul_smul, ← add_smul, h1]
  · intro H
    rw [mem_submodule_iff_I]
    let u : ℂˣ := Units.mk0 2 two_ne_zero
    obtain ⟨h1, h2⟩ := split_coordinates_of_eq (hw u)
    have hu : ((u⁻¹ : ℂˣ) : ℂ) = 2⁻¹ := by simp [u]
    have him : ((((DeligneTorus.splitPointsEquiv ℂ).symm (u, 1))⁻¹ : DeligneTorus.Points ℂ) :
        DeligneTorus.Complexification ℂ).im ≠ 0 := by
      intro h0
      rw [h0, zero_mul, add_zero, hu] at h1
      rw [h0, zero_mul, sub_zero, h1] at h2
      norm_num at h2
    have hx := H u
    rw [← h1, add_smul, add_right_inj, mul_smul] at hx
    exact smul_right_injective _ him hx

end Langlands.Shimura.RegularHodge

namespace Langlands.Shimura.ComplexMatrix

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The semilinear transport `x ↦ s̃(x) γ⁻¹` on the iterated real tensor algebra, computed
through the rational tensor algebra `ℂ ⊗[ℚ] A`, where `s̃` is coefficient change by `s`. -/
def galoisTransport (s : ℂ ≃ₐ[ℚ] ℂ) (γ : (ℂ ⊗[ℚ] A)ˣ) :
    ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) →+ ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) :=
  AddMonoidHom.mk' (fun x => AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A
      (coefficientEquiv s ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) *
        ((γ⁻¹ : (ℂ ⊗[ℚ] A)ˣ) : ℂ ⊗[ℚ] A)))
    (fun x y => by simp only [map_add, add_mul])

theorem galoisTransport_apply (s : ℂ ≃ₐ[ℚ] ℂ) (γ : (ℂ ⊗[ℚ] A)ˣ)
    (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    galoisTransport s γ x = AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A
      (coefficientEquiv s ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) *
        ((γ⁻¹ : (ℂ ⊗[ℚ] A)ˣ) : ℂ ⊗[ℚ] A)) := rfl

/-- The transport is semilinear over `s`. -/
theorem galoisTransport_smul (s : ℂ ≃ₐ[ℚ] ℂ) (γ : (ℂ ⊗[ℚ] A)ˣ) (c : ℂ)
    (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    galoisTransport s γ (c • x) = s c • galoisTransport s γ x := by
  rw [galoisTransport_apply, galoisTransport_apply, map_smul, coefficientEquiv_smul,
    smul_mul_assoc, map_smul]

/-- The transport is injective. -/
theorem galoisTransport_eq_zero (s : ℂ ≃ₐ[ℚ] ℂ) (γ : (ℂ ⊗[ℚ] A)ˣ)
    (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) (hx : galoisTransport s γ x = 0) : x = 0 := by
  rw [galoisTransport_apply, map_eq_zero_iff _ (AlgEquiv.injective _),
    Units.mul_left_eq_zero, map_eq_zero_iff _ (AlgEquiv.injective _),
    map_eq_zero_iff _ (AlgEquiv.injective _)] at hx
  exact hx

/-- The transport commutes with left multiplication by every rational algebra element. -/
theorem galoisTransport_mul_left (s : ℂ ≃ₐ[ℚ] ℂ) (γ : (ℂ ⊗[ℚ] A)ˣ) (a : A)
    (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    galoisTransport s γ (((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a)) * x) =
      ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] a)) * galoisTransport s γ x := by
  simp only [galoisTransport_apply, map_mul, AlgebraInvolution.baseChangeTowerEquiv_symm_tmul,
    one_smul, coefficientEquiv_tmul, map_one, AlgebraInvolution.baseChangeTowerEquiv_tmul,
    mul_assoc]

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The rational-tensor unit of the actual first-factor Kottwitz cocharacter at `u`. -/
def kottwitzCocharacterUnit (u : ℂˣ) : (ℂ ⊗[ℚ] A)ˣ :=
  (D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
    (D.complexCocharacterValue (D.kottwitzCocharacter C true) u)).val.1

/-- In the iterated real tensor algebra, the cocharacter unit is Kottwitz's inverse
Deligne value of the fixed conjugated homomorphism at the first-factor point. -/
theorem baseChangeTower_kottwitzCocharacterUnit (u : ℂˣ) :
    AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A
        (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) =
      ((((D.realPositiveKottwitzHom C).val.delignePoints ℂ
        ((DeligneTorus.splitPointsEquiv ℂ).symm (u, 1)))⁻¹).val.1 :
          ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) := by
  apply (C.iteratedScalarMatrixEquiv D.totallyRealBasis ℂ).injective
  funext τ
  rw [show (D.realPositiveKottwitzHom C).val = (C.realComplexHom D.totallyRealBasis).conj
    from rfl, C.conj_inverse_delignePoints_firstFactor]
  change C.scalarMatrixEquiv D.totallyRealBasis ℂ (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) τ
    = _
  rw [kottwitzCocharacterUnit, ← D.complexAffineCocharacterValue_rational,
    ← D.complexAffinePointMatrices_rational, D.kottwitzCocharacter_affine_matrices]
  rfl

/-- A Galois automorphism stabilizing the actual class transports the cocharacter units
up to one fixed conjugating unit. -/
theorem kottwitzCocharacterUnit_galois {s : ℂ ≃ₐ[ℚ] ℂ}
    (hs : D.ComplexCocharacterConjugate
      (D.galoisCocharacter s (D.kottwitzCocharacter C true)) (D.kottwitzCocharacter C true)) :
    ∃ γ : (ℂ ⊗[ℚ] A)ˣ, ∀ u : ℂˣ,
      (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) =
        (γ : ℂ ⊗[ℚ] A) * ComplexMatrix.coefficientEquiv s
          (D.kottwitzCocharacterUnit C (Units.map s.symm.toMonoidHom u) : ℂ ⊗[ℚ] A) *
          ((γ⁻¹ : (ℂ ⊗[ℚ] A)ˣ) : ℂ ⊗[ℚ] A) := by
  obtain ⟨g, hg⟩ := hs
  refine ⟨(D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)
    (D.complexRationalPointsEquiv g)).val.1, fun u => ?_⟩
  have h := D.complexCocharacterValue_inner
    (D.galoisCocharacter s (D.kottwitzCocharacter C true)) g u
  rw [hg] at h
  rw [kottwitzCocharacterUnit, h, map_mul, map_mul, map_inv,
    D.complexCocharacterValue_galois_coordinates]
  rfl

/-- Kottwitz's Hodge module, read in the rational tensor algebra, is the inverse-weight space
of right multiplication by the actual cocharacter units. -/
theorem mem_kottwitzHodgeModule_iff (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    x ∈ D.kottwitzHodgeModule C ↔ ∀ u : ℂˣ,
      (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x *
          (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) =
        ((u⁻¹ : ℂˣ) : ℂ) • (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x := by
  rw [kottwitzHodgeModule, RegularHodge.mem_submodule_iff_delignePoints]
  refine forall_congr' fun u => ?_
  rw [← D.baseChangeTower_kottwitzCocharacterUnit C u]
  constructor
  · intro h
    apply (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).injective
    rw [map_mul, map_smul, AlgEquiv.apply_symm_apply, h]
  · intro h
    have h' := congrArg (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A) h
    rwa [map_mul, map_smul, AlgEquiv.apply_symm_apply] at h'

/-- The transport by a stabilizing automorphism, with its conjugating unit, preserves the
whole Hodge module. -/
theorem galoisTransport_mem {s : ℂ ≃ₐ[ℚ] ℂ} {γ : (ℂ ⊗[ℚ] A)ˣ}
    (hγ : ∀ u : ℂˣ,
      (D.kottwitzCocharacterUnit C u : ℂ ⊗[ℚ] A) =
        (γ : ℂ ⊗[ℚ] A) * ComplexMatrix.coefficientEquiv s
          (D.kottwitzCocharacterUnit C (Units.map s.symm.toMonoidHom u) : ℂ ⊗[ℚ] A) *
          ((γ⁻¹ : (ℂ ⊗[ℚ] A)ˣ) : ℂ ⊗[ℚ] A))
    {x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)} (hx : x ∈ D.kottwitzHodgeModule C) :
    ComplexMatrix.galoisTransport s γ x ∈ D.kottwitzHodgeModule C := by
  rw [mem_kottwitzHodgeModule_iff] at hx ⊢
  intro u
  rw [ComplexMatrix.galoisTransport_apply, AlgEquiv.symm_apply_apply, hγ u]
  have key : ComplexMatrix.coefficientEquiv s
        ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) *
      ComplexMatrix.coefficientEquiv s
        (D.kottwitzCocharacterUnit C (Units.map s.symm.toMonoidHom u) : ℂ ⊗[ℚ] A) =
      ((u⁻¹ : ℂˣ) : ℂ) • ComplexMatrix.coefficientEquiv s
        ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) := by
    rw [← map_mul, hx, ComplexMatrix.coefficientEquiv_smul]
    congr 2
    simp
  calc _ = (ComplexMatrix.coefficientEquiv s
        ((AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A).symm x) *
      ComplexMatrix.coefficientEquiv s
        (D.kottwitzCocharacterUnit C (Units.map s.symm.toMonoidHom u) : ℂ ⊗[ℚ] A)) *
          ((γ⁻¹ : (ℂ ⊗[ℚ] A)ˣ) : ℂ ⊗[ℚ] A) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [key, smul_mul_assoc]

/-- Every automorphism in the actual cocharacter stabilizer fixes the regular Hodge
determinant polynomial. -/
theorem kottwitzHodgeDeterminant_map_galois {J : Type*} [Fintype J] (a : J → A)
    {s : ℂ ≃ₐ[ℚ] ℂ}
    (hs : D.ComplexCocharacterConjugate
      (D.galoisCocharacter s (D.kottwitzCocharacter C true)) (D.kottwitzCocharacter C true)) :
    MvPolynomial.map ((s : ℂ ≃+* ℂ) : ℂ →+* ℂ) (D.kottwitzHodgeDeterminant C a) =
      D.kottwitzHodgeDeterminant C a := by
  obtain ⟨γ, hγ⟩ := D.kottwitzCocharacterUnit_galois C hs
  let Ψ : D.kottwitzHodgeModule C →+ D.kottwitzHodgeModule C :=
    AddMonoidHom.mk' (fun m => ⟨ComplexMatrix.galoisTransport s γ m,
      D.galoisTransport_mem C hγ m.2⟩) (fun m m' => Subtype.ext (map_add _ _ _))
  exact HodgeDeterminant.map_polynomial_eq_of_semilinear (s : ℂ ≃+* ℂ) Ψ
    (fun m hm => Subtype.ext (ComplexMatrix.galoisTransport_eq_zero s γ m
      (congrArg Subtype.val hm)))
    (fun c m => Subtype.ext (ComplexMatrix.galoisTransport_smul s γ c m)) _ _
    (fun i m => Subtype.ext (ComplexMatrix.galoisTransport_mul_left s γ (a i) m).symm)

/-- **Kottwitz, §5.** Every coefficient of the actual regular Hodge determinant lies in the
fixed field of the actual Kottwitz cocharacter class. -/
theorem kottwitzHodgeDeterminantReflexDescent : D.KottwitzHodgeDeterminantReflexDescent C := by
  intro _ J _ a d
  rw [kottwitzCocharacterReflexField, mem_complexCocharacterFixedField]
  intro s hs
  have h := congrArg (fun p => p.coeff d) (D.kottwitzHodgeDeterminant_map_galois C a hs)
  simp only [MvPolynomial.coeff_map] at h
  exact h

end Langlands.Shimura.CentralSimpleUnitaryData
