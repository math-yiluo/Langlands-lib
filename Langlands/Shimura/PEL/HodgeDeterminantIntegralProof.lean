import Langlands.Shimura.PEL.HodgeDeterminantIntegralStatement
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.TensorProduct.Free

/-! # Integral coefficients of the actual Harris order Hodge determinant: proof -/

noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace Langlands.Shimura.HodgeDeterminant

section Expansion

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The exponent counting how often each index occurs in an assignment of columns. -/
def assignmentDegree (s : κ → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (s j) 1

/-- Multilinear expansion of a determinant whose entries are linear forms. -/
theorem det_linearForms (B : ι → Matrix κ κ R) :
    (Matrix.of fun r j => ∑ i, C (B i r j) * X i : Matrix κ κ (MvPolynomial ι R)).det =
      ∑ s : κ → ι, monomial (assignmentDegree s) (Matrix.of fun r j => B (s j) r j).det := by
  classical
  simp only [Matrix.det_apply, Matrix.of_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.prod_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, assignmentDegree, monomial_sum_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact C_mul_X_eq_monomial

/-- The coefficients of a determinant of linear forms are sums of column-mixed determinants. -/
theorem coeff_det_linearForms [DecidableEq ι] (B : ι → Matrix κ κ R) (d : ι →₀ ℕ) :
    (Matrix.of fun r j => ∑ i, C (B i r j) * X i :
        Matrix κ κ (MvPolynomial ι R)).det.coeff d =
      ∑ s : κ → ι, if assignmentDegree s = d then (Matrix.of fun r j => B (s j) r j).det
        else 0 := by
  rw [det_linearForms, coeff_sum]
  simp only [coeff_monomial]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Multiplying a coefficient by a volume gives a sum of mixed volumes. -/
theorem coeff_polynomial_mul_det [DecidableEq ι] (b : Module.Basis κ R M)
    (f : ι → Module.End R M) (d : ι →₀ ℕ) (w : κ → M) :
    (polynomial b f).coeff d * b.det w =
      ∑ s : κ → ι, if assignmentDegree s = d then b.det (fun j => f (s j) (w j))
        else 0 := by
  have hcol : ∀ i j r, (LinearMap.toMatrix b b (f i) * b.toMatrix w) r j =
      b.repr (f i (w j)) r := by
    intro i j r
    rw [← LinearMap.toMatrix_mulVec_repr b b]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  have hmat : matrix b f * (b.toMatrix w).map C =
      Matrix.of fun r j => ∑ i, C ((LinearMap.toMatrix b b (f i) * b.toMatrix w) r j) * X i := by
    refine Matrix.ext fun r j => ?_
    simp only [Matrix.mul_apply, matrix, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul,
      map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdet : C (b.det w) * polynomial b f =
      (Matrix.of fun r j => ∑ i, C ((LinearMap.toMatrix b b (f i) * b.toMatrix w) r j) * X i :
        Matrix κ κ (MvPolynomial ι R)).det := by
    rw [← hmat, Matrix.det_mul, polynomial, b.det_apply, RingHom.map_det, mul_comm]
    rfl
  rw [mul_comm ((polynomial b f).coeff d), ← coeff_C_mul, hdet, coeff_det_linearForms]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [b.det_apply]
    congr 1
    refine Matrix.ext fun r j => ?_
    rw [Matrix.of_apply, hcol, Module.Basis.toMatrix_apply]
  · rfl

end Expansion

section Integral

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A multilinear value on a span of a finite family lies in the span of its values on
assignments from that family. -/
theorem multilinear_mem_span {S : Type*} [CommSemiring S] {V P : Type*} [AddCommMonoid V]
    [Module S V] [AddCommMonoid P] [Module S P] {γ : Type*} [Fintype γ]
    (φ : MultilinearMap S (fun _ : κ => V) P) (G : γ → V) (w : κ → V)
    (hw : ∀ j, w j ∈ Submodule.span S (Set.range G)) :
    φ w ∈ Submodule.span S (Set.range fun r : κ → γ => φ fun j => G (r j)) := by
  classical
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun S).mp (hw j)
  have hw' : w = fun j => ∑ k, c j k • G k := funext fun j => (hc j).symm
  rw [hw', MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- If the endomorphisms preserve the integer span of a finite family spanning the space,
then every coefficient of their determinant polynomial is integral over `ℤ`. -/
theorem isIntegral_coeff_polynomial (b : Module.Basis κ F V) (f : ι → Module.End F V)
    {γ : Type*} [Fintype γ] (G : γ → V) (hspan : Submodule.span F (Set.range G) = ⊤)
    (hf : ∀ i k, f i (G k) ∈ Submodule.span ℤ (Set.range G)) (d : ι →₀ ℕ) :
    IsIntegral ℤ ((polynomial b f).coeff d) := by
  classical
  set N : Submodule ℤ F :=
    Submodule.span ℤ (Set.range fun r : κ → γ => b.det fun j => G (r j)) with hNdef
  have hmem : ∀ w : κ → V, (∀ j, w j ∈ Submodule.span ℤ (Set.range G)) → b.det w ∈ N :=
    fun w hw => multilinear_mem_span (b.det.toMultilinearMap.restrictScalars ℤ) G w hw
  have hfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hne : N ≠ ⊥ := by
    intro hN
    have h0 : ∀ r : κ → γ, b.det (fun j => G (r j)) = 0 := fun r => by
      have hr : b.det (fun j => G (r j)) ∈ N := Submodule.subset_span ⟨r, rfl⟩
      rw [hN] at hr
      exact (Submodule.mem_bot ℤ).mp hr
    have hb := multilinear_mem_span b.det.toMultilinearMap G b
      (fun j => by rw [hspan]; trivial)
    have hrange : Set.range (fun r : κ → γ => b.det.toMultilinearMap fun j => G (r j)) ⊆
        (⊥ : Submodule F F) := by
      rintro _ ⟨r, rfl⟩
      exact (Submodule.mem_bot F).mpr (h0 r)
    have hzero := Submodule.span_le.mpr hrange hb
    rw [Submodule.mem_bot] at hzero
    have hone : b.det b = 1 := b.det_self
    exact one_ne_zero (hone.symm.trans hzero)
  refine isIntegral_of_smul_mem_submodule N hne hfg _ fun n hn => ?_
  induction hn using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    rw [smul_eq_mul, coeff_polynomial_mul_det]
    refine Submodule.sum_mem _ fun s _ => ?_
    split_ifs
    · exact hmem _ fun j => hf _ _
    · exact N.zero_mem
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul n x _ hx => rw [smul_comm]; exact N.smul_mem n hx

end Integral

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.Shimura.RegularHodge

variable {B : Type*} [Ring B] [Algebra ℝ B] (h : ℂ →ₐ[ℝ] B)

/-- The projection onto the identity Hodge summand along the conjugate summand. -/
def hodgeProjection : ℂ ⊗[ℝ] B →ₗ[ℂ] submodule h :=
  Submodule.projectionOnto _ _ (isCompl h)

/-- The Hodge projection commutes with left multiplication. -/
theorem hodgeProjection_mul (b x : ℂ ⊗[ℝ] B) :
    hodgeProjection h (b * x) = leftAction h b (hodgeProjection h x) := by
  have hc := isCompl h
  set p := (submodule h).projection (conjugateSubmodule h) hc x with hp
  set q := (conjugateSubmodule h).projection (submodule h) hc.symm x with hq
  have hx : p + q = x := Submodule.projection_add_projection_eq_self hc x
  have hpm : p ∈ submodule h := Submodule.projection_apply_mem _ _
  have hqm : q ∈ conjugateSubmodule h := Submodule.projection_apply_mem _ _
  have hbp : b * p ∈ submodule h := mul_mem h b hpm
  have hbq : b * q ∈ conjugateSubmodule h := mul_mem _ b hqm
  apply Subtype.ext
  rw [leftAction_apply]
  simp only [hodgeProjection, Submodule.coe_projectionOnto_apply]
  rw [← hp]
  conv_lhs => rw [← hx]
  rw [mul_add, map_add, Submodule.projection_apply_of_mem_left _ hbp,
    Submodule.projection_apply_of_mem_right _ hbq, add_zero]

/-- Integral coefficients from a finitely generated spanning integer module in the
complexified algebra. -/
theorem isIntegral_coeff_determinantPolynomial [FiniteDimensional ℝ B]
    {ι : Type*} [Fintype ι] {γ : Type*} [Fintype γ] (G : γ → ℂ ⊗[ℝ] B)
    (hspan : Submodule.span ℂ (Set.range G) = ⊤) (a : ι → ℂ ⊗[ℝ] B)
    (ha : ∀ i k, a i * G k ∈ Submodule.span ℤ (Set.range G)) (d : ι →₀ ℕ) :
    IsIntegral ℤ ((determinantPolynomial h a).coeff d) := by
  refine HodgeDeterminant.isIntegral_coeff_polynomial _ _ (fun k => hodgeProjection h (G k))
    ?_ ?_ d
  · have hmap : Submodule.span ℂ (Set.range fun k => hodgeProjection h (G k)) =
        (Submodule.span ℂ (Set.range G)).map (hodgeProjection h) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap, hspan, Submodule.map_top]
    exact Submodule.range_projectionOnto _
  · intro i k
    change leftAction h (a i) (hodgeProjection h (G k)) ∈ _
    rw [← hodgeProjection_mul]
    have hmap : Submodule.span ℤ (Set.range fun k => hodgeProjection h (G k)) =
        (Submodule.span ℤ (Set.range G)).map ((hodgeProjection h).restrictScalars ℤ) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap]
    exact Submodule.mem_map_of_mem (ha i k)

end Langlands.Shimura.RegularHodge

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- **Kottwitz, §5, integer-order form.** Every coefficient of the actual regular Hodge
determinant of a finite family in the constructed Harris order is an algebraic integer. -/
theorem kottwitzIntegralHodgeDeterminantCoefficients :
    D.KottwitzIntegralHodgeDeterminantCoefficients C := by
  intro _ ι _ a d
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ E A
  obtain ⟨N, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := D.harrisHodgePELIntegralOrder C)
  let φ : A →+* ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) :=
    (TensorProduct.includeRight : (ℝ ⊗[ℚ] A) →ₐ[ℝ] ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)).toRingHom.comp
      (TensorProduct.includeRight : A →ₐ[ℚ] ℝ ⊗[ℚ] A).toRingHom
  have hφ : ∀ x, φ x = (1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] x) := fun x => rfl
  let G : Fin N → ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) := fun k => φ (g k)
  have hO : ∀ x ∈ D.harrisHodgePELIntegralOrder C, φ x ∈ Submodule.span ℤ (Set.range G) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : D.harrisHodgePELIntegralOrder C) ∈ Submodule.span ℤ (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx'
    have hxc : x = ∑ k, c k • (g k : A) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    rw [hxc, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hspan : Submodule.span ℂ (Set.range G) = ⊤ := by
    let e := Module.finBasis ℚ A
    let eW := TensorProduct.basis ℂ (TensorProduct.basis ℝ e)
    rw [_root_.eq_top_iff, ← eW.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨m, hm, hmx⟩ := D.exists_int_multiple_mem_harrisHodgePELIntegralOrder C (e j)
    have h1 : φ (m • e j) ∈ Submodule.span ℂ (Set.range G) :=
      Submodule.span_le_restrictScalars ℤ ℂ _ (hO _ hmx)
    have hm' : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have heW : eW j = (m : ℂ)⁻¹ • φ (m • e j) := by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      simp [eW, TensorProduct.basis_apply, hφ]
    change eW j ∈ Submodule.span ℂ (Set.range G)
    rw [heW]
    exact Submodule.smul_mem _ _ h1
  exact RegularHodge.isIntegral_coeff_determinantPolynomial
    (D.realPositiveKottwitzHom C).val.hom G hspan (fun i => φ (a i))
    (fun i k => by
      rw [← map_mul]
      exact hO _ (Subalgebra.mul_mem _ (a i).prop (g k).prop)) d

end Langlands.Shimura.CentralSimpleUnitaryData
