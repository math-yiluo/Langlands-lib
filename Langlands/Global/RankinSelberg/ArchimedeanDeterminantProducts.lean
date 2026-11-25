import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction
import Langlands.Global.RankinSelberg.LocalPointFactorization
import Langlands.Global.Factors.HeckeMixedComponents

/-! # Local normalization and determinant products on the partial domain -/

noncomputable section
universe u
open NumberField MeasureTheory
open Langlands.Global.CompletionPadic
open scoped Classical WithZero NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.DeterminantProducts

variable (F : Type u) [Field F] [NumberField F]

/-- The residue-normalized p-adic absolute value is the native completion norm. -/
theorem normalizedAbs_eq_completion_norm (v : FinitePlace F) (x : FiniteCompletion F v) :
    (padicField v).canonicalTopologicalData.normalizedAbs x = ‖x‖ := by
  have he : (padicField v).canonicalTopologicalData.normalizedAbs x =
      (topologicalData v).normalizedAbs x := by
    rw [PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
      PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree]
  rw [he]
  by_cases hx : x = 0
  · simp [hx, PadicField.TopologicalData.normalizedAbs_zero]
  · rw [PadicField.TopologicalData.normalizedAbs_of_ne_zero _ hx,
      HeckeEulerProduct.residueCardinality_eq,
      PadicField.TopologicalData.ord,
      AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation,
      neg_neg, NumberField.FinitePlace.norm_def,
      WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hx),
      NNReal.coe_zpow]
    rfl

/-- Determinants of matrices with integral entries are integral. -/
theorem det_mem_integers (v : FinitePlace F) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (FiniteCompletion F v))
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) :
    Matrix.det A ∈ v.adicCompletionIntegers F := by
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) :=
    fun i j => ⟨A i j, hA i j⟩
  have he : ((Matrix.det B : v.adicCompletionIntegers F) : FiniteCompletion F v) = Matrix.det A :=
    (v.adicCompletionIntegers F).toSubring.subtype.map_det B
  exact he ▸ (Matrix.det B).property

/-- The determinant norm of an integral invertible matrix is one. -/
theorem norm_det_localIntegral (v : FinitePlace F) (n : ℕ)
    (g : FiniteLocalGL F n v) (hg : g ∈ FiniteAdelicGL.localIntegral F n v) :
    ‖(Matrix.GeneralLinearGroup.det g).val‖ = 1 := by
  obtain ⟨hentries, hinv⟩ := (FiniteAdelicGL.mem_localIntegral F n v g).mp hg
  have hval : (Matrix.GeneralLinearGroup.det g).val ∈ v.adicCompletionIntegers F :=
    det_mem_integers F v n g.val hentries
  have hival : ((Matrix.GeneralLinearGroup.det g)⁻¹).val ∈ v.adicCompletionIntegers F := by
    rw [← map_inv]
    exact det_mem_integers F v n (g⁻¹).val hinv
  have hv : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰)
      (Matrix.GeneralLinearGroup.det g).val = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v) (a := Matrix.GeneralLinearGroup.det g)).mp ⟨hval, hival⟩
  exact (Valued.toNormedField.norm_eq_one_iff
    (Γ₀ := ℤᵐ⁰) (x := (Matrix.GeneralLinearGroup.det g).val)).mpr hv

/-- The same norm is one on the local unipotent-integral double domain. -/
theorem norm_det_isUnipotentIntegral (v : FinitePlace F) (n : ℕ)
    (g : FiniteLocalGL F n v) (hg : IsUnipotentIntegral F n v g) :
    ‖(Matrix.GeneralLinearGroup.det g).val‖ = 1 := by
  obtain ⟨k, hk, hdiag, hlow⟩ := hg
  have hu : PrimitiveAdelicHeight.IsUnitriangular (g * k).val := ⟨hlow, hdiag⟩
  have he : (Matrix.GeneralLinearGroup.det g).val *
      (Matrix.GeneralLinearGroup.det k).val = 1 := by
    rw [← Units.val_mul, ← map_mul, Matrix.GeneralLinearGroup.val_det_apply]
    exact hu.det_eq_one
  have hn := congrArg (fun z : FiniteCompletion F v => ‖z‖) he
  rw [norm_mul, norm_det_localIntegral F v n k hk, mul_one, norm_one] at hn
  exact hn

/-- The adelic determinant norm has exactly the local factors on the partial domain. -/
theorem detNorm_product (n : ℕ) (S : Finset (FinitePlace F)) (g : Points F n)
    (hg : g ∈ unipotentIntegralOutside F n S) :
    detNorm F n g =
      (∏ v, ArchimedeanLocal.realNormalizedAbs
        (Matrix.det (realComponent F n v g).val)) *
      (∏ w, ArchimedeanLocal.complexNormalizedAbs
        (Matrix.det (complexComponent F n w g).val)) *
      ∏ v : S, RankinSelberg.normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData
        (Matrix.det (finiteComponent F n v.1 g).val) := by
  let G := GeneralLinearGroupPoints.adelicEquiv F n g
  let a := AdelicGL.determinant F n G
  have hreal (v : {v : InfinitePlace F // v.IsReal}) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val.1).1 v =
        Matrix.det (realComponent F n v g).val := by
    let f : Adeles F →+* ℝ :=
      (((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
        (RingHom.fst _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comp
        (RingHom.fst _ _)
    change f (Matrix.det G.val) = Matrix.det (G.val.map f)
    exact f.map_det G.val
  have hcomplex (w : {v : InfinitePlace F // v.IsComplex}) :
      (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val.1).2 w =
        Matrix.det (complexComponent F n w g).val := by
    let f : Adeles F →+* ℂ :=
      (((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) w).comp
        (RingHom.snd _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comp
        (RingHom.fst _ _)
    change f (Matrix.det G.val) = Matrix.det (G.val.map f)
    exact f.map_det G.val
  have hfinite (v : FinitePlace F) :
      a.val.2 v = (Matrix.GeneralLinearGroup.det (finiteComponent F n v g)).val := by
    change finiteProjection F v (Matrix.det G.val) =
      Matrix.det (G.val.map (finiteProjection F v))
    exact (finiteProjection F v).map_det G.val
  have hfinprod :
      (∏ᶠ v : FinitePlace F, ‖a.val.2 v‖) =
        ∏ v : S, ‖(Matrix.GeneralLinearGroup.det (finiteComponent F n v.1 g)).val‖ := by
    simp_rw [hfinite]
    rw [finprod_eq_prod_of_mulSupport_subset
      (fun v : FinitePlace F => ‖(Matrix.GeneralLinearGroup.det (finiteComponent F n v g)).val‖)
      (s := S) (fun v hv => by
        by_contra hvS
        exact hv (norm_det_isUnipotentIntegral F v n _ (hg v hvS)))]
    exact (Finset.prod_coe_sort S
      (fun v => ‖(Matrix.GeneralLinearGroup.det (finiteComponent F n v g)).val‖)).symm
  change ((IdeleAbsoluteValue.full F a : ℝ≥0) : ℝ) = _
  rw [IdeleAbsoluteValue.coe_full,
    ← HeckeFunctionalEquation.norm_mixedCoordinates a.val.1,
    Hecke.norm_eq_prod_real_complex, hfinprod]
  simp only [hreal, hcomplex, ArchimedeanLocal.realNormalizedAbs,
    ArchimedeanLocal.complexNormalizedAbs, Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  exact Finset.prod_congr rfl fun v _ =>
    (normalizedAbs_eq_completion_norm F v.1
      (Matrix.det (finiteComponent F n v.1 g).val)).symm

/-- The real-logarithm complex power respects products of positive reals. -/
theorem exp_log_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    Complex.exp (s * (Real.log (a * b) : ℂ)) =
      Complex.exp (s * (Real.log a : ℂ)) * Complex.exp (s * (Real.log b : ℂ)) := by
  rw [Real.log_mul ha.ne' hb.ne', Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The same identity for a finite product, including the empty product. -/
theorem exp_log_prod {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (s : ℂ) :
    Complex.exp (s * (Real.log (∏ i, a i) : ℂ)) =
      ∏ i, Complex.exp (s * (Real.log (a i) : ℂ)) := by
  rw [Real.log_prod (fun i _ => (ha i).ne')]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

/-- Every determinant power splits over the real, complex and `S` components. -/
theorem detPower_product (n : ℕ) (S : Finset (FinitePlace F)) (g : Points F n)
    (hg : g ∈ unipotentIntegralOutside F n S) (s : ℂ) :
    detPower F n g s =
      (∏ v, ArchimedeanLocal.detPower ArchimedeanLocal.realNormalizedAbs
        (realComponent F n v g) s) *
      (∏ w, ArchimedeanLocal.detPower ArchimedeanLocal.complexNormalizedAbs
        (complexComponent F n w g) s) *
      ∏ v : S, ArchimedeanLocal.detPower
        (RankinSelberg.normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
        (finiteComponent F n v.1 g) s := by
  let aR := fun v => ArchimedeanLocal.realNormalizedAbs (Matrix.det (realComponent F n v g).val)
  let aC := fun w => ArchimedeanLocal.complexNormalizedAbs (Matrix.det (complexComponent F n w g).val)
  let aS := fun v : S => RankinSelberg.normalizedAbsoluteValue
    (padicField v.1).canonicalTopologicalData (Matrix.det (finiteComponent F n v.1 g).val)
  have hR (v) : 0 < aR v := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)
  have hC (w) : 0 < aC w := pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2
  have hS (v : S) : 0 < aS v :=
    (padicField v.1).canonicalTopologicalData.normalizedAbs_pos
      (Matrix.GeneralLinearGroup.det_ne_zero _)
  have hRp : 0 < ∏ v, aR v := Finset.prod_pos fun v _ => hR v
  have hCp : 0 < ∏ w, aC w := Finset.prod_pos fun w _ => hC w
  have hSp : 0 < ∏ v, aS v := Finset.prod_pos fun v _ => hS v
  unfold detPower
  rw [detNorm_product F n S g hg]
  change Complex.exp (s * (Real.log ((∏ v, aR v) * (∏ w, aC w) * ∏ v, aS v) : ℂ)) = _
  rw [exp_log_mul _ _ (mul_pos hRp hCp) hSp, exp_log_mul _ _ hRp hCp,
    exp_log_prod aR hR, exp_log_prod aC hC, exp_log_prod aS hS]
  rfl

/-- The determinant-power component of archimedean pointwise factorization. -/
def DeterminantPowerProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S : Finset (FinitePlace F))
    (g : Points F n), g ∈ unipotentIntegralOutside F n S → ∀ s : ℂ,
    detPower F n g s =
      (∏ v, ArchimedeanLocal.detPower ArchimedeanLocal.realNormalizedAbs
        (realComponent F n v g) s) *
      (∏ w, ArchimedeanLocal.detPower ArchimedeanLocal.complexNormalizedAbs
        (complexComponent F n w g) s) *
      ∏ v : S, ArchimedeanLocal.detPower
        (RankinSelberg.normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
        (finiteComponent F n v.1 g) s

theorem determinantPowerProduct : DeterminantPowerProductStatement.{u} := by
  intro F _ _ n S g hg s
  exact detPower_product F n S g hg s

end Langlands.Global.RankinSelbergGlobal.DeterminantProducts
