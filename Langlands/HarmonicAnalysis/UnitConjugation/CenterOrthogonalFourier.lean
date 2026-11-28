import Langlands.HarmonicAnalysis.UnitConjugation.CenterDecomposition
import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar
import Langlands.HarmonicAnalysis.Bicharacter.SelfDual

/-!
# The Fourier transform on the orthogonal of the center

Let `A` be a finite-dimensional semisimple algebra over a nonarchimedean local field `F` of
characteristic zero, `z` its center and `V = z^⊥` the orthogonal of `z` for the trace form
`B₀` (`centerOrthogonal`). The restriction of `B₀` to `V` is symmetric, nondegenerate and
invariant under conjugation (`centerOrthogonalPairing`), so the Library's Fourier transform
`β̂(Y) = ∫_V ψ(B₀(Y, X)) β(X) dμ_V(X)` on `V` is defined. This module proves:

* conjugation by a unit preserves Haar measure on `V` (`measurePreserving_centerOrthogonalConj`),
  so the Fourier transform commutes with conjugation (`fourier_pullback_centerOrthogonalConj`);
* the scaling law `(β_s)^ = |s|^{dim V} (β̂)_{s⁻¹}` for `β_s(X) = β(s⁻¹ X)`
  (`fourier_scalarDilation`), `|s| = distribHaarChar F s`;
* with the product Haar measure on `A = z × V` (`productHaar`), the Fourier transform of
  `extendTest α β` restricted to `V` is `(∫ α) β̂` (`restrict_fourier_extendTest`): the
  pairing `B₀(Y, Z + X)` is `B₀(Y, X)` for `Y, X ∈ V` and central `Z`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed p. 2 (the Fourier transform for a
nondegenerate invariant form) and §3.5, printed p. 29 (`(f_t)^ = |t|^n (f̂)_{t⁻¹}`).
-/

noncomputable section

open MeasureTheory Module

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

section Pairing

variable {F : Type u} [Field F] [CharZero F] {A : Type v} [Ring A] [Algebra F A]
  [FiniteDimensional F A] [IsSemisimpleRing A]

variable (F A) in
/-- The restriction of the trace form to `V = z^⊥`. -/
def centerOrthogonalPairing : LinearMap.BilinForm F (centerOrthogonal F A) :=
  (traceFormPairing F A).restrict (centerOrthogonal F A)

omit [CharZero F] [FiniteDimensional F A] [IsSemisimpleRing A] in
theorem centerOrthogonalPairing_apply (Y X : centerOrthogonal F A) :
    centerOrthogonalPairing F A Y X = traceFormPairing F A Y X := rfl

omit [CharZero F] [FiniteDimensional F A] [IsSemisimpleRing A] in
theorem centerOrthogonalPairing_isSymm : (centerOrthogonalPairing F A).IsSymm :=
  ⟨fun Y X => traceFormPairing_comm (Y : A) X⟩

theorem orthogonal_centerOrthogonal :
    (traceFormPairing F A).orthogonal (centerOrthogonal F A) =
      (Subalgebra.center F A).toSubmodule :=
  LinearMap.BilinForm.orthogonal_orthogonal traceFormPairing_nondegenerate
    traceFormPairing_isSymm.isRefl _

theorem centerOrthogonalPairing_nondegenerate : (centerOrthogonalPairing F A).Nondegenerate := by
  refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _
    traceFormPairing_isSymm.isRefl ?_
  rw [orthogonal_centerOrthogonal]
  exact isCompl_center_centerOrthogonal.disjoint.symm

end Pairing

section Fourier

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A]

instance isFiniteDimensionalOverLocalField_centerOrthogonal :
    IsFiniteDimensionalOverLocalField F (centerOrthogonal F A) where
  finiteDimensional := inferInstance
  isModuleTopology := inferInstance

instance isFiniteDimensionalOverLocalField_centerSubmodule :
    IsFiniteDimensionalOverLocalField F (centerSubmodule F A) where
  finiteDimensional := inferInstance
  isModuleTopology := inferInstance

/-- Conjugation by a unit on `V`, as a linear equivalence. -/
def centerOrthogonalConjLinear (u : Aˣ) : centerOrthogonal F A ≃ₗ[F] centerOrthogonal F A where
  toFun := centerOrthogonalConj u
  invFun := (centerOrthogonalConj u).symm
  left_inv := (centerOrthogonalConj u).symm_apply_apply
  right_inv := (centerOrthogonalConj u).apply_symm_apply
  map_add' Y X := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c Y := Subtype.ext (by simp)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  [FiniteDimensional F A] [IsSemisimpleRing A] [IsModuleTopology F A] in
theorem centerOrthogonalPairing_conj (u : Aˣ) (Y X : centerOrthogonal F A) :
    centerOrthogonalPairing F A (centerOrthogonalConj u Y) (centerOrthogonalConj u X) =
      centerOrthogonalPairing F A Y X :=
  traceFormPairing_conj u (Y : A) X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] in
/-- A linear automorphism preserving a nondegenerate bilinear form has determinant `±1`. -/
theorem det_mul_self_of_preserves {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {B : LinearMap.BilinForm F W} (hB : B.Nondegenerate) (e : W ≃ₗ[F] W)
    (he : ∀ x y, B (e x) (e y) = B x y) : LinearEquiv.det e * LinearEquiv.det e = 1 := by
  let i := B.toDual hB
  have hi : e.toLinearMap.dualMap.comp (i.conj e.toLinearMap) = LinearMap.id := by
    apply LinearMap.ext
    intro L
    apply LinearMap.ext
    intro a
    change B (e (i.symm L)) (e a) = L a
    rw [he]
    exact congrArg (fun z : Module.Dual F W => z a) (i.apply_symm_apply L)
  have hd := congrArg LinearMap.det hi
  rw [LinearMap.det_comp, LinearMap.det_dualMap, LinearMap.det_id] at hd
  have hc : (i.conj e.toLinearMap).det = e.toLinearMap.det := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]
  rw [hc] at hd
  apply Units.ext
  simpa only [Units.val_mul, LinearEquiv.coe_det, Units.val_one] using hd

variable [MeasurableSpace (centerOrthogonal F A)] [BorelSpace (centerOrthogonal F A)]

/-- Conjugation by a unit preserves every Haar measure on `V`. -/
theorem measurePreserving_centerOrthogonalConj (μ : Measure (centerOrthogonal F A))
    [μ.IsAddHaarMeasure] (u : Aˣ) : MeasurePreserving (centerOrthogonalConj u) μ μ := by
  let e := centerOrthogonalConjLinear (F := F) u
  have hd : LinearEquiv.det e * LinearEquiv.det e = 1 :=
    det_mul_self_of_preserves centerOrthogonalPairing_nondegenerate e
      (centerOrthogonalPairing_conj u)
  have hχsq : distribHaarChar F (LinearEquiv.det e) * distribHaarChar F (LinearEquiv.det e) = 1 := by
    rw [← map_mul, hd, map_one]
  have hχ : distribHaarChar F (LinearEquiv.det e) = 1 := by
    apply NNReal.eq
    have h : (distribHaarChar F (LinearEquiv.det e) : ℝ) *
        (distribHaarChar F (LinearEquiv.det e) : ℝ) = 1 := by exact_mod_cast hχsq
    exact (mul_self_inj_of_nonneg (distribHaarChar F _).coe_nonneg zero_le_one).mp
      (by simpa using h)
  refine ⟨(centerOrthogonalConj u).continuous.measurable, ?_⟩
  change μ.map e = μ
  rw [map_linearEquiv_addHaar, hχ, inv_one, one_smul]

variable (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure (centerOrthogonal F A))

/-- The Fourier transform on `V` for the restricted trace form. -/
abbrev centerOrthogonalFourier :
    SchwartzBruhat (centerOrthogonal F A) →ₗ[ℂ] SchwartzBruhat (centerOrthogonal F A) :=
  pairingFourierSB ψ centerOrthogonalPairing_isSymm centerOrthogonalPairing_nondegenerate μ

/-- The Fourier transform on `V` commutes with conjugation. -/
theorem fourier_pullback_centerOrthogonalConj (u : Aˣ) (β : SchwartzBruhat (centerOrthogonal F A)) :
    centerOrthogonalFourier ψ μ (Hecke.TestFunction.pullback (centerOrthogonalConj u) β) =
      Hecke.TestFunction.pullback (centerOrthogonalConj u) (centerOrthogonalFourier ψ μ β) := by
  ext Y
  rw [Hecke.TestFunction.pullback_apply, pairingFourierSB_apply, pairingFourierSB_apply]
  have h := (measurePreserving_centerOrthogonalConj μ.measure u).integral_comp
    (centerOrthogonalConj u).measurableEmbedding
    (fun X => (ψ (centerOrthogonalPairing F A (centerOrthogonalConj u Y) X) : ℂ) * β X)
  rw [← h]
  congr 1
  funext X
  rw [Hecke.TestFunction.pullback_apply, centerOrthogonalPairing_conj]

/-- **Scaling of the Fourier transform**: `(β_s)^ = |s|^{dim V} (β̂)_{s⁻¹}`. -/
theorem fourier_scalarDilation (s : Fˣ) (β : SchwartzBruhat (centerOrthogonal F A)) :
    centerOrthogonalFourier ψ μ (scalarDilation s β) =
      ((distribHaarChar F s : ℝ) : ℂ) ^ finrank F (centerOrthogonal F A) •
        scalarDilation s⁻¹ (centerOrthogonalFourier ψ μ β) := by
  ext Y
  rw [pairingFourierSB_apply, SetLike.val_smul, Pi.smul_apply, scalarDilation_apply,
    pairingFourierSB_apply, inv_inv]
  set n := finrank F (centerOrthogonal F A)
  let S : centerOrthogonal F A ≃ₗ[F] centerOrthogonal F A :=
    LinearEquiv.smulOfNeZero F _ (s : F) (Units.ne_zero s)
  have hdet : LinearEquiv.det S = s ^ n := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det ((s : F) •
      (LinearMap.id : centerOrthogonal F A →ₗ[F] centerOrthogonal F A)) = ((s ^ n : Fˣ) : F)
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_pow_eq_pow_val]
  have hmap : μ.measure.map S = (distribHaarChar F s ^ n)⁻¹ • μ.measure := by
    rw [map_linearEquiv_addHaar, hdet, map_pow]
  have hne : (distribHaarChar F s ^ n) ≠ 0 := pow_ne_zero _ distribHaarChar_pos.ne'
  have hμ : μ.measure = (distribHaarChar F s ^ n) • μ.measure.map S := by
    rw [hmap, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hSm : MeasurableEmbedding (S : centerOrthogonal F A → centerOrthogonal F A) :=
    (Homeomorph.smul s).measurableEmbedding
  conv_lhs => rw [hμ]
  rw [integral_smul_nnreal_measure, hSm.integral_map]
  have hint : (fun X => (ψ (centerOrthogonalPairing F A Y (S X)) : ℂ) *
      scalarDilation s β (S X)) =
      fun X => (ψ (centerOrthogonalPairing F A (s • Y) X) : ℂ) * β X := by
    funext X
    have h1 : S X = (s : F) • X := rfl
    have h2 : (s • Y : centerOrthogonal F A) = (s : F) • Y := rfl
    rw [scalarDilation_apply, h1, h2, Units.smul_def, smul_smul, Units.inv_mul, one_smul,
      LinearMap.map_smul, LinearMap.map_smul₂]
  rw [hint, NNReal.smul_def, Complex.real_smul, NNReal.coe_pow, smul_eq_mul]
  push_cast
  ring

end Fourier

section Product

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A]
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (centerSubmodule F A)] [BorelSpace (centerSubmodule F A)]
  [MeasurableSpace (centerOrthogonal F A)] [BorelSpace (centerOrthogonal F A)]

variable [T2Space A]

/-- The Haar measure on `A` transported from the product `μ_z × μ_V` along `z × V ≃ A`. -/
def productHaar (μz : Measure (centerSubmodule F A)) [μz.IsAddHaarMeasure]
    (μV : AdditiveHaarMeasure (centerOrthogonal F A)) : AdditiveHaarMeasure A where
  measure := (μz.prod μV.measure).map (centerDecomposition F A)
  isAddHaar := ContinuousLinearEquiv.isAddHaarMeasure_map _ _
  regular := by
    have : IsFiniteDimensionalOverLocalField F A := ⟨inferInstance, inferInstance⟩
    have : (μz.prod μV.measure).map (centerDecomposition F A) |>.IsAddHaarMeasure :=
      ContinuousLinearEquiv.isAddHaarMeasure_map _ _
    infer_instance

/-- **Fourier transform of `extendTest α β` on `V`**: for the product Haar measure and the trace
form, the restriction to `V` of the Fourier transform of `X ↦ α(Z) β(Y)` is `(∫ α) β̂`. -/
theorem restrict_fourier_extendTest (ψ : UnitaryAdditiveCharacter F)
    (μz : Measure (centerSubmodule F A)) [μz.IsAddHaarMeasure]
    (μV : AdditiveHaarMeasure (centerOrthogonal F A))
    (α : SchwartzBruhat (centerSubmodule F A)) (β : SchwartzBruhat (centerOrthogonal F A)) :
    restrictCenterOrthogonal (pairingFourierSB ψ isInvariantPairing_traceFormPairing.isSymm
        isInvariantPairing_traceFormPairing.nondegenerate (productHaar μz μV) (extendTest α β)) =
      (∫ Z, α Z ∂μz) • centerOrthogonalFourier ψ μV β := by
  ext Y
  rw [restrictCenterOrthogonal_apply, pairingFourierSB_apply, SetLike.val_smul, Pi.smul_apply,
    pairingFourierSB_apply]
  have hme : MeasurableEmbedding (centerDecomposition F A) :=
    (centerDecomposition F A).toHomeomorph.measurableEmbedding
  change ∫ X, _ ∂((μz.prod μV.measure).map (centerDecomposition F A)) = _
  rw [hme.integral_map]
  have hint : (fun p : centerSubmodule F A × centerOrthogonal F A =>
      (ψ (traceFormPairing F A (Y : A) (centerDecomposition F A p)) : ℂ) *
        extendTest α β (centerDecomposition F A p)) =
      fun p => α p.1 * ((ψ (centerOrthogonalPairing F A Y p.2) : ℂ) * β p.2) := by
    funext p
    rw [extendTest_apply, ContinuousLinearEquiv.symm_apply_apply, centerDecomposition_apply,
      map_add, traceFormPairing_comm (Y : A) (p.1 : A),
      (mem_centerOrthogonal_iff (Y : A)).1 Y.2 _ p.1.2, zero_add, centerOrthogonalPairing_apply]
    ring
  rw [hint, smul_eq_mul]
  exact integral_prod_mul (μ := μz) (ν := μV.measure) (fun Z => α Z)
    (fun X => (ψ (centerOrthogonalPairing F A Y X) : ℂ) * β X)

end Product

end Langlands.HarmonicAnalysis.UnitConjugation
