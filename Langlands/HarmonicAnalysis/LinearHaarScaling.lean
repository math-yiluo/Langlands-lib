import Langlands.HarmonicAnalysis.GeneralHaarScalingProof
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Haar measure under linear automorphisms over a nonarchimedean local field

Let `F` be a nonarchimedean local field and `V` a finite-dimensional `F`-vector space with its
module topology. For an `F`-linear automorphism `T` of `V` and an additive Haar measure `μ` on `V`,

`μ.map T = (distribHaarChar F (det T))⁻¹ • μ`  (`map_linearEquiv_addHaar`),

where `distribHaarChar F : Fˣ →* ℝ≥0` is Mathlib's modulus of `F` (`|a|_F`, the factor by which
multiplication by `a` scales Haar measure). Corollaries: multiplication by a unit `z` of a finite
`F`-algebra `E` scales Haar measure on `E` by `|N_{E/F} z|_F` (`map_mul_left_addHaar_algebra`), and
`x ↦ u x a` on `M_{α×ν}(E)`, for an extension field `E`, by
`|N det u|_F^{|ν|} |N det a|_F^{|α|}` (`map_mul_mul_addHaar`). The proof reduces to coordinates and
to the Library's determinant change of variables on `Fⁿ`
(`haarMeasure_map_in_coordinates`). A measure on `F` without atom at `0`, finite on compacts and
scaling like Haar measure under multiplication by units, is a multiple of Haar measure
(`eq_smul_addHaar_of_map_mul_left`).

The comparison with the Library's normalized absolute values: `distribHaarChar F a` is the
residue-normalized absolute value of `a` (`distribHaarChar_eq_absUnits`), and the rectangular
statement `GeneralRectangularHaarScalingStatement` follows from `map_linearEquiv_addHaar`
(`generalRectangularHaarScalingStatement_of_map_linearEquiv`).
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix ValuativeRel
open scoped NNReal ENNReal Pointwise Topology

namespace Langlands.HarmonicAnalysis

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-! ### The modulus of `F` -/

/-- The scaling of Haar measure under multiplication by a unit of `F`. -/
theorem map_mul_left_addHaar [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] (a : Fˣ) :
    μ.map (fun x => (a : F) * x) = (distribHaarChar F a)⁻¹ • μ := by
  have := GeneralLocalField.secondCountableTopology F
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  have hset : (fun y => (a : F) * y) ⁻¹' s = a⁻¹ • s := by
    ext y
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]
  rw [hset, ← distribHaarChar_mul, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := a)).ne']

/-- The modulus of a unit of valuation one is one. -/
theorem distribHaarChar_eq_one_of_valuation_eq_one {a : Fˣ} (ha : valuation F (a : F) = 1) :
    distribHaarChar F a = 1 := by
  borelize F
  have := GeneralLocalField.secondCountableTopology F
  let μ : Measure F := addHaar
  have h0 : μ (𝒪[F] : Set F) ≠ 0 :=
    ((GeneralLocalField.isOpen_integer F).measure_pos μ ⟨0, zero_mem _⟩).ne'
  have ht : μ (𝒪[F] : Set F) ≠ ∞ := (GeneralLocalField.isCompact_integer F).measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 ht (r := 1) ?_
  have hs : (a • (𝒪[F] : Set F) : Set F) = 𝒪[F] := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe,
      SetLike.mem_coe, Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one, one_mul]
  rw [hs, ENNReal.coe_one, one_mul]

open Classical in
/-- `|x|_F` as a homomorphism `F →*₀ ℝ≥0`: the modulus on units, `0` at `0`. -/
private def modulusWithZero (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : F →*₀ ℝ≥0 where
  toFun x := if h : x = 0 then 0 else distribHaarChar F (Units.mk0 x h)
  map_zero' := dite_eq_left rfl
  map_one' := by
    rw [dite_eq_right one_ne_zero]
    simp only [Units.mk0_one, map_one]
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [dite_eq_right (mul_ne_zero hx hy), dite_eq_right hx, dite_eq_right hy, ← map_mul]
    congr 1
    ext
    simp

private theorem modulusWithZero_units (a : Fˣ) :
    modulusWithZero F (a : F) = distribHaarChar F a := by
  simp only [modulusWithZero, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dite_eq_right a.ne_zero,
    Units.mk0_val]

/-! ### Linear automorphisms -/

/-- **Haar measure under a linear automorphism.** For an `F`-linear automorphism `T` of a
finite-dimensional `F`-vector space with its module topology, `μ.map T = |det T|_F⁻¹ • μ`. -/
theorem map_linearEquiv_addHaar {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V) :
    μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  borelize F
  have := GeneralLocalField.secondCountableTopology F
  have : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup F V
  let b := Module.finBasis F V
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let E : V ≃ₜ+ (Fin (Module.finrank F V) → F) :=
    { e.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hdet : M.det = ((LinearEquiv.det T : Fˣ) : F) := by
    simp [M, LinearMap.det_toMatrix]
  have hM : M.det ≠ 0 := by rw [hdet]; exact Units.ne_zero _
  have hχ (a : F) (ha : a ≠ 0) :
      (addHaar : Measure F).map (fun x => a * x) = (modulusWithZero F a)⁻¹ • addHaar := by
    have h := map_mul_left_addHaar (addHaar : Measure F) (Units.mk0 a ha)
    rwa [← modulusWithZero_units, Units.val_mk0] at h
  have h := haarMeasure_map_in_coordinates (addHaar : Measure F) (modulusWithZero F) hχ E μ hM
  have hT : (fun x => E.symm (Matrix.toLin' M (E x))) = (T : V → V) := by
    funext x
    apply e.injective
    change e (e.symm (Matrix.toLin' M (e x))) = e (T x)
    rw [e.apply_symm_apply, Matrix.toLin'_apply]
    simp only [e, Module.Basis.equivFun_apply, M]
    exact LinearMap.toMatrix_mulVec_repr b b T.toLinearMap x
  rw [hT, hdet, modulusWithZero_units] at h
  exact h

/-- Multiplication by a unit `z` of a finite `F`-algebra `E` scales Haar measure on `E` by
`|N_{E/F}(z)|_F`. -/
theorem map_mul_left_addHaar_algebra {E : Type*} [Ring E] [Algebra F E] [FiniteDimensional F E]
    [TopologicalSpace E] [IsModuleTopology F E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F (Units.map (Algebra.norm F : E →* F) z))⁻¹ • μ := by
  let T : E ≃ₗ[F] E :=
    { LinearMap.mulLeft F (z : E) with
      invFun := fun x => ((z⁻¹ : Eˣ) : E) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have hT : LinearEquiv.det T = Units.map (Algebra.norm F : E →* F) z := by
    ext
    rw [LinearEquiv.coe_det, Units.coe_map, Algebra.norm_apply]
    rfl
  rw [← hT]
  exact map_linearEquiv_addHaar μ T

/-- The `E`-linear map `x ↦ u x a` of `α × ν` matrices. -/
private def mulMulLinear {E : Type*} [Field E] {α ν : Type*} [Fintype α] [Fintype ν]
    (u : Matrix α α E) (a : Matrix ν ν E) : Matrix α ν E →ₗ[E] Matrix α ν E where
  toFun x := u * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

private theorem det_mulMulLinear {E : Type*} [Field E] {α ν : Type*} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (mulMulLinear u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by
  let e : (α × ν → E) ≃ₗ[E] Matrix α ν E := LinearEquiv.curry E E α ν
  have h : mulMulLinear u a =
      (e : _ →ₗ[E] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) u a.transpose)) ∘ₗ
        (e.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (u * z * a) i j =
      (Matrix.kroneckerMap (· * ·) u a.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Function.uncurry z (b, c) = z b c from rfl]
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The determinant over `F` of `x ↦ u x a` on `α × ν` matrices over a finite extension `E`. -/
theorem det_restrictScalars_mul_mul {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
    {α ν : Type*} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
    (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E)
    (hT : ∀ x, T x = u * x * a) :
    LinearMap.det T =
      Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  have hT' : T = (mulMulLinear u a).restrictScalars F := by
    refine LinearMap.ext fun x => ?_
    rw [hT]
    rfl
  rw [hT', LinearMap.det_restrictScalars, det_mulMulLinear, map_mul, map_pow, map_pow]

/-- The `F`-linear automorphism `x ↦ u x a` of `α × ν` matrices over `E`. -/
def mulMulEquiv (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]
    {α ν : Type*} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    change ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) *
      ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    change (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x *
      ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem mulMulEquiv_apply (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]
    {α ν : Type*} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) (x : Matrix α ν E) :
    mulMulEquiv F u a x = (u : Matrix α α E) * x * (a : Matrix ν ν E) :=
  rfl

/-- The module topology on matrices over a finite `F`-algebra with its module topology. -/
@[instance]
theorem isModuleTopology_matrix (F : Type*) [Field F] [TopologicalSpace F] {E : Type*}
    [Ring E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (α ν : Type*)
    [Finite α] [Finite ν] : IsModuleTopology F (Matrix α ν E) :=
  inferInstanceAs (IsModuleTopology F (α → ν → E))

/-- **Two-sided multiplication on matrices over an extension.** For a finite extension `E` of
`F`, `x ↦ u x a` scales Haar measure on `M_{α×ν}(E)` by
`|N_{E/F} det u|_F^{|ν|} |N_{E/F} det a|_F^{|α|}`. -/
theorem map_mul_mul_addHaar {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
    [TopologicalSpace E] [IsModuleTopology F E] {α ν : Type*} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
    (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E) :
    μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) =
      (distribHaarChar F (Units.map (Algebra.norm F : E →* F) u.det) ^ Fintype.card ν *
        distribHaarChar F (Units.map (Algebra.norm F : E →* F) a.det) ^ Fintype.card α)⁻¹ • μ := by
  have := isModuleTopology_matrix F (E := E) α ν
  let T := mulMulEquiv F u a
  have hdet : LinearEquiv.det T =
      Units.map (Algebra.norm F : E →* F) u.det ^ Fintype.card ν *
        Units.map (Algebra.norm F : E →* F) a.det ^ Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, det_restrictScalars_mul_mul (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x => rfl)]
    simp
  have hT : (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, map_linearEquiv_addHaar μ T, hdet, map_mul, map_pow, map_pow]

/-! ### Measures that scale like Haar measure -/

namespace LinearHaarScaling.Internal

theorem nhdsNE_neBot : (𝓝[≠] (0 : F)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro t ht
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 ht
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  refine ⟨y * r, hs ?_, mul_ne_zero (by simpa using hγ) hr⟩
  show valuation F (y * r) < valuation F y
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1

theorem isOpen_sphere {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {y : F | valuation F y = γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation F).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

/-- `|x|_F` in `ℝ≥0∞`. -/
def absE (x : F) : ℝ≥0∞ := (modulusWithZero F x : ℝ≥0∞)

theorem absE_units (a : Fˣ) : absE (a : F) = distribHaarChar F a := by
  rw [absE, modulusWithZero_units]

theorem absE_ne_zero {x : F} (hx : x ≠ 0) : absE x ≠ 0 := by
  have := absE_units (Units.mk0 x hx)
  rw [Units.val_mk0] at this
  rw [this, ne_eq, ENNReal.coe_eq_zero]
  exact (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne'

theorem absE_ne_top (x : F) : absE x ≠ ∞ := ENNReal.coe_ne_top

theorem absE_inv {x : F} (hx : x ≠ 0) : absE x⁻¹ = (absE x)⁻¹ := by
  rw [absE, absE, map_inv₀, ENNReal.coe_inv]
  have := absE_ne_zero hx
  rwa [absE, ne_eq, ENNReal.coe_eq_zero] at this

theorem absE_eq_one {x : F} (hx : valuation F x = 1) : absE x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h := absE_units (Units.mk0 x hx0)
  rw [Units.val_mk0, distribHaarChar_eq_one_of_valuation_eq_one (by simpa using hx)] at h
  simpa using h

theorem absE_eq_of_val_eq {x y : F} (h : valuation F y = valuation F x) : absE y = absE x := by
  by_cases hx : x = 0
  · subst hx
    have : y = 0 := by simpa using h
    rw [this]
  have hy : y ≠ 0 := by rintro rfl; exact hx (by simpa using h.symm)
  have hu : valuation F (y / x) = 1 := by
    rw [map_div₀, h, div_self (by simpa using hx)]
  have e1 := absE_eq_one hu
  have hyx : y = x * (y / x) := by rw [mul_div_cancel₀ _ hx]
  simp only [absE] at e1 ⊢
  rw [hyx, map_mul, ENNReal.coe_mul, e1, mul_one]

variable [MeasurableSpace F] [BorelSpace F]

theorem measurableSet_preimage_valuation (S : Set (ValueGroupWithZero F)) :
    MeasurableSet (valuation F ⁻¹' S) := by
  have e : valuation F ⁻¹' S = valuation F ⁻¹' (S \ {0}) ∪ valuation F ⁻¹' (S ∩ {0}) := by
    rw [← Set.preimage_union, Set.sdiff_union_inter]
  rw [e]
  refine MeasurableSet.union (IsOpen.measurableSet ?_) ?_
  · have : valuation F ⁻¹' (S \ {0}) = ⋃ γ ∈ S \ {0}, {y : F | valuation F y = γ} := by
      ext y; simp
    rw [this]
    exact isOpen_biUnion fun γ hγ ↦ isOpen_sphere hγ.2
  · by_cases h0 : (0 : ValueGroupWithZero F) ∈ S
    · have : valuation F ⁻¹' (S ∩ {0}) = {0} := by
        ext y; simp [h0]
      rw [this]; exact measurableSet_singleton 0
    · have : valuation F ⁻¹' (S ∩ {0}) = ∅ := by
        ext y; simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hy h'; exact h0 (h' ▸ hy)
      rw [this]; exact MeasurableSet.empty

theorem measurable_absE : Measurable (absE : F → ℝ≥0∞) := by
  intro T _
  have : absE ⁻¹' T = valuation F ⁻¹' (valuation F '' (absE ⁻¹' T)) := by
    ext x; constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      simp only [Set.mem_preimage] at hy ⊢
      rwa [← absE_eq_of_val_eq hxy]
  rw [this]; exact measurableSet_preimage_valuation _

theorem lintegral_comp_mul_left (μ : Measure F)
    (hμ : ∀ x : F, x ≠ 0 → μ.map (fun y ↦ x * y) = (absE x)⁻¹ • μ) {f : F → ℝ≥0∞}
    (hf : Measurable f) {x : F} (hx : x ≠ 0) :
    ∫⁻ t, f (x * t) ∂μ = (absE x)⁻¹ * ∫⁻ t, f t ∂μ := by
  calc ∫⁻ t, f (x * t) ∂μ = ∫⁻ t, f t ∂(μ.map (fun y ↦ x * y)) :=
        (lintegral_map hf (measurable_const_mul x)).symm
    _ = _ := by rw [hμ x hx, lintegral_smul_measure]; rfl

theorem map_mul_haar (lam : Measure F) [lam.IsAddHaarMeasure] {x : F} (hx : x ≠ 0) :
    lam.map (fun y ↦ x * y) = (absE x)⁻¹ • lam := by
  have h := map_mul_left_addHaar lam (Units.mk0 x hx)
  rw [Units.val_mk0] at h
  have h' := absE_units (Units.mk0 x hx)
  rw [Units.val_mk0] at h'
  rw [h, h', ← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']
  ext s
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

/-- The units of the valuation ring. -/
def U : Set F := {y | valuation F y = 1}

theorem measurableSet_U : MeasurableSet (U : Set F) :=
  (isOpen_sphere one_ne_zero).measurableSet

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem inv_mem_U_iff (t : F) : t⁻¹ ∈ (U : Set F) ↔ t ∈ U := by
  simp [U, map_inv₀]

theorem measure_mul_measure_units_eq (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F)
    [SFinite n] (hn0 : n {0} = 0)
    (hn : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n)
    {A : Set F} (hA : MeasurableSet A) :
    n A * lam U = n U * lam A := by
  have := GeneralLocalField.secondCountableTopology F
  have := nhdsNE_neBot (F := F)
  have hU := measurableSet_U (F := F)
  have hl := fun x (hx : x ≠ 0) ↦ map_mul_haar lam (x := x) hx
  have hlam0 : lam {0} = 0 := measure_singleton 0
  let K : F → F → ℝ≥0∞ := fun x y ↦ A.indicator 1 x * (absE x)⁻¹ * U.indicator 1 (x⁻¹ * y)
  let G : F → F → ℝ≥0∞ := fun y t ↦ U.indicator 1 t * A.indicator 1 (y * t)
  have hIA : Measurable (A.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hA
  have hIU : Measurable (U.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hU
  have hK : Measurable (Function.uncurry K) := by
    refine ((hIA.comp measurable_fst).mul (measurable_absE.comp measurable_fst).inv).mul
      (hIU.comp (measurable_fst.inv.mul measurable_snd))
  have hG : Measurable (Function.uncurry G) :=
    (hIU.comp measurable_snd).mul (hIA.comp (measurable_fst.mul measurable_snd))
  have h1 : ∫⁻ x, ∫⁻ y, K x y ∂lam ∂n = n A * lam U := by
    have h0 : ∀ᵐ x ∂n, x ≠ 0 := by
      rw [ae_iff]; simpa using hn0
    have : ∀ᵐ x ∂n, ∫⁻ y, K x y ∂lam = A.indicator 1 x * lam U := by
      filter_upwards [h0] with x hx
      simp only [K]
      rw [lintegral_const_mul, lintegral_comp_mul_left lam hl hIU (inv_ne_zero hx), absE_inv hx,
        inv_inv, lintegral_indicator_one hU, mul_assoc, ← mul_assoc (absE x)⁻¹,
        ENNReal.inv_mul_cancel (absE_ne_zero hx) (absE_ne_top x), one_mul]
      exact hIU.comp (measurable_const_mul _)
    rw [lintegral_congr_ae this, lintegral_mul_const _ hIA, lintegral_indicator_one hA]
  have h2 : ∫⁻ y, ∫⁻ x, K x y ∂n ∂lam = ∫⁻ y, ∫⁻ t, G y t ∂n ∂lam := by
    have h0 : ∀ᵐ y ∂lam, y ≠ 0 := by
      rw [ae_iff]; simp [hlam0]
    apply lintegral_congr_ae
    filter_upwards [h0] with y hy
    have hf : Measurable fun x ↦ K x y := hK.comp (measurable_id.prodMk measurable_const)
    have hsub := lintegral_comp_mul_left n hn hf hy
    have hpt : ∀ t, K (y * t) y = (absE y)⁻¹ * G y t := by
      intro t
      simp only [K, G]
      have e : (y * t)⁻¹ * y = t⁻¹ := by rw [_root_.mul_inv_rev, inv_mul_cancel_right₀ hy]
      rw [e]
      by_cases ht : t ∈ (U : Set F)
      · have hv : valuation F (y * t) = valuation F y := by
          rw [map_mul, show valuation F t = 1 from ht, mul_one]
        rw [absE_eq_of_val_eq hv, Set.indicator_of_mem ((inv_mem_U_iff t).mpr ht),
          Set.indicator_of_mem ht]
        simp only [Pi.one_apply]; ring
      · rw [Set.indicator_of_notMem (fun h ↦ ht ((inv_mem_U_iff t).mp h)),
          Set.indicator_of_notMem ht]
        simp
    simp only [hpt] at hsub
    rw [lintegral_const_mul _ (show Measurable fun t ↦ G y t from
      hG.comp (measurable_const.prodMk measurable_id))] at hsub
    have hne := absE_ne_zero hy
    have hnt := absE_ne_top y
    have := congrArg (fun z ↦ absE y * z) hsub
    simp only [← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul] at this
    exact this.symm
  have h3 : ∫⁻ t, ∫⁻ y, G y t ∂lam ∂n = n U * lam A := by
    have : ∀ t, ∫⁻ y, G y t ∂lam = U.indicator 1 t * lam A := by
      intro t
      simp only [G]
      rw [lintegral_const_mul]
      swap; · exact hIA.comp (measurable_mul_const t)
      by_cases ht : t ∈ (U : Set F)
      · have ht0 : t ≠ 0 := by rintro rfl; simp [U] at ht
        simp_rw [mul_comm _ t]
        rw [lintegral_comp_mul_left lam hl hIA ht0, absE_eq_one ht, inv_one, one_mul,
          lintegral_indicator_one hA]
      · simp [Set.indicator_of_notMem ht]
    simp_rw [this]
    rw [lintegral_mul_const _ hIU, lintegral_indicator_one hU]
  rw [← h1, lintegral_lintegral_swap hK.aemeasurable, h2,
    lintegral_lintegral_swap hG.aemeasurable, h3]

end LinearHaarScaling.Internal

open LinearHaarScaling.Internal in
/-- **A measure on `F` that scales like Haar measure is a multiple of Haar measure**: if `n` has
no atom at `0`, is finite on compacts, and `n.map (u * ·) = |u|_F⁻¹ • n` for every unit `u`,
then `n = r • lam` for every Haar measure `lam`. -/
theorem eq_smul_addHaar_of_map_mul_left [MeasurableSpace F] [BorelSpace F]
    (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n]
    (hn0 : n {0} = 0)
    (hn : ∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) :
    ∃ r : ℝ≥0, n = r • lam := by
  have := GeneralLocalField.secondCountableTopology F
  have hn' : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n := by
    intro x hx
    have h := hn (Units.mk0 x hx)
    simp only [Units.val_mk0] at h
    rw [h]
    have h' := absE_units (Units.mk0 x hx)
    rw [Units.val_mk0] at h'
    rw [h', ← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']
    ext s
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]
  have hUO : (U : Set F) ⊆ (𝒪[F] : Set F) := fun y hy ↦
    (Valuation.mem_integer_iff _ _).mpr (le_of_eq hy)
  have hnU : n U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GeneralLocalField.isCompact_integer F).measure_lt_top).ne
  have hlU : lam U ≠ ∞ :=
    ((measure_mono hUO).trans_lt (GeneralLocalField.isCompact_integer F).measure_lt_top).ne
  have hlU0 : lam U ≠ 0 :=
    ((isOpen_sphere (F := F) one_ne_zero).measure_pos lam ⟨1, by simp⟩).ne'
  refine ⟨(n U / lam U).toNNReal, ?_⟩
  ext s hs
  rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hnU hlU0),
    smul_eq_mul]
  have hk := measure_mul_measure_units_eq lam n hn0 hn' hs
  rw [div_eq_mul_inv, mul_right_comm, ← hk, mul_assoc, ENNReal.mul_inv_cancel hlU0 hlU, mul_one]

/-! ### Comparison with the Library's normalized absolute values -/

/-- The modulus `distribHaarChar F a` is the residue-normalized absolute value of `a`: for an
absolute value `abv` with `abv ϖ = q⁻¹` on a uniformizer and `abv = 1` on units of the valuation
ring, `distribHaarChar F a = |a|`. -/
theorem distribHaarChar_eq_absUnits (q : ℕ)
    (hq : q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer))
    (abv : AbsoluteValue F ℝ) (ϖ : Fˣ) (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
        (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹) (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (a : Fˣ) : distribHaarChar F a = (Shahidi.absUnits abv a : ℝ≥0) := by
  borelize F
  have := GeneralLocalField.secondCountableTopology F
  let μ : Measure F := addHaar
  have h1 := map_mul_left_addHaar μ a
  have h2 := generalScalarHaarScalingStatement F q hq abv ϖ hϖ habv hunit μ a
  rw [h1] at h2
  have h0 : μ (𝒪[F] : Set F) ≠ 0 :=
    ((GeneralLocalField.isOpen_integer F).measure_pos μ ⟨0, zero_mem _⟩).ne'
  have ht : μ (𝒪[F] : Set F) ≠ ∞ := (GeneralLocalField.isCompact_integer F).measure_lt_top.ne
  have h3 := congrArg (fun ν : Measure F => ν (𝒪[F] : Set F)) h2
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj h0 ht).1 h3
  rw [ENNReal.coe_inj] at h4
  exact inv_injective h4

/-- The Library's rectangular Haar scaling statement is a case of `map_linearEquiv_addHaar`
(through `map_mul_mul_addHaar` for `E = F`), given its scalar statement. -/
theorem generalRectangularHaarScalingStatement_of_map_linearEquiv :
    GeneralRectangularHaarScalingStatement F := by
  intro q hq abv ϖ hϖ habv hunit r s _ _ μ _ A B
  have h := map_mul_mul_addHaar (F := F) (E := F) μ A B⁻¹
  have hd (g : Fˣ) : distribHaarChar F (Units.map (Algebra.norm F : F →* F) g) =
      (Shahidi.absUnits abv g : ℝ≥0) := by
    rw [distribHaarChar_eq_absUnits q hq abv ϖ hϖ habv hunit]
    congr 3
    ext
    simp [Algebra.norm_self]
  rw [h, hd, hd]
  congr 1
  simp only [Fintype.card_fin, Shahidi.determinantAbs, MonoidHom.coe_comp, Function.comp_apply,
    map_inv, Units.val_inv_eq_inv_val, inv_pow, div_eq_mul_inv]

end Langlands.HarmonicAnalysis
