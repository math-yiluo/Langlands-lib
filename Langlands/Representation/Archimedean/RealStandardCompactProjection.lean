import Langlands.Representation.Archimedean.RealStandardCompactFourier
import Langlands.Representation.Archimedean.RealStandardCompactTraceKernel

/-! # Compact projection into the real standard module -/

noncomputable section

open MeasureTheory Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

open GramFormula OrthogonalFinitePolynomial PrincipalSeriesExtension RealBlockFourierFinite
  RealInducedBlockBound RealInducedStandardBound

local notation "G" => Langlands.GeneralLinear
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "V" => fun n ds => kFiniteFunctions (realStandardModule n ds)
  (unitaryCompact ℝ n)

variable {n : ℕ}

private def leftPull (x : G n ℝ) : Module.End ℂ C(G n ℝ, ℂ) :=
  (ContinuousMap.compCLM ℂ ℂ ⟨fun y => x * y, continuous_const.mul continuous_id⟩).toLinearMap

private theorem reflection_character_sq (ds : List RealBlock) (i : Fin n) :
    realPositionCharacter ds i (-1) * realPositionCharacter ds i (-1) = 1 := by
  rcases RealStrictCharacterLanglandsQuotient.realPositionCharacter_neg_one ds i with h | h
  all_goals rw [h]; norm_num

/-- Project to the required eigenvalue for one diagonal sign reflection. -/
def signFilter (ds : List RealBlock) (i : Fin n) : Module.End ℂ C(G n ℝ, ℂ) :=
  (2 : ℂ)⁻¹ • (LinearMap.id +
    realPositionCharacter ds i (-1) • leftPull (Unitary.toUnits (signReflection n i)))

theorem signFilter_apply (ds : List RealBlock) (i : Fin n) (f : C(G n ℝ, ℂ)) (x : G n ℝ) :
    signFilter ds i f x = (2 : ℂ)⁻¹ * (f x +
      realPositionCharacter ds i (-1) * f (Unitary.toUnits (signReflection n i) * x)) := rfl

private theorem signFilter_eigen (ds : List RealBlock) (i : Fin n)
    (f : C(G n ℝ, ℂ)) (x : G n ℝ) :
    signFilter ds i f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * signFilter ds i f x := by
  simp only [signFilter_apply, toUnits_signReflection_mul_mul_self]
  calc
    _ = (2 : ℂ)⁻¹ * (1 * f (Unitary.toUnits (signReflection n i) * x) +
        realPositionCharacter ds i (-1) * f x) := by rw [one_mul]
    _ = _ := by rw [← reflection_character_sq ds i]; ring

private theorem signFilter_preserves (ds : List RealBlock) (i j : Fin n)
    (f : C(G n ℝ, ℂ))
    (hf : ∀ x, f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * f x) (x : G n ℝ) :
    signFilter ds j f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * signFilter ds j f x := by
  simp only [signFilter_apply]
  have h : Unitary.toUnits (signReflection n j) * (Unitary.toUnits (signReflection n i) * x) =
      Unitary.toUnits (signReflection n i) * (Unitary.toUnits (signReflection n j) * x) := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, signReflection_mul_comm]
  rw [h, hf, hf]
  ring

private theorem signFilter_fixes (ds : List RealBlock) (i : Fin n) (f : C(G n ℝ, ℂ))
    (hf : ∀ x, f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * f x) : signFilter ds i f = f := by
  apply ContinuousMap.ext
  intro x
  rw [signFilter_apply, hf, ← mul_assoc, reflection_character_sq, one_mul]
  ring

private theorem signFilter_isKFin (ds : List RealBlock) (i : Fin n)
    {f : C(G n ℝ, ℂ)} (hf : IsKFin f) :
    IsKFin (signFilter ds i f) := by
  change (2 : ℂ)⁻¹ • ((f : G n ℝ → ℂ) + realPositionCharacter ds i (-1) •
    (fun x => f (Unitary.toUnits (signReflection n i) * x))) ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (G n ℝ)) (unitaryCompact ℝ n)
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hf (Submodule.smul_mem _ _
    (isKFin_leftTranslate hf _)))

/-- Compose the sign averages indexed by the given coordinate list. -/
def signFilters (ds : List RealBlock) (I : List (Fin n)) : Module.End ℂ C(G n ℝ, ℂ) :=
  I.foldr (fun i A => (signFilter ds i).comp A) LinearMap.id

@[simp]
theorem signFilters_nil (ds : List RealBlock) (f : C(G n ℝ, ℂ)) :
    signFilters ds ([] : List (Fin n)) f = f := rfl

@[simp]
theorem signFilters_cons (ds : List RealBlock) (i : Fin n) (I : List (Fin n))
    (f : C(G n ℝ, ℂ)) :
    signFilters ds (i :: I) f = signFilter ds i (signFilters ds I f) := rfl

private theorem signFilters_eigen (ds : List RealBlock) {I : List (Fin n)}
    {i : Fin n} (hi : i ∈ I) (f : C(G n ℝ, ℂ)) (x : G n ℝ) :
    signFilters ds I f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * signFilters ds I f x := by
  induction I generalizing x with
  | nil => simp at hi
  | cons j I ih =>
    simp only [signFilters_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact signFilter_eigen ds i _ x
    · exact signFilter_preserves ds i j _ (ih hi') x

private theorem signFilters_fixes (ds : List RealBlock) (I : List (Fin n)) (f : C(G n ℝ, ℂ))
    (hf : ∀ i x, f (Unitary.toUnits (signReflection n i) * x) =
      realPositionCharacter ds i (-1) * f x) :
    signFilters ds I f = f := by
  induction I with
  | nil => rfl
  | cons i I ih => rw [signFilters_cons, ih, signFilter_fixes ds i f (hf i)]

private theorem signFilters_isKFin (ds : List RealBlock) (I : List (Fin n))
    {f : C(G n ℝ, ℂ)} (hf : IsKFin f) : IsKFin (signFilters ds I f) := by
  induction I with
  | nil => exact hf
  | cons i I ih => exact signFilter_isKFin ds i ih

private theorem signFilters_eqOn (ds : List RealBlock) (I : List (Fin n))
    {f h : C(G n ℝ, ℂ)} (he : Set.EqOn f h (unitaryCompact ℝ n)) :
    Set.EqOn (signFilters ds I f) (signFilters ds I h) (unitaryCompact ℝ n) := by
  induction I with
  | nil => exact he
  | cons i I ih =>
    intro x hx
    have hs : Unitary.toUnits (signReflection n i) ∈ unitaryCompact ℝ n :=
      (signReflection n i).2
    simp only [signFilters_cons, signFilter_apply, ih hx,
      ih ((unitaryCompact ℝ n).mul_mem hs hx)]

private def polynomialExtension (s : Fin n → ℂ) : polynomialFunctions n →ₗ[ℂ] C(G n ℝ, ℂ) where
  toFun φ := ⟨extension s φ, by
    obtain ⟨_, hφ⟩ := exists_mvPolynomial_of_mem_polynomialFunctions φ.2
    exact (contMDiff_extension s hφ).continuous⟩
  map_add' φ ψ := ContinuousMap.ext fun x => congrFun
    ((extensionLinear s).map_add (φ : K n → ℂ) (ψ : K n → ℂ)) x
  map_smul' c φ := ContinuousMap.ext fun x => congrFun
    ((extensionLinear s).map_smul c (φ : K n → ℂ)) x

private theorem extension_mul_unitary (s : Fin n → ℂ) (φ : K n → ℂ) (x : G n ℝ) (k : K n) :
    extension s φ (x * Unitary.toUnits k) = extension s (fun y => φ (y * k)) x := by
  obtain ⟨a, u, v, hv, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  let b := Matrix.diagonal (fun i => (a i : ℝ)) * (u : G n ℝ).val
  let w : K n := ⟨v.val, hv⟩
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hd (i : Fin n) : b i i ≠ 0 := by
    change (Matrix.diagonal (fun i => (a i : ℝ)) * (u : G n ℝ).val) i i ≠ 0
    rw [diagonal_mul_apply_self]
    exact (a i).ne_zero
  have hx : (Iwasawa.diagonalUnits a * u * v : G n ℝ).val = b * w.val := rfl
  have hxk : (Iwasawa.diagonalUnits a * u * v * Unitary.toUnits k : G n ℝ).val =
      b * (w * k).val := by
    change (b * w.val) * k.val = b * (w.val * k.val)
    exact mul_assoc _ _ _
  rw [extension_eq s φ hb hd (w * k).2 hxk, extension_eq s _ hb hd w.2 hx, mul_assoc]

private theorem polynomialExtension_isKFin (s : Fin n → ℂ) (φ : polynomialFunctions n) :
    IsKFin (polynomialExtension s φ) := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions φ.2
  let S := translateSpan (φ : K n → ℂ)
  have : FiniteDimensional ℂ S := by
    change FiniteDimensional ℂ (translateSpan (φ : K n → ℂ))
    rw [funext hP]
    exact TranslateFinite.finiteDimensional_span_eval P
  rw [IsKFin, mem_kFiniteVectors_iff]
  refine Submodule.finiteDimensional_of_le (S₂ := S.map (extensionLinear s)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  let u : K n := ⟨((k : G n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩
  refine ⟨_, translate_mem_translateSpan (φ : K n → ℂ) u, funext fun x => ?_⟩
  change extension s (fun y => (φ : K n → ℂ) (y * u)) x =
    extension s φ (x * (k : G n ℝ))
  rw [← extension_mul_unitary, RealReverseTransfer.toUnits_mk k.2]

private def coordinateList (n : ℕ) : List (Fin n) := List.ofFn id

private theorem mem_coordinateList (i : Fin n) : i ∈ coordinateList n :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Sign averaging and removal of low rotation modes, applied to an extension of the compact
polynomial. The resulting compact restriction supplies the standard extension. -/
def filteredPolynomial (ds : List RealBlock) : polynomialFunctions n →ₗ[ℂ] C(G n ℝ, ℂ) :=
  (highModesList (slots ds n)).comp
    ((signFilters ds (coordinateList n)).comp (polynomialExtension 0))

private def filteredExtension (ds : List RealBlock) : polynomialFunctions n →ₗ[ℂ] (G n ℝ → ℂ) :=
  (extensionLinear (shiftedExponent n (realPositionExponent ds))).comp
    ((LinearMap.funLeft ℂ ℂ (Unitary.toUnits : K n → G n ℝ)).comp
      ((ContinuousMap.coeFnLinearMap ℂ).comp (filteredPolynomial ds)))

private theorem filteredExtension_mem {ds : List RealBlock} (hr : realRank ds = n)
    (φ : polynomialFunctions n) : filteredExtension ds φ ∈ V n ds := by
  let F := filteredPolynomial ds φ
  let q (k : K n) := F (Unitary.toUnits k)
  have hKF : IsKFin F :=
    highModesList_isKFin (slots ds n) (signFilters_isKFin ds (coordinateList n)
      (polynomialExtension_isKFin 0 φ))
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_kFiniteVectors F.continuous hKF (1 : G n ℝ)
  have hqP : q = fun k : K n => MvPolynomial.eval
      (fun ij => ((k : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) P := by
    funext k
    simpa only [q, one_mul] using hP k
  have hqfin : FiniteDimensional ℂ (translateSpan q) := by
    rw [hqP]
    exact TranslateFinite.finiteDimensional_span_eval P
  have hqsign (i : Fin n) (k : K n) :
      q (signReflection n i * k) = realPositionCharacter ds i (-1) * q k := by
    change F (Unitary.toUnits (signReflection n i * k)) = _
    rw [map_mul]
    exact highModesList_signReflection (slots ds n) i _ (signFilters_eigen ds
      (mem_coordinateList i) (polynomialExtension 0 φ)) (Unitary.toUnits k)
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hExt := extension_mem_kFiniteFunctions _ hχ.eq
    (F.continuous.comp continuous_unitary_toUnits) hqfin
    (RealLeviModes.apply_signDiagonal_mul hχ.one hqsign)
  apply RealLeviModes.mem_kFin_standard_of_window hr hExt
  intro t ht j hj x hx
  have hzero := coefficientMap_highModesList_eq_zero (pairwise_slots ds n) ht
    (mem_lowModes.mpr hj) (signFilters ds (coordinateList n) (polynomialExtension 0 φ))
  have hz : blockFourierCoefficient n t.p j F x = 0 :=
    congrArg (fun h : C(G n ℝ, ℂ) => h x) hzero
  change blockFourierCoefficient n t.p j
    (extension (shiftedExponent n (realPositionExponent ds)) q) x = 0
  rw [← hz]
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hk := (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n t.p θ) hx
  rw [← RealReverseTransfer.toUnits_mk hk, extension_unitary]

/-- The projection from polynomial compact functions to the actual compact-finite standard
module. -/
def compactProjection {ds : List RealBlock} (hr : realRank ds = n) :
    polynomialFunctions n →ₗ[ℂ] V n ds :=
  (filteredExtension ds).codRestrict _ (filteredExtension_mem hr)

theorem compactProjection_apply (ds : List RealBlock) (hr : realRank ds = n)
    (φ : polynomialFunctions n) (x : G n ℝ) :
    (compactProjection hr φ).1 x = extension (shiftedExponent n (realPositionExponent ds))
      (fun k => filteredPolynomial ds φ (Unitary.toUnits k)) x := rfl

theorem compactProjection_compactRestriction {ds : List RealBlock} (hr : realRank ds = n)
    (f : V n ds) : compactProjection hr (compactRestriction ds f) = f := by
  let F : C(G n ℝ, ℂ) := ⟨f, RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions f.2⟩
  have hsign := signFilters_fixes ds (coordinateList n) F
    (fun i x => apply_signReflection_mul (RealStrictCharacterLanglandsQuotient.isSignedPower ds).one
      f.2.1.1 i x)
  have hhigh : highModesList (slots ds n) F = F := by
    apply highModesList_eq_of_vanishing
    intro t ht j hj
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots ht
    apply ContinuousMap.ext
    intro x
    change blockFourierCoefficient n p j f x = 0
    exact f.2.1.2 p d hd j (by
      simpa only [Int.abs_eq_natAbs d.weight, mkSlot] using mem_lowModes.mp hj) x
  have he : Set.EqOn (polynomialExtension 0 (compactRestriction ds f)) F
      (unitaryCompact ℝ n) := by
    intro x hx
    change extension 0 (fun k => f.1 (Unitary.toUnits k)) x = f.1 x
    rw [← RealReverseTransfer.toUnits_mk hx, extension_unitary]
  have hcomp := highModesList_eqOn (slots ds n) (signFilters_eqOn ds (coordinateList n) he)
  rw [hsign, hhigh] at hcomp
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (compactProjection hr (compactRestriction ds f)).2.1.1 f.2.1.1 ?_
  intro x hx
  rw [compactProjection_apply ds hr, ← RealReverseTransfer.toUnits_mk hx, extension_unitary]
  exact hcomp hx

/-- The averaging trace uses the explicit sign and rotation projection on the kernel
columns. -/
theorem averageTrace_eq_compactProjection_integral (μ : Measure (K n)) [μ.IsHaarMeasure]
    {ds : List RealBlock} (hr : realRank ds = n) (φ : polynomialStar n) (g : G n ℝ) :
    averageTrace μ ds φ g =
      ∫ y, (compactProjection hr (kernelColumn φ y)).1 (Unitary.toUnits y * g) ∂μ :=
  averageTrace_eq_kernelIntegral μ ds φ g (compactProjection hr)
    (compactProjection_compactRestriction hr)

/-- The explicit sign and rotation projection is a left inverse to compact restriction. -/
def RealStandardCompactProjectionStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (hr : realRank ds = n) (f : V n ds),
    compactProjection hr (compactRestriction ds f) = f

theorem realStandardCompactProjection : RealStandardCompactProjectionStatement :=
  fun _ _ hr f => compactProjection_compactRestriction hr f

end Langlands.Archimedean.RealStandardCompactAverage
