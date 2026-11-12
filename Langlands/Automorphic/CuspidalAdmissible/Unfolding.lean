import Langlands.Automorphic.OperatorDeterminantSliceMeasure

/-!
# Bounded multiplicity and quotient integrals

If every orbit of a discrete subgroup `Γ` meets a set `t` in at most `M` points, then the
integral over `t` of a lifted function is at most `M` times its quotient integral. This is
the converse of the covering inequality `lintegral_restrict_discreteQuotientMeasure_le`.
-/

noncomputable section

universe uF uH

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Langlands.Global.LeftCosetSpace

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ν : Measure H) [ν.IsMulLeftInvariant]

/-- **Unfolding with bounded multiplicity.** If `t` lies over `A` and every orbit meets `t`
in at most `M` points, then `∫_t f([x]) dν ≤ M ∫_A f`. -/
theorem lintegral_le_mul_discreteQuotientMeasure
    (A : Set (Langlands.Global.LeftCosetSpace Γ)) (hA : MeasurableSet A)
    (t : Set H) (ht : MeasurableSet t) (htA : ∀ x ∈ t, mk Γ x ∈ A)
    (M : ℝ≥0∞) (hmult : ∀ x : H, (({γ : Γ | (γ : H) * x ∈ t}.encard : ℕ∞) : ℝ≥0∞) ≤ M)
    (f : Langlands.Global.LeftCosetSpace Γ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in t, f (mk Γ x) ∂ν ≤ M * ∫⁻ q in A, f q ∂discreteQuotientMeasure Γ hΓ ν := by
  classical
  let := countable_of_isDiscrete Γ hΓ
  let s := fundamentalDomain Γ hΓ
  let k : H → ℝ≥0∞ := t.indicator (fun x => f (mk Γ x))
  have hk : Measurable k := (hf.comp (measurable_mk Γ)).indicator ht
  have hpt (x : H) : ∑' γ : Γ, k ((γ : H) * x) ≤ M * A.indicator f (mk Γ x) := by
    by_cases hx : mk Γ x ∈ A
    · rw [indicator_of_mem hx]
      have hk' : ∀ γ : Γ, k ((γ : H) * x) =
          {γ : Γ | (γ : H) * x ∈ t}.indicator (fun _ => f (mk Γ x)) γ := by
        intro γ
        change t.indicator (fun x => f (mk Γ x)) ((γ : H) * x) = _
        by_cases hγ : (γ : H) * x ∈ t
        · rw [indicator_of_mem hγ, indicator_of_mem (show γ ∈ {γ : Γ | (γ : H) * x ∈ t}
            from hγ), mk_subgroup_mul]
        · rw [indicator_of_notMem hγ, indicator_of_notMem (show γ ∉ {γ : Γ | (γ : H) * x ∈ t}
            from hγ)]
      calc ∑' γ : Γ, k ((γ : H) * x)
          = ∑' γ : Γ, {γ : Γ | (γ : H) * x ∈ t}.indicator (fun _ => f (mk Γ x)) γ :=
            tsum_congr hk'
        _ = ∑' _ : {γ : Γ | (γ : H) * x ∈ t}, f (mk Γ x) := (tsum_subtype _ _).symm
        _ = ({γ : Γ | (γ : H) * x ∈ t}.encard : ℝ≥0∞) * f (mk Γ x) :=
            ENNReal.tsum_set_const _ _
        _ ≤ M * f (mk Γ x) := by gcongr; exact hmult x
    · have h0 : ∀ γ : Γ, k ((γ : H) * x) = 0 := fun γ =>
        indicator_of_notMem (fun h => hx ((mk_subgroup_mul Γ γ x) ▸ htA _ h)) _
      simp only [h0, tsum_zero]
      exact zero_le
  calc ∫⁻ x in t, f (mk Γ x) ∂ν = ∫⁻ x, k x ∂ν := (lintegral_indicator ht _).symm
    _ = ∑' γ : Γ, ∫⁻ x in s, k ((γ : H) * x) ∂ν :=
      (isFundamentalDomain Γ hΓ ν).lintegral_eq_tsum'' k
    _ = ∫⁻ x in s, ∑' γ : Γ, k ((γ : H) * x) ∂ν := by
      rw [lintegral_tsum]
      intro γ
      exact (hk.comp (measurable_const.mul measurable_id)).aemeasurable
    _ ≤ ∫⁻ x in s, M * A.indicator f (mk Γ x) ∂ν := lintegral_mono hpt
    _ = M * ∫⁻ x in s, A.indicator f (mk Γ x) ∂ν :=
      lintegral_const_mul M ((hf.indicator hA).comp (measurable_mk Γ))
    _ = M * ∫⁻ q, A.indicator f q ∂discreteQuotientMeasure Γ hΓ ν := by
      congr 1
      exact (lintegral_map (hf.indicator hA) (measurable_mk Γ)).symm
    _ = M * ∫⁻ q in A, f q ∂discreteQuotientMeasure Γ hΓ ν := by
      rw [lintegral_indicator hA]

end Langlands.Global.LeftCosetSpace

namespace Langlands.Automorphic.OperatorDeterminantSlice

open CategoryTheory _root_.AlgebraicGeometry Langlands.Global
open scoped CategoryTheory.MonObj

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
  [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

local instance unfoldingIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance unfoldingSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- **Unfolding for the actual quotient.** If `t` lies over the quotient set `A` and each
rational orbit meets `t` in at most `M` points, then the `matrixHaarMeasure` integral over
`t` of a lifted function is at most `M` times its `quotientHaarMeasure` integral over `A`. -/
theorem lintegral_le_mul_quotient (A : Set (Quotient F n)) (hA : MeasurableSet A)
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t) (htA : ∀ x ∈ t, point F n x ∈ A)
    (M : ℝ≥0∞)
    (hmult : ∀ x : AdelicGL F n,
      (({γ : RationalGL F n | AdelicGL.rational F n γ * x ∈ t}.encard : ℕ∞) : ℝ≥0∞) ≤ M)
    (h : Quotient F n → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x in t, h (point F n x) ∂matrixHaarMeasure F n ≤
      M * ∫⁻ q in A, h q ∂quotientHaarMeasure F n := by
  classical
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  have he : Measurable (fun y => e y) := e.continuous.measurable
  have hpoint : ∀ y, point F n (e y) = LeftCosetSpace.mk Γ y := fun y => by
    simp [point, e]
    rfl
  have hpm : Measurable (point F n) :=
    (LeftCosetSpace.measurable_mk _).comp e.symm.continuous.measurable
  -- rational elements of the subgroup, as rational matrices
  let ψ : Γ → RationalGL F n := fun γ =>
    GeneralLinearGroupPoints.rationalEquiv F n (Classical.choose γ.2)
  have hψ : ∀ γ : Γ, e (γ : AdelicGroupPoints F (matrixGroupScheme F n)) =
      AdelicGL.rational F n (ψ γ) := fun γ => by
    have := Classical.choose_spec γ.2
    change e _ = _
    rw [← this]
    exact GeneralLinearGroupPoints.adelicHomeomorph_rational F n _
  have hψinj : Function.Injective ψ := by
    intro γ₁ γ₂ h12
    apply Subtype.ext
    apply e.injective
    rw [hψ, hψ, h12]
  have hmult' : ∀ y : AdelicGroupPoints F (matrixGroupScheme F n),
      (({γ : Γ | (γ : AdelicGroupPoints F (matrixGroupScheme F n)) * y ∈ e ⁻¹' t}.encard :
        ℕ∞) : ℝ≥0∞) ≤ M := by
    intro y
    refine le_trans ?_ (hmult (e y))
    exact_mod_cast Set.encard_le_encard_of_injOn (f := ψ)
      (fun γ hγ => show AdelicGL.rational F n (ψ γ) * e y ∈ t by
        rw [← hψ, ← map_mul]; exact hγ)
      hψinj.injOn
  have hle := LeftCosetSpace.lintegral_le_mul_discreteQuotientMeasure Γ
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n))
    Measure.haar A hA (e ⁻¹' t) (ht.preimage he)
    (fun y hy => (hpoint y) ▸ htA _ hy) M hmult' h hh
  refine le_trans (le_of_eq ?_) hle
  rw [← lintegral_indicator ht _, matrixHaarMeasure,
    lintegral_map (g := fun x => e x)
      (show Measurable (t.indicator (fun x => h (point F n x))) from
        (hh.comp hpm).indicator ht) he,
    ← lintegral_indicator (ht.preimage he) _]
  congr 1
  funext y
  simp only [Set.indicator, Set.mem_preimage, hpoint]

/-- **Covering for the actual quotient.** If every point of `GL_n(𝔸)` over the quotient set
`A` has a rational translate in `t`, then the `quotientHaarMeasure` integral over `A` is at most
the `matrixHaarMeasure` integral over `t` of the lifted function. -/
theorem lintegral_quotient_le_cover (A : Set (Quotient F n)) (hA : MeasurableSet A)
    (t : Set (AdelicGL F n)) (ht : MeasurableSet t)
    (hcover : ∀ x : AdelicGL F n, point F n x ∈ A →
      ∃ γ : RationalGL F n, AdelicGL.rational F n γ * x ∈ t)
    (h : Quotient F n → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ q in A, h q ∂quotientHaarMeasure F n ≤
      ∫⁻ x in t, h (point F n x) ∂matrixHaarMeasure F n := by
  classical
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  let Γ := AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)
  have he : Measurable (fun y => e y) := e.continuous.measurable
  have hpoint : ∀ y, point F n (e y) = LeftCosetSpace.mk Γ y := fun y => by
    simp [point, e]
    rfl
  have hpm : Measurable (point F n) :=
    (LeftCosetSpace.measurable_mk _).comp e.symm.continuous.measurable
  have hcov : ∀ y : AdelicGroupPoints F (matrixGroupScheme F n),
      LeftCosetSpace.mk Γ y ∈ A → ∃ γ : Γ, (γ : AdelicGroupPoints F (matrixGroupScheme F n)) * y ∈
        e ⁻¹' t := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcover (e y) (by rw [hpoint]; exact hy)
    let r := (GeneralLinearGroupPoints.rationalEquiv F n).symm γ
    refine ⟨⟨AdelicGroupPoints.rational F (matrixGroupScheme F n) r, ⟨r, rfl⟩⟩, ?_⟩
    change e (AdelicGroupPoints.rational F (matrixGroupScheme F n) r * y) ∈ t
    simpa only [e, r, map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational,
      MulEquiv.apply_symm_apply] using hγ
  have hle := LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le Γ
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (matrixGroupScheme F n))
    Measure.haar A hA (e ⁻¹' t) (ht.preimage he) hcov h hh
  refine hle.trans (le_of_eq ?_)
  rw [← lintegral_indicator ht _, matrixHaarMeasure,
    lintegral_map (g := fun x => e x)
      (show Measurable (t.indicator (fun x => h (point F n x))) from
        (hh.comp hpm).indicator ht) he,
    ← lintegral_indicator (ht.preimage he) _]
  congr 1
  funext y
  simp only [Set.indicator, Set.mem_preimage, hpoint]

end Langlands.Automorphic.OperatorDeterminantSlice
