import Langlands.Global.AdelicScalarHaarChar
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.CompletionResidue
import Langlands.Representation.Whittaker.Iwasawa

/-! # Haar scaling of the adeles by a uniformizer at one finite place

Multiplication by the idele `ι_v(ϖ)` (a uniformizer `ϖ` at the finite place `v`, `1` at every
other place) scales additive Haar measure on `𝔸_F` by `N(v)⁻¹`, and multiplication by
`ι_v(ϖ) ^ k` scales it by `N(v) ^ (-k)`. The paired Markdown records the argument.
-/

noncomputable section

universe u

namespace Langlands.Global.RankinSelbergGlobal.WhittakerCellAdelicScaling

open MeasureTheory MeasureTheory.Measure NumberField IsDedekindDomain
open scoped NNReal ENNReal Pointwise Valued

section Counting

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]

/-- **Counting cosets.** If `J ≤ O` are additive subgroups and `ρ : O → k` is a surjective
additive homomorphism onto a finite group with kernel `J`, then every left-invariant measure
gives `O` the mass `|k|` times the mass of `J`. -/
theorem measure_eq_card_mul (μ : Measure G) [μ.IsAddLeftInvariant]
    {k : Type*} [AddGroup k] [Finite k] (O J : AddSubgroup G) (hJO : J ≤ O) (ρ : O →+ k)
    (hρ : Function.Surjective ρ) (hker : ∀ y : O, ρ y = 0 ↔ (y : G) ∈ J)
    (hJ : MeasurableSet (J : Set G)) :
    μ O = Nat.card k * μ J := by
  classical
  have : Fintype k := Fintype.ofFinite k
  choose r hr using hρ
  let T : k → Set G := fun c => (r c : G) +ᵥ (J : Set G)
  have hmem : ∀ c y, y ∈ T c ↔ -(r c : G) + y ∈ J := fun c y =>
    Set.mem_vadd_set_iff_neg_vadd_mem
  have hsub : ∀ c y, y ∈ T c → y ∈ O := by
    intro c y hy
    have h1 := hJO ((hmem c y).1 hy)
    have h2 : (r c : G) + (-(r c : G) + y) ∈ O := O.add_mem (r c).2 h1
    simpa using h2
  have hval : ∀ c y (hy : y ∈ O), y ∈ T c → ρ ⟨y, hy⟩ = c := by
    intro c y hy hc
    have hJ' := (hmem c y).1 hc
    have h0 : ρ ⟨-(r c : G) + y, O.add_mem (O.neg_mem (r c).2) hy⟩ = 0 := (hker _).2 hJ'
    have hdec : (⟨y, hy⟩ : O) = r c + ⟨-(r c : G) + y, O.add_mem (O.neg_mem (r c).2) hy⟩ :=
      Subtype.ext (by simp)
    rw [hdec, map_add, h0, add_zero, hr]
  have hunion : (O : Set G) = ⋃ c, T c := by
    ext y
    constructor
    · intro hy
      refine Set.mem_iUnion.2 ⟨ρ ⟨y, hy⟩, (hmem _ _).2 ?_⟩
      have h0 : ρ (-(r (ρ ⟨y, hy⟩)) + ⟨y, hy⟩) = 0 := by
        rw [map_add, map_neg, hr, neg_add_cancel]
      exact (hker _).1 h0
    · intro hy
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy
      exact hsub c y hc
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c d hcd
    rw [Function.onFun, Set.disjoint_left]
    intro y hc hd
    apply hcd
    have hyO : y ∈ O := hsub c y hc
    rw [← hval c y hyO hc, hval d y hyO hd]
  have hmeas : ∀ c, MeasurableSet (T c) := fun c => hJ.const_vadd _
  have hT : ∀ c, μ (T c) = μ J := fun c => measure_vadd μ _ _
  rw [hunion, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

end Counting

section Valuation

/-- In a linearly ordered commutative group with zero, a nonzero `x` with `ϖ x < 1` has
`x ≤ 1`, once every nonzero value is an integer power of `ϖ` with `ϖ < 1`. -/
theorem le_one_of_mul_lt_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {w : Valuation K Γ₀} {ϖ : Kˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement w ϖ) {x : K}
    (h : w ((ϖ : K) * x) < 1) : w x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn⟩ := hϖ.2 x hx
  have hpos : 0 < w (ϖ : K) := GeneralLinear.Iwasawa.valuation_pos w ϖ
  rw [map_mul, hn, ← zpow_one_add₀ hpos.ne'] at h
  rw [hn]
  have h1 := (zpow_lt_one_iff_right_of_lt_one₀ hpos hϖ.1).1 h
  exact (zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1).2 (by omega)

end Valuation

variable (F : Type u) [Field F] [NumberField F]

section Finite

/-- The normalized valuation of the completion `F_v`, with values in `ℤₘ₀`. -/
abbrev valuation (v : FinitePlace F) :
    Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ)) :=
  Valued.v

/-- The integral finite adeles `Ô = ∏_w 𝒪_w`, as an additive subgroup. -/
abbrev integralSubgroup : AddSubgroup (FiniteAdeles F) :=
  (integralFiniteAdeles F).toAddSubgroup

/-- The additive subgroup `{y ∈ Ô : y_v ∈ 𝔪_v}` of the integral finite adeles. -/
def maximalSubgroup (v : FinitePlace F) : AddSubgroup (FiniteAdeles F) where
  carrier := {y | y ∈ integralFiniteAdeles F ∧
    valuation F v (y v) < 1}
  zero_mem' := ⟨(integralFiniteAdeles F).zero_mem, by
    change valuation F v 0 < 1
    simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(integralFiniteAdeles F).add_mem ha hb, ?_⟩
    change valuation F v (a v + b v) < 1
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha' hb')
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(integralFiniteAdeles F).neg_mem ha, ?_⟩
    change valuation F v (-(a v)) < 1
    rwa [Valuation.map_neg]

theorem mem_maximalSubgroup (v : FinitePlace F) (y : FiniteAdeles F) :
    y ∈ maximalSubgroup F v ↔ y ∈ integralFiniteAdeles F ∧
      valuation F v (y v) < 1 :=
  Iff.rfl

theorem maximalSubgroup_le (v : FinitePlace F) :
    maximalSubgroup F v ≤ integralSubgroup F :=
  fun _ h => h.1

local notation "Ov" v => LocalGalois.baseIntegers (FiniteCompletion F v)

theorem norm_le_one_of_mem (v : FinitePlace F) {y : FiniteAdeles F}
    (hy : y ∈ integralFiniteAdeles F) : ‖y v‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2 ((mem_integralFiniteAdeles F y).1 hy v)

/-- The reduction `Ô → 𝒪_v → 𝒪_v / 𝔪_v` at `v`. -/
def residue (v : FinitePlace F) :
    integralSubgroup F →+ IsLocalRing.ResidueField (Ov v) :=
  (IsLocalRing.residue (Ov v)).toAddMonoidHom.comp
    { toFun := fun y => ⟨(y : FiniteAdeles F) v, norm_le_one_of_mem F v y.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem residue_apply (v : FinitePlace F) (y : integralSubgroup F) :
    residue F v y = IsLocalRing.residue (Ov v) ⟨(y : FiniteAdeles F) v,
      norm_le_one_of_mem F v y.2⟩ := rfl

theorem residue_eq_zero_iff (v : FinitePlace F) (y : integralSubgroup F) :
    residue F v y = 0 ↔ (y : FiniteAdeles F) ∈ maximalSubgroup F v := by
  rw [residue_apply, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff,
    mem_maximalSubgroup]
  change ‖(y : FiniteAdeles F) v‖ < 1 ↔ _
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

theorem residue_surjective (v : FinitePlace F) : Function.Surjective (residue F v) := by
  classical
  intro c
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  have hx : (x : FiniteCompletion F v) ∈ v.adicCompletionIntegers F :=
    (Valued.toNormedField.norm_le_one_iff).1 x.2
  let y : FiniteAdeles F :=
    RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v
      (x : FiniteCompletion F v)
  have hy : y ∈ integralFiniteAdeles F := by
    rw [mem_integralFiniteAdeles]
    intro w
    change Pi.single v (x : FiniteCompletion F v) w ∈ w.adicCompletionIntegers F
    by_cases hw : w = v
    · subst hw
      simpa using hx
    · rw [Pi.single_eq_of_ne hw]
      exact (w.adicCompletionIntegers F).zero_mem
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [residue_apply]
  congr 1
  apply Subtype.ext
  change Pi.single v (x : FiniteCompletion F v) v = (x : FiniteCompletion F v)
  simp

theorem isOpen_maximalSubgroup (v : FinitePlace F) :
    IsOpen (maximalSubgroup F v : Set (FiniteAdeles F)) := by
  have h : (maximalSubgroup F v : Set (FiniteAdeles F)) =
      (integralFiniteAdeles F : Set (FiniteAdeles F)) ∩
        (fun y : FiniteAdeles F => y v) ⁻¹' Metric.ball 0 1 := by
    ext y
    simp only [SetLike.mem_coe, mem_maximalSubgroup, Set.mem_inter_iff, Set.mem_preimage,
      mem_ball_zero_iff, Valued.toNormedField.norm_lt_one_iff]
  rw [h]
  exact (isOpen_integralFiniteAdeles F).inter
    (Metric.isOpen_ball.preimage (RestrictedProduct.continuous_eval v))

/-- The finite idele `ι_v(a)`: `a` at `v` and `1` at every other finite place. -/
def finiteSingle (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ) : (FiniteAdeles F)ˣ :=
  Units.map (FiniteAdeleRing.ofAdicCompletion F v) a

theorem finiteSingle_apply_self (v : FinitePlace F) (a : (FiniteCompletion F v)ˣ) :
    ((finiteSingle F v a : FiniteAdeles F)) v = a := by
  classical
  change Pi.mulSingle v (a : FiniteCompletion F v) v = _
  simp

theorem finiteSingle_apply_of_ne {v w : FinitePlace F} (hw : w ≠ v)
    (a : (FiniteCompletion F v)ˣ) :
    ((finiteSingle F v a : FiniteAdeles F)) w = 1 := by
  classical
  change Pi.mulSingle v (a : FiniteCompletion F v) w = _
  exact Pi.mulSingle_eq_of_ne hw _

/-- Multiplication by `ι_v(ϖ)` carries exactly the integral finite adeles into
`{y ∈ Ô : y_v ∈ 𝔪_v}`. -/
theorem finiteSingle_mul_mem_iff (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (valuation F v) ϖ) (y : FiniteAdeles F) :
    (finiteSingle F v ϖ : FiniteAdeles F) * y ∈ maximalSubgroup F v ↔
      y ∈ integralFiniteAdeles F := by
  have happ : ∀ w, ((finiteSingle F v ϖ : FiniteAdeles F) * y) w =
      (finiteSingle F v ϖ : FiniteAdeles F) w * y w := fun w => rfl
  rw [mem_maximalSubgroup, mem_integralFiniteAdeles, mem_integralFiniteAdeles]
  constructor
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w = v
    · subst hw
      rw [happ, finiteSingle_apply_self] at h2
      exact le_one_of_mul_lt_one hϖ h2
    · have := h1 w
      rwa [happ, finiteSingle_apply_of_ne F hw, one_mul] at this
  · intro h
    have hv : valuation F v
        ((ϖ : FiniteCompletion F v) * y v) < 1 := by
      rw [map_mul]
      calc valuation F v (ϖ : FiniteCompletion F v) *
            valuation F v (y v)
          ≤ valuation F v (ϖ : FiniteCompletion F v) * 1 := by
            gcongr
            exact h v
        _ < 1 := by rw [mul_one]; exact hϖ.1
    refine ⟨fun w => ?_, ?_⟩
    · by_cases hw : w = v
      · subst hw
        rw [happ, finiteSingle_apply_self]
        exact hv.le
      · rw [happ, finiteSingle_apply_of_ne F hw, one_mul]
        exact h w
    · rw [happ, finiteSingle_apply_self]
      exact hv

/-- **Finite-adelic scaling.** Multiplication by `ι_v(ϖ)` scales additive Haar measure on the
finite adeles by `N(v)⁻¹`. -/
theorem addEquivAddHaarChar_mulLeft_finiteSingle [MeasurableSpace (FiniteAdeles F)]
    [BorelSpace (FiniteAdeles F)] (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (valuation F v) ϖ) :
    let := finiteAdeles_locallyCompactSpace F
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (finiteSingle F v ϖ)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  let := finiteAdeles_locallyCompactSpace F
  set φ := ContinuousAddEquiv.mulLeft (finiteSingle F v ϖ)
  let μ : Measure (FiniteAdeles F) := addHaar
  set J := maximalSubgroup F v
  have hJo : IsOpen (J : Set (FiniteAdeles F)) := isOpen_maximalSubgroup F v
  have hJm : MeasurableSet (J : Set (FiniteAdeles F)) := hJo.measurableSet
  have hpre : φ ⁻¹' (J : Set (FiniteAdeles F)) = (integralFiniteAdeles F : Set _) := by
    ext y
    exact finiteSingle_mul_mem_iff F v hϖ y
  have hcount : μ (integralFiniteAdeles F : Set (FiniteAdeles F)) =
      Nat.card (IsLocalRing.ResidueField (Ov v)) * μ J :=
    measure_eq_card_mul μ (integralSubgroup F) J (maximalSubgroup_le F v) (residue F v)
      (residue_surjective F v) (residue_eq_zero_iff F v) hJm
  rw [CompletionResidue.card_residueField] at hcount
  have hJpos : μ J ≠ 0 := (hJo.measure_pos μ ⟨0, J.zero_mem⟩).ne'
  have hJfin : μ J ≠ ∞ :=
    (measure_mono (maximalSubgroup_le F v)).trans_lt
      (isCompact_integralFiniteAdeles F).measure_lt_top |>.ne
  have hsmul := addEquivAddHaarChar_smul_preimage μ (X := (J : Set (FiniteAdeles F))) φ
  rw [hpre, hcount] at hsmul
  have hN : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hkey : ((addEquivAddHaarChar φ : ℝ≥0) : ℝ≥0∞) * (Ideal.absNorm v.asIdeal : ℝ≥0) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc] at hsmul
    have := (ENNReal.mul_eq_right hJpos hJfin).1 (by simpa using hsmul)
    exact_mod_cast this
  have hkey' : addEquivAddHaarChar φ * (Ideal.absNorm v.asIdeal : ℝ≥0) = 1 := by
    exact_mod_cast hkey
  exact eq_inv_of_mul_eq_one_left hkey'

end Finite

section Units

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

omit [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] in
theorem mulLeft_one : ContinuousAddEquiv.mulLeft (1 : Rˣ) = ContinuousAddEquiv.refl R := by
  ext x
  simp

omit [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] in
theorem mulLeft_mul (r s : Rˣ) :
    ContinuousAddEquiv.mulLeft (r * s) =
      (ContinuousAddEquiv.mulLeft s).trans (ContinuousAddEquiv.mulLeft r) := by
  ext x
  simp [mul_assoc]

/-- The additive Haar modulus of left multiplication, `r ↦ mod(x ↦ r x)`, as a monoid
homomorphism on the units of a locally compact topological ring. -/
def mulLeftHaarChar : Rˣ →* ℝ≥0 where
  toFun r := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r)
  map_one' := by rw [mulLeft_one, addEquivAddHaarChar_refl]
  map_mul' r s := by rw [mulLeft_mul, addEquivAddHaarChar_trans, mul_comm]

theorem mulLeftHaarChar_apply (r : Rˣ) :
    mulLeftHaarChar r = addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r) :=
  rfl

end Units

section Full

/-- **Adelic scaling.** Multiplication by the idele `ι_v(ϖ)` (`ϖ` at `v`, `1` at every other
place) scales additive Haar measure on `𝔸_F` by `N(v)⁻¹`. -/
theorem addEquivAddHaarChar_mulLeft_finiteIdeleInclusion [MeasurableSpace (Adeles F)]
    [BorelSpace (Adeles F)] (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F v) ϖ) :
    let := adeles_locallyCompactSpace F
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  classical
  let := adeles_locallyCompactSpace F
  let : MeasurableSpace (InfiniteAdeles F) := borel _
  have : BorelSpace (InfiniteAdeles F) := ⟨rfl⟩
  let : MeasurableSpace (FiniteAdeles F) := borel _
  have : BorelSpace (FiniteAdeles F) := ⟨rfl⟩
  have := infiniteAdeles_secondCountableTopology F
  have := finiteAdeles_secondCountableTopology F
  have := finiteAdeles_locallyCompactSpace F
  have := adeles_secondCountableTopology F
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F
  -- the two factor measures
  let μi : Measure (InfiniteAdeles F) :=
    (volume : Measure (mixedEmbedding.mixedSpace F)).map R.symm
  have : IsAddHaarMeasure μi :=
    R.symm.toAddEquiv.isAddHaarMeasure_map volume (continuous_infiniteAdeleCoordinates_symm F)
      (continuous_infiniteAdeleCoordinates F)
  let μf : Measure (FiniteAdeles F) := addHaar
  -- the adeles as the product of their infinite and finite parts
  let e : (InfiniteAdeles F × FiniteAdeles F) ≃ₜ+ Adeles F :=
    { toFun := fun p => p
      invFun := fun p => p
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  have he : Measurable e := e.continuous.measurable
  let μ : Measure (Adeles F) := (μi.prod μf).map e
  have : IsAddHaarMeasure μ := e.isAddHaarMeasure_map _
  have : Regular μ := by
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Adeles F)) := inferInstance
    exact regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  apply Langlands.HarmonicAnalysis.addEquivAddHaarChar_eq_of_smul_map μ
  -- multiplication by `ι_v(ϖ)` is multiplication by `ι_v(ϖ)` on the finite factor
  let g := ContinuousAddEquiv.mulLeft (finiteSingle F v ϖ)
  have hg : Measurable g := g.continuous.measurable
  have hφ : Measurable (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ)) :=
    (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ)).continuous.measurable
  have hcomp : (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ) : Adeles F → Adeles F) ∘
      e = e ∘ Prod.map id g := by
    funext p
    change ((1 * p.1, (finiteSingle F v ϖ : FiniteAdeles F) * p.2) :
      InfiniteAdeles F × FiniteAdeles F) = (p.1, (finiteSingle F v ϖ : FiniteAdeles F) * p.2)
    rw [one_mul]
  have hf : addEquivAddHaarChar g • μf.map g = μf := addEquivAddHaarChar_smul_map μf g
  rw [addEquivAddHaarChar_mulLeft_finiteSingle F v hϖ] at hf
  change ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ •
      Measure.map (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ)) ((μi.prod μf).map e) =
    (μi.prod μf).map e
  rw [Measure.map_map hφ he, hcomp, ← Measure.map_map he (measurable_id.prodMap hg),
    ← Measure.map_prod_map μi μf measurable_id hg, Measure.map_id,
    ← Measure.map_smul _ he.aemeasurable, ← Measure.prod_smul_right, hf]

/-- **Adelic scaling by powers.** Multiplication by `ι_v(ϖ) ^ k` scales additive Haar measure
on `𝔸_F` by `N(v) ^ (-k)`. -/
theorem addEquivAddHaarChar_mulLeft_finiteIdeleInclusion_zpow [MeasurableSpace (Adeles F)]
    [BorelSpace (Adeles F)] (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F v) ϖ) (k : ℤ) :
    let := adeles_locallyCompactSpace F
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ ^ k)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-k) := by
  intro _
  have h1 : addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (finiteIdeleInclusion F v ϖ)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ :=
    addEquivAddHaarChar_mulLeft_finiteIdeleInclusion F v hϖ
  rw [← mulLeftHaarChar_apply, map_zpow, mulLeftHaarChar_apply, h1, zpow_neg, inv_zpow]

end Full

end Langlands.Global.RankinSelbergGlobal.WhittakerCellAdelicScaling
