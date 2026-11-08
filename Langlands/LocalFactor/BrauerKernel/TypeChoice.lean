import Langlands.LocalFactor.BrauerKernel.TypeSplit
import Langlands.LocalFactor.CommonClosureRankOneSpectral
import Langlands.LocalFactor.Abelian.LocalAnalysisHelpers
import Langlands.LocalField.Uniformizer
import Mathlib.Data.ZMod.QuotientGroup

/-! # Admissible unramified exponents for actual Brauer relations -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.PadicAbelian

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- Every continuous quasicharacter becomes of finite image after multiplication by a
suitable complex power of the normalized absolute value. -/
theorem exists_finite_range_mul_absPower
    (χ : @HarmonicAnalysis.Quasicharacter K.Carrier _ T.topology) :
    ∃ t : ℂ, (Set.range (fun x : K.Carrierˣ => (χ x : ℂ) *
      Complex.exp (-t * (Real.log (T.normalizedAbs (x : K.Carrier)) : ℂ)))).Finite := by
  let := T.topology
  let π := uniformizerUnit T
  let c : ℂ := (χ π : ℂ)
  have hc : c ≠ 0 := (χ π).ne_zero
  have hq1 : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hlogq : (Real.log T.residueCardinality : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hq1).ne'
  refine ⟨-Complex.log c / (Real.log T.residueCardinality : ℂ), ?_⟩
  apply ((quasicharacter_finite_unit_image T χ).image (fun z : ℂˣ => (z : ℂ))).subset
  rintro _ ⟨x, rfl⟩
  let k : ℤ := T.ord (x : K.Carrier)
  let u : K.Carrierˣ := x * π ^ (-k)
  have hπk : T.ord ((π ^ (-k) : K.Carrierˣ) : K.Carrier) = -k := by
    rw [Units.val_zpow_eq_zpow_val, T.ord_zpow, uniformizerUnit_ord, mul_one]
  have hu : T.ord (u : K.Carrier) = 0 := by
    change T.ord ((x : K.Carrier) * ((π ^ (-k) : K.Carrierˣ) : K.Carrier)) = 0
    rw [T.ord_mul x.ne_zero (Units.ne_zero _), hπk]
    ring
  have hxu : x = u * π ^ k := by
    simp [u, mul_assoc]
  refine ⟨χ u, ⟨⟨u, by simp [unitLevel, hu]⟩, rfl⟩, ?_⟩
  change (χ u : ℂ) = (χ x : ℂ) * Complex.exp
    (-(-Complex.log c / (Real.log T.residueCardinality : ℂ)) *
      (Real.log (T.normalizedAbs (x : K.Carrier)) : ℂ))
  have habs : (Real.log (T.normalizedAbs (x : K.Carrier)) : ℂ) =
      -(k : ℂ) * (Real.log T.residueCardinality : ℂ) := by
    rw [T.normalizedAbs_of_ne_zero x.ne_zero, Real.log_zpow]
    push_cast
    ring
  have hχx : (χ x : ℂ) = (χ u : ℂ) * c ^ k := by
    conv_lhs => rw [hxu]
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [habs, hχx]
  have hexp : Complex.exp (-(-Complex.log c / (Real.log T.residueCardinality : ℂ)) *
      (-(k : ℂ) * (Real.log T.residueCardinality : ℂ))) = c ^ (-k) := by
    rw [show -(-Complex.log c / (Real.log T.residueCardinality : ℂ)) *
        (-(k : ℂ) * (Real.log T.residueCardinality : ℂ)) = ((-k : ℤ) : ℂ) * Complex.log c by
      field_simp
      push_cast
      ring]
    rw [Complex.exp_int_mul, Complex.exp_log hc]
  rw [hexp, mul_assoc, ← zpow_add₀ hc, add_neg_cancel, zpow_zero, mul_one]

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- For normalized reciprocity, every field character has an exponent whose twisted
Weil character has finite image. -/
theorem exists_twistedWeilCharacter_finite_range (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (L : Extension F) (χ : FieldCharacter F L) :
    ∃ t : ℂ, (Set.range (twistedWeilCharacter F e L χ t)).Finite := by
  let := (fieldData F L).topology
  obtain ⟨t, ht⟩ := PadicAbelian.exists_finite_range_mul_absPower (fieldData F L) χ
  refine ⟨t, ?_⟩
  apply Set.Finite.of_finite_image _ (Units.val_injective.injOn)
  apply ht.subset
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨reciprocityUnits F e L w, ?_⟩
  change _ = ((weilCharacter F e L χ w : ℂˣ) : ℂ) *
    (CommonClosureSpectral.character F L (-t) w : ℂ)
  rw [CommonClosureSpectralAnalytic.character_eq_norm_exp F e L he]
  rfl

/-- Changing the exponent by `a` multiplies the twisted character by the twist `-a`. -/
theorem twistedWeilCharacter_add (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) (t a : ℂ) :
    twistedWeilCharacter F e L χ (t + a) =
      twistedWeilCharacter F e L χ t * (CommonClosureSpectral.character F L (-a)).toMonoidHom := by
  ext w
  change (weilCharacter F e L χ w : ℂ) * (CommonClosureSpectral.character F L (-(t + a)) w : ℂ) =
    (weilCharacter F e L χ w : ℂ) * (CommonClosureSpectral.character F L (-t) w : ℂ) *
      (CommonClosureSpectral.character F L (-a) w : ℂ)
  rw [mul_assoc, CommonClosureSpectral.character_apply, CommonClosureSpectral.character_apply,
    CommonClosureSpectral.character_apply, ← mul_zpow, ← Complex.exp_add]
  congr 3
  ring

/-- The rational lattice `(2πi / log q_F) ℚ` of unramified exponents of finite order. -/
def rationalExponents : AddSubgroup ℂ where
  carrier := {z | ∃ r : ℚ, z = (2 * Real.pi * Complex.I /
    (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ)) * r}
  add_mem' := by
    rintro _ _ ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r + s, by push_cast; ring⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro _ ⟨r, rfl⟩
    exact ⟨-r, by push_cast; ring⟩

theorem baseCardinality_log_ne_zero :
    (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ) ≠ 0 := by
  have h1 : (1 : ℝ) < CommonClosureSpectral.baseCardinality F := by
    change (1 : ℝ) < (F.canonicalTopologicalData.residueCardinality : ℝ)
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact_mod_cast (Real.log_pos h1).ne'

/-- Twisting by a rational exponent has finite image. -/
theorem character_neg_finite_range (L : Extension F) {a : ℂ}
    (ha : a ∈ rationalExponents F) :
    (Set.range (CommonClosureSpectral.character F L (-a))).Finite := by
  obtain ⟨r, rfl⟩ := ha
  let ζ : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * r))
    (Complex.exp_ne_zero _)
  have hζ : IsOfFinOrder ζ := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨r.den, r.den_pos, ?_⟩
    apply Units.ext
    simp only [ζ, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have hr : (r : ℂ) = (r.num : ℂ) / (r.den : ℂ) := by
      exact_mod_cast (Rat.num_div_den r).symm
    rw [hr]
    have hd : (r.den : ℂ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    field_simp
  apply (Set.finite_coe_iff.mp hζ.finite_zpowers).subset
  rintro _ ⟨w, rfl⟩
  refine ⟨(CommonClosureSpectral.baseDegree F L w).toAdd, ?_⟩
  apply Units.ext
  change ((ζ ^ (CommonClosureSpectral.baseDegree F L w).toAdd : ℂˣ) : ℂ) = _
  rw [CommonClosureSpectral.character_apply, Units.val_zpow_eq_zpow_val]
  congr 1
  simp only [ζ, Units.val_mk0]
  congr 1
  field_simp [baseCardinality_log_ne_zero F]

/-- Finite image of the twisted character persists under a rational change of exponent. -/
theorem twistedWeilCharacter_finite_range_add (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) {t a : ℂ}
    (ht : (Set.range (twistedWeilCharacter F e L χ t)).Finite)
    (ha : a ∈ rationalExponents F) :
    (Set.range (twistedWeilCharacter F e L χ (t + a))).Finite := by
  rw [twistedWeilCharacter_add]
  apply (ht.mul (character_neg_finite_range F L ha)).subset
  rintro _ ⟨w, rfl⟩
  exact Set.mul_mem_mul ⟨w, rfl⟩ ⟨w, rfl⟩

/-- The chosen representative of the class of an exponent modulo the rational lattice. -/
def typeRepresentative (t : ℂ) : ℂ :=
  (QuotientAddGroup.mk t : ℂ ⧸ rationalExponents F).out

theorem typeRepresentative_sub_mem (t : ℂ) :
    typeRepresentative F t - t ∈ rationalExponents F := by
  have h : (QuotientAddGroup.mk (typeRepresentative F t) : ℂ ⧸ rationalExponents F) =
      QuotientAddGroup.mk t := Quotient.out_eq _
  rw [QuotientAddGroup.eq] at h
  have := (rationalExponents F).neg_mem h
  simpa [sub_eq_add_neg, add_comm] using this

/-- Distinct representatives are separated modulo every nonzero integral multiple. -/
theorem typeRepresentative_separated (t t' : ℂ)
    (hne : typeRepresentative F t ≠ typeRepresentative F t') (m : ℤ) (hm : m ≠ 0) :
    Complex.exp (-(typeRepresentative F t - typeRepresentative F t') *
      (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ) * m) ≠ 1 := by
  intro h
  apply hne
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hmem : typeRepresentative F t - typeRepresentative F t' ∈ rationalExponents F := by
    refine ⟨-(n : ℚ) / m, ?_⟩
    have hlog := baseCardinality_log_ne_zero F
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hn
  have hq : (QuotientAddGroup.mk (typeRepresentative F t) : ℂ ⧸ rationalExponents F) =
      QuotientAddGroup.mk (typeRepresentative F t') := by
    rw [QuotientAddGroup.eq]
    have := (rationalExponents F).neg_mem hmem
    simpa [sub_eq_add_neg, add_comm] using this
  unfold typeRepresentative at hq ⊢
  rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at hq
  rw [hq]

/-- The subgroup of `W_E`, inside `W_L ∩ W_E`, on which a character of `W_L` is trivial. -/
def kernelInWeil {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) : Subgroup (weilSubgroup F E) :=
  (ψ.comp (nestedWeilEquiv F E g.extension g.inclusion).toMonoidHom).ker.map g.nested.subtype

theorem kernelInWeil_le_nested {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) : kernelInWeil F g ψ ≤ g.nested := by
  rintro _ ⟨s, -, rfl⟩
  exact s.property

theorem kernelInWeil_apply {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) (n : weilSubgroup F E)
    (hn : n ∈ kernelInWeil F g ψ) (h : n ∈ g.nested) :
    ψ (nestedWeilEquiv F E g.extension g.inclusion ⟨n, h⟩) = 1 := by
  obtain ⟨s, hs, rfl⟩ := hn
  exact hs

theorem kernelInWeil_finiteIndex {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) (hψ : (Set.range ψ).Finite) :
    (kernelInWeil F g ψ).FiniteIndex := by
  let f := ψ.comp (nestedWeilEquiv F E g.extension g.inclusion).toMonoidHom
  have hf : Finite f.range := by
    change Finite ((f.range : Set ℂˣ))
    apply Set.finite_coe_iff.mpr
    apply hψ.subset
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  have hk : f.ker.FiniteIndex := inferInstance
  constructor
  rw [kernelInWeil, Subgroup.index_map_subtype]
  exact mul_ne_zero hk.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero)

/-- Admissible exponents exist for every presentation: both twisted characters of each
generator have finite image, and distinct exponents are separated. -/
theorem exists_admissible_exponents (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (z : Presentation F E) :
    ∃ t₁ t₂ : Generator F E → ℂ,
      (∀ g ∈ z.support,
        (Set.range (twistedWeilCharacter F e g.extension g.first (t₁ g))).Finite) ∧
      (∀ g ∈ z.support,
        (Set.range (twistedWeilCharacter F e g.extension g.second (t₂ g))).Finite) ∧
      (∀ τ ∈ z.support.image t₁ ∪ z.support.image t₂,
        ∀ τ' ∈ z.support.image t₁ ∪ z.support.image t₂, τ ≠ τ' → ∀ m : ℤ, m ≠ 0 →
          Complex.exp (-(τ - τ') *
            (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ) * m) ≠ 1) := by
  choose s₁ hs₁ using fun g : Generator F E =>
    exists_twistedWeilCharacter_finite_range F e he g.extension g.first
  choose s₂ hs₂ using fun g : Generator F E =>
    exists_twistedWeilCharacter_finite_range F e he g.extension g.second
  refine ⟨fun g => typeRepresentative F (s₁ g), fun g => typeRepresentative F (s₂ g),
    ?_, ?_, ?_⟩
  · intro g _
    have h := twistedWeilCharacter_finite_range_add F e g.extension g.first (hs₁ g)
      (typeRepresentative_sub_mem F (s₁ g))
    simpa using h
  · intro g _
    have h := twistedWeilCharacter_finite_range_add F e g.extension g.second (hs₂ g)
      (typeRepresentative_sub_mem F (s₂ g))
    simpa using h
  · intro τ hτ τ' hτ' hne m hm
    have hrep : ∀ x ∈ z.support.image (fun g => typeRepresentative F (s₁ g)) ∪
        z.support.image (fun g => typeRepresentative F (s₂ g)),
        ∃ a, x = typeRepresentative F a := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;>
        obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hx <;> exact ⟨_, rfl⟩
    obtain ⟨a, rfl⟩ := hrep τ hτ
    obtain ⟨b, rfl⟩ := hrep τ' hτ'
    exact typeRepresentative_separated F a b hne m hm

/-- **Type separation of every actual Brauer relation.** For admissible exponents, every
type component of an actual relation vanishes identically on `W_E`. -/
theorem exists_typeComponent_eq_zero (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) :
    ∃ t₁ t₂ : Generator F E → ℂ,
      (∀ g ∈ z.support,
        (Set.range (twistedWeilCharacter F e g.extension g.first (t₁ g))).Finite) ∧
      (∀ g ∈ z.support,
        (Set.range (twistedWeilCharacter F e g.extension g.second (t₂ g))).Finite) ∧
      (∀ τ ∈ z.support.image t₁ ∪ z.support.image t₂,
        ∀ τ' ∈ z.support.image t₁ ∪ z.support.image t₂, τ ≠ τ' → ∀ m : ℤ, m ≠ 0 →
          Complex.exp (-(τ - τ') *
            (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ) * m) ≠ 1) ∧
      ∀ τ w, typeComponent F e z t₁ t₂ τ w = 0 := by
  obtain ⟨t₁, t₂, h₁, h₂, hsep⟩ := exists_admissible_exponents F e he E z
  refine ⟨t₁, t₂, h₁, h₂, hsep, ?_⟩
  let K : z.support → Subgroup (weilSubgroup F E) := fun g =>
    kernelInWeil F g.1 (twistedWeilCharacter F e g.1.extension g.1.first (t₁ g.1)) ⊓
      kernelInWeil F g.1 (twistedWeilCharacter F e g.1.extension g.1.second (t₂ g.1))
  have hK : ∀ g, (K g).FiniteIndex := by
    intro g
    have := kernelInWeil_finiteIndex F g.1 _ (h₁ g.1 g.2)
    have := kernelInWeil_finiteIndex F g.1 _ (h₂ g.1 g.2)
    infer_instance
  have hN₀ : (⨅ g, K g).FiniteIndex := Subgroup.finiteIndex_iInf hK
  let N := (⨅ g, K g).normalCore
  have hNK : ∀ g, N ≤ K g := fun g => (Subgroup.normalCore_le _).trans (iInf_le K g)
  have hNle : ∀ g ∈ z.support, N ≤ g.nested := fun g hg =>
    (hNK ⟨g, hg⟩).trans (inf_le_left.trans (kernelInWeil_le_nested F g _))
  exact typeComponent_eq_zero F e E z hz t₁ t₂ N hNle
    (fun g hg n hn => kernelInWeil_apply F g _ n
      (inf_le_left (a := kernelInWeil F g _) (hNK ⟨g, hg⟩ hn)) _)
    (fun g hg n hn => kernelInWeil_apply F g _ n
      (inf_le_right (b := kernelInWeil F g _) (hNK ⟨g, hg⟩ hn)) _)
    hsep

end Langlands.LocalFactor.NonabelianBrauer
