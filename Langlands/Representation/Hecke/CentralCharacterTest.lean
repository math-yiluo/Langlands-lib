import Langlands.Analysis.Local.QuotientAverageReal
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Locally constant tests with a prescribed central character -/

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Set Topology

namespace Langlands.Hecke

universe u v

/-- A locally constant group character with values in the complex unit circle. -/
structure SmoothUnitaryCharacter (H : Type u) [Group H] [TopologicalSpace H] where
  toMonoidHom : H →* Circle
  locallyConstant : IsLocallyConstant toMonoidHom

namespace SmoothUnitaryCharacter

variable {H : Type u} [Group H] [TopologicalSpace H]
variable {K : Type v} [Group K] [TopologicalSpace K]

instance : CoeFun (SmoothUnitaryCharacter H) (fun _ => H → Circle) :=
  ⟨fun ω => ω.toMonoidHom⟩

@[simp] theorem complex_mul (ω : SmoothUnitaryCharacter H) (x y : H) :
    (ω (x * y) : ℂ) = (ω x : ℂ) * (ω y : ℂ) := by
  rw [map_mul, Circle.coe_mul]

@[simp] theorem complex_inv (ω : SmoothUnitaryCharacter H) (x : H) :
    (ω x⁻¹ : ℂ) = (ω x : ℂ)⁻¹ := by
  rw [map_inv, Circle.coe_inv]

theorem locallyConstant_complex (ω : SmoothUnitaryCharacter H) :
    IsLocallyConstant (fun x => (ω x : ℂ)) :=
  ω.locallyConstant.comp ((↑) : Circle → ℂ)

/-- Pullback of a smooth unitary character along a continuous group homomorphism. -/
def comp (ω : SmoothUnitaryCharacter H) (φ : K →ₜ* H) : SmoothUnitaryCharacter K where
  toMonoidHom := ω.toMonoidHom.comp φ.toMonoidHom
  locallyConstant := ω.locallyConstant.comp_continuous φ.continuous

@[simp] theorem comp_apply (ω : SmoothUnitaryCharacter H) (φ : K →ₜ* H) (x : K) :
    ω.comp φ x = ω (φ x) := rfl

end SmoothUnitaryCharacter

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace CentralCharacterTest

/-- The projection of the nonzero set to the actual quotient by `Z`. -/
def quotientSupport (Z : Subgroup G) (f : G → ℂ) : Set (G ⧸ Z) :=
  QuotientGroup.mk '' support f

variable {Z : Subgroup G} [Z.Normal] {ω : SmoothUnitaryCharacter Z}

/-- The nonzero set of an equivariant function is saturated for the quotient map. -/
theorem preimage_quotientSupport {f : G → ℂ}
    (hf : ∀ (z : Z) (g : G), f (z.val * g) = (ω z : ℂ)⁻¹ * f g) :
    QuotientGroup.mk ⁻¹' quotientSupport Z f = support f := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    let z : Z := ⟨x * y⁻¹, by simpa only [div_eq_mul_inv] using
      QuotientGroup.eq_iff_div_mem.mp hyx.symm⟩
    have hx : z.val * y = x := by simp [z]
    rw [← hx, mem_support, hf]
    exact mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero (ω z))) hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- The projected support of a locally constant equivariant function is closed and open. -/
theorem isClopen_quotientSupport_of_equivariant {f : G → ℂ} (hf : IsLocallyConstant f)
    (hcov : ∀ (z : Z) (g : G), f (z.val * g) = (ω z : ℂ)⁻¹ * f g) :
    IsClopen (quotientSupport Z f) := by
  have hm := (QuotientGroup.isQuotientMap_mk Z).isCoinducing
  have hs : IsClopen (support f) := (hf.isClopen_fiber 0).compl
  have he := preimage_quotientSupport hcov
  exact ⟨hm.isClosed_preimage.mp (he ▸ hs.isClosed), hm.isOpen_preimage.mp (he ▸ hs.isOpen)⟩

/-- Pointwise linear space of locally constant functions with compact projected support
and inverse central-character equivariance. -/
def submodule (Z : Subgroup G) [Z.Normal] (ω : SmoothUnitaryCharacter Z) :
    Submodule ℂ (G → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ IsCompact (quotientSupport Z f) ∧
    ∀ (z : Z) (g : G), f (z.val * g) = (ω z : ℂ)⁻¹ * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp [quotientSupport], by simp⟩
  add_mem' {f g} hf hg := by
    have hl := hf.1.add hg.1
    have hc (z : Z) (x : G) : (f + g) (z.val * x) = (ω z : ℂ)⁻¹ * (f + g) x := by
      simp only [Pi.add_apply, hf.2.2, hg.2.2, mul_add]
    refine ⟨hl, (hf.2.1.union hg.2.1).of_isClosed_subset
      (isClopen_quotientSupport_of_equivariant hl hc).isClosed ?_, hc⟩
    change QuotientGroup.mk '' support (f + g) ⊆
      (QuotientGroup.mk '' support f) ∪ (QuotientGroup.mk '' support g)
    rw [← Set.image_union]
    exact Set.image_mono (support_add f g)
  smul_mem' c f hf := by
    have hl : IsLocallyConstant (c • f) := hf.1.comp (c • ·)
    have hc (z : Z) (x : G) : (c • f) (z.val * x) = (ω z : ℂ)⁻¹ * (c • f) x := by
      simp only [Pi.smul_apply, smul_eq_mul, hf.2.2, mul_left_comm c]
    refine ⟨hl, hf.2.1.of_isClosed_subset
      (isClopen_quotientSupport_of_equivariant hl hc).isClosed ?_, hc⟩
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, fun h => hx ?_, rfl⟩
    change c • f x = 0
    rw [h, smul_zero]

end CentralCharacterTest

/-- The space of tests transforming by the inverse of `ω` along the central subgroup `Z`. -/
abbrev CentralCharacterTest (Z : Subgroup G) [Z.Normal] (ω : SmoothUnitaryCharacter Z) :=
  ↥(CentralCharacterTest.submodule Z ω)

namespace CentralCharacterTest

variable {Z : Subgroup G} [Z.Normal] {ω : SmoothUnitaryCharacter Z}

instance : CoeFun (CentralCharacterTest Z ω) (fun _ => G → ℂ) := ⟨fun f => f.val⟩

@[ext] theorem ext {f g : CentralCharacterTest Z ω} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

theorem locallyConstant (f : CentralCharacterTest Z ω) : IsLocallyConstant (f : G → ℂ) :=
  f.property.1

theorem isCompact_quotientSupport (f : CentralCharacterTest Z ω) :
    IsCompact (quotientSupport Z f) := f.property.2.1

theorem equivariant (f : CentralCharacterTest Z ω) (z : Z) (g : G) :
    f (z.val * g) = (ω z : ℂ)⁻¹ * f g := f.property.2.2 z g

theorem isClopen_quotientSupport (f : CentralCharacterTest Z ω) :
    IsClopen (quotientSupport Z f) :=
  isClopen_quotientSupport_of_equivariant f.locallyConstant f.equivariant

section Average

open HarmonicAnalysis (SchwartzBruhat)

variable [IsTopologicalGroup G] [MeasurableSpace Z] [BorelSpace Z]
variable (ω : SmoothUnitaryCharacter Z) (dz : Measure Z)

/-- The pointwise weighted integral along a central coset. -/
def averageValue (f : SchwartzBruhat G) (g : G) : ℂ :=
  ∫ z : Z, (ω z : ℂ) * f (z.val * g) ∂dz

omit [Z.Normal] in
theorem averageIntegrand_integrable [IsFiniteMeasureOnCompacts dz]
    (hZ : IsClosed (Z : Set G)) (f : SchwartzBruhat G) (g : G) :
    Integrable (fun z : Z => (ω z : ℂ) * f (z.val * g)) dz := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ω.locallyConstant_complex.continuous.mul
      (f.continuous.comp (continuous_subtype_val.mul_const g))
  · exact (QuotientIntegration.hasCompactSupport_subgroup_mul_of_hasCompactSupport
      Z hZ f f.hasCompactSupport g).mul_left

omit [TopologicalSpace G] [Z.Normal] [IsTopologicalGroup G] [BorelSpace Z] in
/-- A left-invariant measure on a central subgroup is right invariant as well. -/
theorem isMulRightInvariant_of_central [IsMulLeftInvariant dz]
    (hZ : Z ≤ Subgroup.center G) : IsMulRightInvariant dz := by
  constructor
  intro z
  have he : (fun x : Z => x * z) = fun x => z * x := by
    funext x
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ z.property) x.val)
  rw [he, map_mul_left_eq_self]

omit [Z.Normal] in
private theorem averageValue_equivariant [IsMulRightInvariant dz]
    (f : SchwartzBruhat G) (z : Z) (g : G) :
    averageValue ω dz f (z.val * g) = (ω z : ℂ)⁻¹ * averageValue ω dz f g := by
  calc
    _ = ∫ w : Z, (ω z : ℂ)⁻¹ * ((ω (w * z) : ℂ) * f ((w * z).val * g)) ∂dz := by
      apply integral_congr_ae (Eventually.of_forall fun w => ?_)
      rw [Subgroup.coe_mul, mul_assoc w.val z.val g, ω.complex_mul,
        mul_comm (ω w : ℂ) (ω z : ℂ), mul_assoc (ω z : ℂ),
        inv_mul_cancel_left₀ (Circle.coe_ne_zero (ω z))]
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg ((ω z : ℂ)⁻¹ * ·)
        (integral_mul_right_eq_self (μ := dz) (fun w : Z => (ω w : ℂ) * f (w.val * g)) z)

omit [IsTopologicalGroup G] [BorelSpace Z] in
private theorem quotientSupport_averageValue_subset (f : SchwartzBruhat G) :
    quotientSupport Z (averageValue ω dz f) ⊆ quotientSupport Z f := by
  rintro _ ⟨g, hg, rfl⟩
  by_contra h
  apply hg
  apply integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  suffices f (z.val * g) = 0 by simp [this]
  by_contra hz
  exact h ⟨z.val * g, hz, by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 z.property, one_mul]⟩

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

omit [Z.Normal] [BorelSpace Z] in
private theorem averageValue_locallyConstant (f : SchwartzBruhat G) :
    IsLocallyConstant (averageValue ω dz f) := by
  classical
  obtain ⟨K, _, _, hK⟩ := TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hr := (hK f (Finset.mem_singleton_self f)).2
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have hnear : ∀ᶠ k : G in 𝓝 (1 : G), k ∈ (K : Set G) := K.mem_nhds_one
  have hmem : ∀ᶠ y in 𝓝 g, g⁻¹ * y ∈ (K : Set G) :=
    ((continuous_const.mul continuous_id).tendsto g).eventually (by simpa using hnear)
  filter_upwards [hmem] with y hy
  let k : K.toSubgroup := ⟨g⁻¹ * y, hy⟩
  apply integral_congr_ae (Eventually.of_forall fun z => ?_)
  have he : z.val * g * (k : G) = z.val * y := by simp [k, mul_assoc]
  exact congrArg ((ω z : ℂ) * ·) (he ▸ hr k (z.val * g))

/-- Averaging an ordinary Schwartz–Bruhat test against the prescribed character and
subgroup Haar measure gives a complex-linear map into the central-character test space. -/
def average (hZ : IsClosed (Z : Set G)) (hcentral : Z ≤ Subgroup.center G) [dz.IsHaarMeasure] :
    SchwartzBruhat G →ₗ[ℂ] CentralCharacterTest Z ω where
  toFun f := by
    letI := isMulRightInvariant_of_central dz hcentral
    have hl := averageValue_locallyConstant ω dz f
    have he := averageValue_equivariant ω dz f
    refine ⟨averageValue ω dz f, hl, ?_, he⟩
    exact ((TestFunction.isCompact_support f).image QuotientGroup.continuous_mk).of_isClosed_subset
      (isClopen_quotientSupport_of_equivariant hl he).isClosed (quotientSupport_averageValue_subset ω dz f)
  map_add' f g := by
    ext x
    change (∫ z : Z, (ω z : ℂ) * (f (z.val * x) + g (z.val * x)) ∂dz) = _
    simp_rw [mul_add]
    exact integral_add (averageIntegrand_integrable ω dz hZ f x)
      (averageIntegrand_integrable ω dz hZ g x)
  map_smul' c f := by
    ext x
    change (∫ z : Z, (ω z : ℂ) * (c * f (z.val * x)) ∂dz) = c * _
    simp_rw [mul_left_comm (ω _ : ℂ) c]
    exact integral_const_mul c _

@[simp] theorem average_apply (hZ : IsClosed (Z : Set G)) (hcentral : Z ≤ Subgroup.center G)
    [dz.IsHaarMeasure] (f : SchwartzBruhat G) (g : G) :
    average ω dz hZ hcentral f g = ∫ z : Z, (ω z : ℂ) * f (z.val * g) ∂dz := rfl

theorem quotientSupport_average_subset (hZ : IsClosed (Z : Set G))
    (hcentral : Z ≤ Subgroup.center G) [dz.IsHaarMeasure] (f : SchwartzBruhat G) :
    quotientSupport Z (average ω dz hZ hcentral f) ⊆ quotientSupport Z f :=
  quotientSupport_averageValue_subset ω dz f

end Average

end CentralCharacterTest
end Langlands.Hecke
