import Langlands.Representation.MatrixCoefficient.CentralCosetSum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The twisted `ℓ²` space of a coset space and its left translations

Let `J` be a subgroup of a group `G` and `ψ : J →* ℂ` a unitary character. Functions
`f : G → ℂ` with `f (g * j) = f g * ψ j` are determined by their values on the chosen
representatives `α.out` of the cosets `α ∈ G ⧸ J`. This file identifies them with functions on
`G ⧸ J` through `lift`, and studies the Hilbert space `ℓ²(G ⧸ J)` (Mathlib's `lp`) with the
left translations `translate h`, which are unitary.

* `lift F g = phase g * F (g J)`, with `lift_mul`, `lift_out`, `lift_restrict`.
* `translate h`: left translation by `h` as a linear isometry equivalence;
  `lift (translate h F) g = lift F (h⁻¹ * g)`.
* `xi`: the twisted indicator vector of `J`, with `lift xi j = ψ j` on `J` and `0` off `J`.
* `eq_zero_of_apply_xi`: `xi` is separating for the commutant of the translations.
* `norm_apply_xi_eq_norm_star_apply_xi`: `‖x xi‖ = ‖star x xi‖` for `x` in that commutant,
  when `J` is open, contains the center, and `G ⧸ Z(G)` carries a left and right invariant
  Haar measure giving the image of `J` finite measure.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace Langlands.TwistedCoset

section Algebra

variable {G : Type*} [Group G] (J : Subgroup G) (ψ : J →* ℂ)

theorem out_inv_mul_mem (g : G) : (QuotientGroup.mk g : G ⧸ J).out⁻¹ * g ∈ J := by
  obtain ⟨j, hj, hout⟩ := CentralCoset.exists_out_mk_eq_mul J g
  rw [hout, mul_inv_rev, inv_mul_cancel_right]
  exact J.inv_mem hj

/-- The phase `ψ (ḡ⁻¹ * g)`, where `ḡ` is the chosen representative of the coset `g J`. -/
def phase (g : G) : ℂ := ψ ⟨_, out_inv_mul_mem J g⟩

theorem phase_mul (g : G) {j : G} (hj : j ∈ J) :
    phase J ψ (g * j) = phase J ψ g * ψ ⟨j, hj⟩ := by
  unfold phase
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem g hj, mul_assoc]

theorem phase_out (α : G ⧸ J) : phase J ψ α.out = 1 := by
  unfold phase
  have h1 : (⟨_, out_inv_mul_mem J α.out⟩ : J) = 1 := by
    apply Subtype.ext
    simp only [QuotientGroup.out_eq', inv_mul_cancel, OneMemClass.coe_one]
  rw [h1, map_one]

/-- The `ψ`-equivariant function on `G` with values `F` on the chosen representatives. -/
def lift (F : G ⧸ J → ℂ) (g : G) : ℂ := phase J ψ g * F (QuotientGroup.mk g)

theorem lift_mul (F : G ⧸ J → ℂ) (g : G) {j : G} (hj : j ∈ J) :
    lift J ψ F (g * j) = lift J ψ F g * ψ ⟨j, hj⟩ := by
  unfold lift
  rw [phase_mul J ψ g hj, QuotientGroup.mk_mul_of_mem g hj]
  ring

theorem lift_out (F : G ⧸ J → ℂ) (α : G ⧸ J) : lift J ψ F α.out = F α := by
  unfold lift
  rw [phase_out, QuotientGroup.out_eq', one_mul]

/-- A `ψ`-equivariant function is the lift of its values on the chosen representatives. -/
theorem lift_restrict (f : G → ℂ)
    (hf : ∀ g : G, ∀ (j : G) (hj : j ∈ J), f (g * j) = f g * ψ ⟨j, hj⟩) :
    lift J ψ (fun α => f α.out) = f := by
  funext g
  obtain ⟨j, hj, hout⟩ := CentralCoset.exists_out_mk_eq_mul J g
  show phase J ψ g * f (QuotientGroup.mk g : G ⧸ J).out = f g
  rw [hout, hf g j hj]
  have hone : phase J ψ g * ψ ⟨j, hj⟩ = 1 := by
    unfold phase
    rw [← map_mul]
    convert map_one ψ
    apply Subtype.ext
    simp [hout, mul_assoc]
  calc phase J ψ g * (f g * ψ ⟨j, hj⟩) = (phase J ψ g * ψ ⟨j, hj⟩) * f g := by ring
    _ = f g := by rw [hone, one_mul]

theorem lift_add (F F' : G ⧸ J → ℂ) (g : G) :
    lift J ψ (F + F') g = lift J ψ F g + lift J ψ F' g := by
  simp only [lift, Pi.add_apply, mul_add]

theorem lift_smul (c : ℂ) (F : G ⧸ J → ℂ) (g : G) :
    lift J ψ (c • F) g = c * lift J ψ F g := by
  simp only [lift, Pi.smul_apply, smul_eq_mul]
  ring

/-- Left translation: `translateFun h F α = lift F (h⁻¹ * α.out)`. -/
def translateFun (h : G) (F : G ⧸ J → ℂ) : G ⧸ J → ℂ := fun α => lift J ψ F (h⁻¹ * α.out)

theorem lift_translateFun (h : G) (F : G ⧸ J → ℂ) :
    lift J ψ (translateFun J ψ h F) = fun g => lift J ψ F (h⁻¹ * g) :=
  lift_restrict J ψ (fun g => lift J ψ F (h⁻¹ * g)) fun g j hj => by
    rw [← mul_assoc]
    exact lift_mul J ψ F _ hj

variable {J ψ}

theorem norm_phase (hψ : ∀ j, ‖ψ j‖ = 1) (g : G) : ‖phase J ψ g‖ = 1 := hψ _

theorem norm_lift (hψ : ∀ j, ‖ψ j‖ = 1) (F : G ⧸ J → ℂ) (g : G) :
    ‖lift J ψ F g‖ = ‖F (QuotientGroup.mk g)‖ := by
  unfold lift
  rw [norm_mul, norm_phase hψ, one_mul]

theorem enorm_eq_of_norm_eq {a b : ℂ} (h : ‖a‖ = ‖b‖) : ‖a‖ₑ = ‖b‖ₑ := by
  simp only [enorm_eq_nnnorm]
  exact congrArg _ (NNReal.eq h)

theorem enorm_eq_one_of_norm_eq_one {a : ℂ} (h : ‖a‖ = 1) : ‖a‖ₑ = 1 := by
  have := enorm_eq_of_norm_eq (a := a) (b := 1) (by rw [h, norm_one])
  rwa [enorm_one] at this

theorem enorm_lift (hψ : ∀ j, ‖ψ j‖ = 1) (F : G ⧸ J → ℂ) (g : G) :
    ‖lift J ψ F g‖ₑ = ‖F (QuotientGroup.mk g)‖ₑ :=
  enorm_eq_of_norm_eq (norm_lift hψ F g)

theorem norm_translateFun (hψ : ∀ j, ‖ψ j‖ = 1) (h : G) (F : G ⧸ J → ℂ) (α : G ⧸ J) :
    ‖translateFun J ψ h F α‖ = ‖F (h⁻¹ • α)‖ := by
  unfold translateFun
  rw [norm_lift hψ]
  congr 2
  exact MulAction.Quotient.mk_smul_out J h⁻¹ α

end Algebra

section Hilbert

variable {G : Type*} [Group G] (J : Subgroup G)

/-- The Hilbert space `ℓ²(G ⧸ J)`. -/
abbrev L2 := lp (fun _ : G ⧸ J => ℂ) 2

variable {J} {ψ : J →* ℂ} (hψ : ∀ j, ‖ψ j‖ = 1)

/-- Two vectors with equal extended squared norms have equal norms. -/
theorem norm_eq_of_enorm_sq_eq {E : Type*} [SeminormedAddCommGroup E] {x y : E}
    (h : ‖x‖ₑ ^ 2 = ‖y‖ₑ ^ 2) : ‖x‖ = ‖y‖ := by
  have h' : ‖x‖ₑ = ‖y‖ₑ := le_antisymm
    ((ENNReal.pow_le_pow_left_iff two_ne_zero).mp h.le)
    ((ENNReal.pow_le_pow_left_iff two_ne_zero).mp h.ge)
  exact le_antisymm (enorm_le_iff_norm_le.mp h'.le) (enorm_le_iff_norm_le.mp h'.ge)

include hψ in
theorem tsum_enorm_translateFun (h : G) (F : L2 J) :
    ∑' α, ‖translateFun J ψ h F α‖ₑ ^ 2 = ‖F‖ₑ ^ 2 := by
  rw [Langlands.Analysis.lp_two_enorm_sq_eq_tsum]
  have hpt : ∀ α, ‖translateFun J ψ h F α‖ₑ ^ 2 = ‖F (h⁻¹ • α)‖ₑ ^ 2 := fun α => by
    rw [enorm_eq_of_norm_eq (norm_translateFun hψ h F α)]
  simp_rw [hpt]
  exact Equiv.tsum_eq (MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ J)) fun α => ‖F α‖ₑ ^ 2

include hψ in
theorem memℓp_translateFun (h : G) (F : L2 J) : Memℓp (translateFun J ψ h F) 2 := by
  apply Langlands.Analysis.memℓp_two_of_tsum_enorm_ne_top
  rw [tsum_enorm_translateFun hψ h F]
  exact ENNReal.pow_ne_top enorm_ne_top

/-- Left translation by `h` on `ℓ²(G ⧸ J)` as a linear map. -/
def translateₗ (h : G) : L2 J →ₗ[ℂ] L2 J where
  toFun F := ⟨translateFun J ψ h F, memℓp_translateFun hψ h F⟩
  map_add' F F' := by
    ext α
    change lift J ψ (⇑(F + F')) (h⁻¹ * α.out) =
      lift J ψ (⇑F) (h⁻¹ * α.out) + lift J ψ (⇑F') (h⁻¹ * α.out)
    rw [lp.coeFn_add, lift_add]
  map_smul' c F := by
    ext α
    change lift J ψ (⇑(c • F)) (h⁻¹ * α.out) = c * lift J ψ (⇑F) (h⁻¹ * α.out)
    rw [lp.coeFn_smul, lift_smul]

theorem translateₗ_apply (h : G) (F : L2 J) (α : G ⧸ J) :
    translateₗ hψ h F α = lift J ψ F (h⁻¹ * α.out) := rfl

theorem lift_translateₗ (h : G) (F : L2 J) (g : G) :
    lift J ψ (translateₗ hψ h F) g = lift J ψ F (h⁻¹ * g) :=
  congrFun (lift_translateFun J ψ h F) g

theorem translateₗ_mul (h h' : G) (F : L2 J) :
    translateₗ hψ h (translateₗ hψ h' F) = translateₗ hψ (h * h') F := by
  ext α
  rw [translateₗ_apply, lift_translateₗ, translateₗ_apply, mul_inv_rev, mul_assoc]

theorem translateₗ_one (F : L2 J) : translateₗ hψ 1 F = F := by
  ext α
  rw [translateₗ_apply, inv_one, one_mul, lift_out]

/-- Left translation by `h` on `ℓ²(G ⧸ J)` as a unitary operator. -/
def translate (h : G) : L2 J ≃ₗᵢ[ℂ] L2 J where
  toLinearEquiv := LinearEquiv.ofLinearMap (translateₗ hψ h) (translateₗ hψ h⁻¹)
    (LinearMap.ext fun F => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [translateₗ_mul, mul_inv_cancel, translateₗ_one])
    (LinearMap.ext fun F => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [translateₗ_mul, inv_mul_cancel, translateₗ_one])
  norm_map' F := by
    apply norm_eq_of_enorm_sq_eq
    change ‖translateₗ hψ h F‖ₑ ^ 2 = ‖F‖ₑ ^ 2
    rw [Langlands.Analysis.lp_two_enorm_sq_eq_tsum]
    exact tsum_enorm_translateFun hψ h F

theorem translate_apply (h : G) (F : L2 J) : translate hψ h F = translateₗ hψ h F := rfl

theorem translate_symm (h : G) : (translate hψ h).symm = translate hψ h⁻¹ :=
  LinearIsometryEquiv.ext fun _ => rfl

theorem translate_mul_apply (h h' : G) (F : L2 J) :
    translate hψ h (translate hψ h' F) = translate hψ (h * h') F :=
  translateₗ_mul hψ h h' F

/-- The left translations, as bounded operators. -/
def translates : Set (L2 J →L[ℂ] L2 J) :=
  Set.range fun h : G => ((translate hψ h : L2 J ≃ₗᵢ[ℂ] L2 J) : L2 J →L[ℂ] L2 J)

theorem star_translate (h : G) :
    star ((translate hψ h : L2 J ≃ₗᵢ[ℂ] L2 J) : L2 J →L[ℂ] L2 J) =
      ((translate hψ h⁻¹ : L2 J ≃ₗᵢ[ℂ] L2 J) : L2 J →L[ℂ] L2 J) := by
  rw [LinearIsometryEquiv.star_eq_symm, translate_symm]

/-- The commutant of the translations consists of the operators commuting with every
translation. -/
theorem mem_centralizer_translates_iff (x : L2 J →L[ℂ] L2 J) :
    x ∈ StarSubalgebra.centralizer ℂ (translates hψ) ↔
      ∀ h : G, ∀ F : L2 J, translate hψ h (x F) = x (translate hψ h F) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro H h F
    exact congrArg (fun T : L2 J →L[ℂ] L2 J => T F) (H _ ⟨h, rfl⟩).1
  · rintro H _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · ext1 F
      exact H h F
    · rw [star_translate]
      ext1 F
      exact H h⁻¹ F

open Classical in
/-- The twisted indicator vector of `J`. -/
def xi : L2 J := lp.single 2 (QuotientGroup.mk 1 : G ⧸ J) (phase J ψ 1)⁻¹

open Classical in
include hψ in
theorem lift_xi (g : G) :
    lift J ψ (xi (ψ := ψ)) g = if h : g ∈ J then ψ ⟨g, h⟩ else 0 := by
  classical
  have hph : phase J ψ 1 ≠ 0 := by
    intro h0
    have := norm_phase hψ (1 : G)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  split_ifs with hg
  · have h1 := lift_mul J ψ (xi (ψ := ψ)) 1 hg
    rw [one_mul] at h1
    rw [h1]
    unfold lift xi
    simp only [lp.single_apply, Pi.single_eq_same]
    rw [mul_inv_cancel₀ hph, one_mul]
  · unfold lift xi
    have hne : (QuotientGroup.mk g : G ⧸ J) ≠ QuotientGroup.mk 1 := by
      intro h
      rw [QuotientGroup.eq] at h
      apply hg
      simpa using J.inv_mem h
    simp [lp.single_apply, hne]

open Classical in
include hψ in
/-- A translate of `xi` is a unit multiple of a basis vector. -/
theorem translate_xi (h : G) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      translate hψ h (xi (ψ := ψ)) = lp.single 2 (QuotientGroup.mk h : G ⧸ J) c := by
  classical
  have hmem : h⁻¹ * (QuotientGroup.mk h : G ⧸ J).out ∈ J := by
    obtain ⟨j, hj, hout⟩ := CentralCoset.exists_out_mk_eq_mul J h
    rw [hout, inv_mul_cancel_left]
    exact hj
  refine ⟨ψ ⟨_, hmem⟩, hψ _, ?_⟩
  ext β
  rw [translate_apply, translateₗ_apply, lift_xi hψ, lp.single_apply, Pi.single_apply]
  by_cases hβ : β = QuotientGroup.mk h
  · subst hβ
    simp [hmem]
  · have hnot : h⁻¹ * β.out ∉ J := by
      intro hmem'
      apply hβ
      conv_lhs => rw [← QuotientGroup.out_eq' β]
      rw [eq_comm, QuotientGroup.eq]
      exact hmem'
    simp [hβ, hnot]

include hψ in
/-- Translating `xi` by an element of `J` multiplies it by a unit. -/
theorem translate_xi_of_mem {j : G} (hj : j ∈ J) :
    ∃ d : ℂ, ‖d‖ = 1 ∧ translate hψ j (xi (ψ := ψ)) = d • xi (ψ := ψ) := by
  classical
  obtain ⟨c, hc, hξ⟩ := translate_xi hψ j
  have hmk : (QuotientGroup.mk j : G ⧸ J) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.eq]
    simpa using J.inv_mem hj
  refine ⟨c * phase J ψ 1, by rw [norm_mul, hc, norm_phase hψ, one_mul], ?_⟩
  have hph : phase J ψ 1 ≠ 0 := by
    intro h0
    have := norm_phase hψ (1 : G)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [hξ, hmk, xi, ← lp.single_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hph, mul_one]

include hψ in
/-- `xi` is separating for the commutant of the translations. -/
theorem eq_zero_of_apply_xi (x : L2 J →L[ℂ] L2 J)
    (hx : x ∈ StarSubalgebra.centralizer ℂ (translates hψ)) (h0 : x (xi (ψ := ψ)) = 0) :
    x = 0 := by
  classical
  have hcomm := (mem_centralizer_translates_iff hψ x).mp hx
  have hsingle : ∀ (α : G ⧸ J) (a : ℂ), x (lp.single 2 α a) = 0 := by
    intro α a
    obtain ⟨c, hc, hξ⟩ := translate_xi hψ α.out
    rw [QuotientGroup.out_eq'] at hξ
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact zero_ne_one hc
    have hs : lp.single 2 α a = (a * c⁻¹) • translate hψ α.out (xi (ψ := ψ)) := by
      rw [hξ, ← lp.single_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    rw [hs, map_smul, ← hcomm, h0, map_zero, smul_zero]
  ext1 F
  have hs := (lp.hasSum_single (E := fun _ : G ⧸ J => ℂ) (p := 2) ENNReal.ofNat_ne_top F).mapL x
  simp only [hsingle] at hs
  show x F = 0
  exact hs.unique hasSum_zero

include hψ in
/-- The coordinates of `star x xi` are, up to units, the values of `lift (x xi)` at the
inverse representatives. -/
theorem norm_star_apply_xi_apply (x : L2 J →L[ℂ] L2 J)
    (hx : x ∈ StarSubalgebra.centralizer ℂ (translates hψ)) (α : G ⧸ J) :
    ‖((star x) (xi (ψ := ψ))) α‖ = ‖lift J ψ (x (xi (ψ := ψ))) α.out⁻¹‖ := by
  classical
  have hcomm := (mem_centralizer_translates_iff hψ x).mp hx
  obtain ⟨c, hc, hξ⟩ := translate_xi hψ α.out
  rw [QuotientGroup.out_eq'] at hξ
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc
    exact zero_ne_one hc
  obtain ⟨c', hc', hξ'⟩ := translate_xi hψ α.out⁻¹
  have hcoord : ((star x) (xi (ψ := ψ))) α =
      ⟪lp.single 2 α (1 : ℂ), (star x) (xi (ψ := ψ))⟫_ℂ := by
    rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  have hs : lp.single 2 α (1 : ℂ) = c⁻¹ • translate hψ α.out (xi (ψ := ψ)) := by
    rw [hξ, ← lp.single_smul, smul_eq_mul, inv_mul_cancel₀ hc0]
  have hinner : ⟪translate hψ α.out (x (xi (ψ := ψ))), xi (ψ := ψ)⟫_ℂ =
      ⟪x (xi (ψ := ψ)), translate hψ α.out⁻¹ (xi (ψ := ψ))⟫_ℂ := by
    rw [← LinearIsometryEquiv.inner_map_map (translate hψ α.out) (x (xi (ψ := ψ)))
      (translate hψ α.out⁻¹ (xi (ψ := ψ))), translate_mul_apply, mul_inv_cancel,
      show translate hψ 1 (xi (ψ := ψ)) = xi from translateₗ_one hψ _]
  rw [hcoord, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hs,
    map_smul, ← hcomm, inner_smul_left, hinner, hξ', lp.inner_single_right,
    RCLike.inner_apply', norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj,
    hc', mul_one, norm_inv, hc, inv_one, one_mul, norm_lift hψ]

end Hilbert

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {J : Subgroup G} {ψ : J →* ℂ} (hψ : ∀ j, ‖ψ j‖ = 1)
  (hZJ : Subgroup.center G ≤ J) (hJ : IsOpen (J : Set G))
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

include hψ hZJ hJ in
/-- `xi` is a tracial vector for the commutant of the translations:
`‖x xi‖ = ‖star x xi‖`. -/
theorem norm_apply_xi_eq_norm_star_apply_xi
    (hfin : μ (CentralCoset.centralImage J) ≠ ∞) (x : L2 J →L[ℂ] L2 J)
    (hx : x ∈ StarSubalgebra.centralizer ℂ (translates hψ)) :
    ‖x (xi (ψ := ψ))‖ = ‖(star x) (xi (ψ := ψ))‖ := by
  have hcomm := (mem_centralizer_translates_iff hψ x).mp hx
  let Φ : G → ℝ≥0∞ := fun g => ‖lift J ψ (x (xi (ψ := ψ))) g‖ₑ ^ 2
  have hΦr : ∀ g, ∀ j ∈ J, Φ (g * j) = Φ g := by
    intro g j hj
    simp only [Φ]
    rw [lift_mul J ψ _ g hj, enorm_mul, enorm_eq_one_of_norm_eq_one (hψ _), mul_one]
  have hΦl : ∀ g, ∀ j ∈ J, Φ (j * g) = Φ g := by
    intro g j hj
    obtain ⟨d, hd, hξ⟩ := translate_xi_of_mem hψ (J.inv_mem hj)
    have hF : translate hψ j⁻¹ (x (xi (ψ := ψ))) = d • x (xi (ψ := ψ)) := by
      rw [hcomm, hξ, map_smul]
    have h1 : lift J ψ (x (xi (ψ := ψ))) (j * g) =
        lift J ψ (translate hψ j⁻¹ (x (xi (ψ := ψ)))) g := by
      rw [translate_apply, lift_translateₗ, inv_inv]
    simp only [Φ]
    rw [h1, hF, lp.coeFn_smul, lift_smul, enorm_mul, enorm_eq_one_of_norm_eq_one hd, one_mul]
  have hsum := CentralCoset.tsum_out_eq_tsum_out_inv J hZJ hJ μ hfin Φ hΦr hΦl
  apply norm_eq_of_enorm_sq_eq
  rw [Langlands.Analysis.lp_two_enorm_sq_eq_tsum, Langlands.Analysis.lp_two_enorm_sq_eq_tsum]
  have h1 : ∀ α : G ⧸ J, ‖x (xi (ψ := ψ)) α‖ₑ ^ 2 = Φ α.out := fun α => by
    simp only [Φ, lift_out]
  have h2 : ∀ α : G ⧸ J, ‖((star x) (xi (ψ := ψ))) α‖ₑ ^ 2 = Φ α.out⁻¹ := fun α => by
    simp only [Φ]
    rw [enorm_eq_of_norm_eq (norm_star_apply_xi_apply hψ x hx α)]
  simp_rw [h1, h2]
  exact hsum

end Measure

end Langlands.TwistedCoset
