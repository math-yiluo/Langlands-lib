import Langlands.VirtualRepresentation.ScalarKernelGroup
import Langlands.Weil.Representation.CharacterLine
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RepresentationTheory.Coinduced

/-!
# Scalar lifts of induced characters of the normalized image

Let `ρ` be a finite-dimensional complex representation of `S`, and let `A` be a
subgroup of the finite group `normalizedImage ρ` with a character `ψ`. If `ψ`
agrees with the tautological character on the scalar elements of `A`, the scalar
lift of the induced representation `Ind_A ψ` is the induced representation
`Ind_T θ` of `S`, where `T` is the set of `s` with `ρ s ∈ ℂˣ · A` and
`θ s = z ψ(a)` when `ρ s = z • a`. Otherwise the tautological part of `Ind_A ψ`
is zero. When `ρ` is continuous and scalar on an open subgroup, scalar lifts and
the characters `θ` are continuous.
-/

noncomputable section

universe uS uV uY uW

namespace Langlands.VirtualRepresentation.ScalarKernel

variable {S : Type uS} [Group S] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ S V)

section Products

theorem rho_mul_of_eq {s t : S} {c d : ℂˣ} {h k : normalizedImage ρ}
    (hs : ρ s = (c : ℂ) • endOf ρ h) (ht : ρ t = (d : ℂ) • endOf ρ k) :
    ρ (s * t) = ((c * d : ℂˣ) : ℂ) • endOf ρ (h * k) := by
  rw [map_mul, hs, ht, smul_mul_smul_comm, Units.val_mul]
  rfl

theorem rho_inv_of_eq {s : S} {c : ℂˣ} {h : normalizedImage ρ}
    (hs : ρ s = (c : ℂ) • endOf ρ h) :
    ρ s⁻¹ = ((c⁻¹ : ℂˣ) : ℂ) • endOf ρ h⁻¹ := by
  have h1 : ((c⁻¹ : ℂˣ) : ℂ) • endOf ρ h⁻¹ * ρ s = 1 := by
    rw [hs, smul_mul_smul_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    exact Units.inv_mul (h : (Module.End ℂ V)ˣ)
  have h2 : ρ s * ρ s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact (left_inv_eq_right_inv h1 h2).symm

theorem rho_mul_inv_of_eq {s t : S} {c d : ℂˣ} {h k : normalizedImage ρ}
    (hs : ρ s = (c : ℂ) • endOf ρ h) (ht : ρ t = (d : ℂ) • endOf ρ k) :
    ρ (s * t⁻¹) = ((c * d⁻¹ : ℂˣ) : ℂ) • endOf ρ (h * k⁻¹) :=
  rho_mul_of_eq ρ hs (rho_inv_of_eq ρ ht)

theorem endOf_one : endOf ρ 1 = 1 := rfl

variable [Nontrivial V]

theorem scalar_ne_zero_of_endOf {h : normalizedImage ρ} {c : ℂ} (hc : endOf ρ h = c • 1) :
    c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  exact Units.ne_zero (h : (Module.End ℂ V)ˣ) hc

end Products

section Preimage

variable (A : Subgroup (normalizedImage ρ))

/-- The elements `s` of `S` with `ρ s` a nonzero scalar multiple of an element of `A`. -/
def scalarPreimage : Subgroup S where
  carrier := {s | ∃ a ∈ A, ∃ z : ℂˣ, ρ s = (z : ℂ) • endOf ρ a}
  one_mem' := ⟨1, A.one_mem, 1, by rw [map_one, Units.val_one, one_smul]; rfl⟩
  mul_mem' := by
    rintro s t ⟨a, ha, z, hz⟩ ⟨b, hb, w, hw⟩
    exact ⟨a * b, A.mul_mem ha hb, z * w, rho_mul_of_eq ρ hz hw⟩
  inv_mem' := by
    rintro s ⟨a, ha, z, hz⟩
    exact ⟨a⁻¹, A.inv_mem ha, z⁻¹, rho_inv_of_eq ρ hz⟩

theorem mem_scalarPreimage {s : S} {a : normalizedImage ρ} (ha : a ∈ A) {z : ℂˣ}
    (hz : ρ s = (z : ℂ) • endOf ρ a) : s ∈ scalarPreimage ρ A :=
  ⟨a, ha, z, hz⟩

/-- A subgroup on which `ρ` is scalar lies in every `scalarPreimage`. -/
theorem le_scalarPreimage [Nontrivial V] {N : Subgroup S} (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1) :
    N ≤ scalarPreimage ρ A := by
  intro n hn
  obtain ⟨c, hc⟩ := hN n hn
  have hc0 : c ≠ 0 := scalar_ne_zero ρ hc
  exact ⟨1, A.one_mem, Units.mk0 c hc0, by rw [hc, Units.val_mk0]; rfl⟩

/-- `ψ` agrees with the tautological character on the scalar elements of `A`. -/
def IsTautOn (ψ : A →* ℂˣ) : Prop :=
  ∀ (a : A) (c : ℂ), endOf ρ (a : normalizedImage ρ) = c • 1 → (ψ a : ℂ) = c

variable {A} {ψ : A →* ℂˣ}

theorem theta_eq_aux (hψ : IsTautOn ρ A ψ) {a a' : normalizedImage ρ} (ha : a ∈ A)
    (ha' : a' ∈ A) {z z' : ℂˣ} (he : (z : ℂ) • endOf ρ a = (z' : ℂ) • endOf ρ a') :
    z * ψ ⟨a, ha⟩ = z' * ψ ⟨a', ha'⟩ := by
  have hk := scalar_of_smul_eq ρ he
  have h1 := hψ ⟨a * a'⁻¹, A.mul_mem ha (A.inv_mem ha')⟩ _ hk
  have h2 : (⟨a * a'⁻¹, A.mul_mem ha (A.inv_mem ha')⟩ : A) =
      ⟨a, ha⟩ * (⟨a', ha'⟩ : A)⁻¹ := rfl
  rw [h2, map_mul, map_inv, Units.val_mul, Units.val_div_eq_div_val] at h1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hψ0 : ((ψ ⟨a', ha'⟩ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hz0 : (z : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : ((ψ ⟨a, ha⟩ : ℂˣ) : ℂ) = (z' : ℂ) / z * ψ ⟨a', ha'⟩ := by
    rw [← h1, Units.val_inv_eq_inv_val, mul_assoc, inv_mul_cancel₀ hψ0, mul_one]
  rw [h3]
  field_simp

/-- The character `θ s = z ψ(a)` when `ρ s = z • a`, before bundling. -/
def scalarCharacterFun (t : scalarPreimage ρ A) : ℂˣ :=
  (t.2.choose_spec.2.choose : ℂˣ) * ψ ⟨t.2.choose, t.2.choose_spec.1⟩

theorem scalarCharacterFun_spec (hψ : IsTautOn ρ A ψ) (t : scalarPreimage ρ A)
    {a : normalizedImage ρ} (ha : a ∈ A) {z : ℂˣ} (hz : ρ t = (z : ℂ) • endOf ρ a) :
    scalarCharacterFun ρ (ψ := ψ) t = z * ψ ⟨a, ha⟩ :=
  theta_eq_aux ρ hψ _ ha (t.2.choose_spec.2.choose_spec.symm.trans hz)

/-- The character `θ` of `scalarPreimage ρ A`. -/
def scalarCharacter (hψ : IsTautOn ρ A ψ) : scalarPreimage ρ A →* ℂˣ where
  toFun := scalarCharacterFun ρ
  map_one' := by
    rw [scalarCharacterFun_spec ρ hψ 1 A.one_mem (z := 1)
      (by rw [OneMemClass.coe_one, map_one, Units.val_one, one_smul]; rfl)]
    rw [one_mul]
    exact map_one ψ
  map_mul' s t := by
    obtain ⟨a, ha, z, hz⟩ := s.2
    obtain ⟨b, hb, w, hw⟩ := t.2
    rw [scalarCharacterFun_spec ρ hψ s ha hz, scalarCharacterFun_spec ρ hψ t hb hw,
      scalarCharacterFun_spec ρ hψ (s * t) (A.mul_mem ha hb) (rho_mul_of_eq ρ hz hw)]
    have : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    rw [mul_mul_mul_comm]

theorem scalarCharacter_spec (hψ : IsTautOn ρ A ψ) (t : scalarPreimage ρ A)
    {a : normalizedImage ρ} (ha : a ∈ A) {z : ℂˣ} (hz : ρ t = (z : ℂ) • endOf ρ a) :
    scalarCharacter ρ hψ t = z * ψ ⟨a, ha⟩ :=
  scalarCharacterFun_spec ρ hψ t ha hz

end Preimage

section InducedEquivalence

variable [Nontrivial V] [FiniteDimensional ℂ V] {A : Subgroup (normalizedImage ρ)}
  {ψ : A →* ℂˣ} (χ : Representation ℂ A ℂ) (hχ : ∀ a x, χ a x = (ψ a : ℂ) * x)

omit [Nontrivial V] [FiniteDimensional ℂ V] in
include hχ in
theorem coindV_apply_mul (y : Representation.coindV A.subtype χ) (a : A)
    (x : normalizedImage ρ) : y.1 ((a : normalizedImage ρ) * x) = (ψ a : ℂ) * y.1 x := by
  rw [← hχ]
  exact y.2 a x

omit [Nontrivial V] [FiniteDimensional ℂ V] in
/-- Evaluation form of `tautPart_key` for induced functions. -/
theorem taut_coind_eval {y : Representation.coindV A.subtype χ}
    (hy : y ∈ tautPart ρ (Representation.coind A.subtype χ)) {h₁ h₂ : normalizedImage ρ}
    {c₁ c₂ : ℂˣ} (he : (c₁ : ℂ) • endOf ρ h₁ = (c₂ : ℂ) • endOf ρ h₂) :
    (c₁ : ℂ) * y.1 h₁ = (c₂ : ℂ) * y.1 h₂ := by
  have h := congrArg (fun f : Representation.coindV A.subtype χ => f.1 1)
    (tautPart_key ρ _ hy he)
  change (c₁ : ℂ) * y.1 (1 * h₁) = (c₂ : ℂ) * y.1 (1 * h₂) at h
  simpa only [one_mul] using h

omit [Nontrivial V] [FiniteDimensional ℂ V] in
include hχ in
/-- Outside the tautological case the tautological part of `Ind_A ψ` is zero. -/
theorem tautPart_coind_eq_bot (h : ¬ IsTautOn ρ A ψ) :
    tautPart ρ (Representation.coind A.subtype χ) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  simp only [IsTautOn, not_forall] at h
  obtain ⟨a, c, hc, hne⟩ := h
  rw [Submodule.mem_bot]
  apply Subtype.ext
  funext x
  have h1 : y.1 (x * a) = c * y.1 x :=
    congrArg (fun f : Representation.coindV A.subtype χ => f.1 x) (hy _ c hc)
  have h2 := coindV_apply_mul ρ χ hχ y a x
  rw [← commute_of_scalar ρ hc x] at h1
  rw [h1] at h2
  have h3 : ((ψ a : ℂ) - c) * y.1 x = 0 := by rw [sub_mul, ← h2, sub_self]
  change y.1 x = 0
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)

variable (hψ : IsTautOn ρ A ψ)

/-- The coinduced character line `Ind_T θ` of `S`. -/
abbrev coindCharacter :=
  Representation.coind (scalarPreimage ρ A).subtype
    (FiniteRepresentation.characterLine.{uS, uW} (scalarCharacter ρ hψ)).representation

omit [Nontrivial V] [FiniteDimensional ℂ V] in
theorem coindCharacter_eval
    (F : Representation.coindV (scalarPreimage ρ A).subtype
      (FiniteRepresentation.characterLine.{uS, uW} (scalarCharacter ρ hψ)).representation)
    {s₁ s₂ : S} {a : normalizedImage ρ} (ha : a ∈ A) {w : ℂˣ}
    (he : ρ (s₁ * s₂⁻¹) = (w : ℂ) • endOf ρ a) :
    (F.1 s₁).down = (w : ℂ) * ψ ⟨a, ha⟩ * (F.1 s₂).down := by
  let t : scalarPreimage ρ A := ⟨s₁ * s₂⁻¹, mem_scalarPreimage ρ A ha he⟩
  have h := F.2 t s₂
  change F.1 (s₁ * s₂⁻¹ * s₂) = _ at h
  rw [inv_mul_cancel_right] at h
  have h2 : (F.1 s₁).down = (scalarCharacter ρ hψ t : ℂ) * (F.1 s₂).down := by
    rw [h]
    rfl
  rw [h2, scalarCharacter_spec ρ hψ t ha he, Units.val_mul]

include hχ in
/-- The induced character line, as functions on the normalized image. -/
def toCoindFun
    (F : Representation.coindV (scalarPreimage ρ A).subtype
      (FiniteRepresentation.characterLine.{uS, uW} (scalarCharacter ρ hψ)).representation) :
    tautPart ρ (Representation.coind A.subtype χ) :=
  ⟨⟨fun h => ((preScalar ρ h)⁻¹ : ℂˣ) * (F.1 (preElem ρ h)).down, by
    intro a x
    change ((preScalar ρ ((a : normalizedImage ρ) * x))⁻¹ : ℂˣ) *
        (F.1 (preElem ρ ((a : normalizedImage ρ) * x))).down =
      χ a (((preScalar ρ x)⁻¹ : ℂˣ) * (F.1 (preElem ρ x)).down)
    rw [hχ]
    have hr := rho_mul_inv_of_eq ρ (pre_spec ρ ((a : normalizedImage ρ) * x)) (pre_spec ρ x)
    rw [mul_inv_cancel_right] at hr
    rw [coindCharacter_eval ρ hψ F a.2 hr]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have h0 : ((preScalar ρ ((a : normalizedImage ρ) * x) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp⟩, by
    intro h c hc
    apply Subtype.ext
    funext x
    change ((preScalar ρ (x * h))⁻¹ : ℂˣ) * (F.1 (preElem ρ (x * h))).down =
      c * (((preScalar ρ x)⁻¹ : ℂˣ) * (F.1 (preElem ρ x)).down)
    have hc0 := scalar_ne_zero_of_endOf ρ hc
    have hr := rho_mul_inv_of_eq ρ (pre_spec ρ (x * h)) (pre_spec ρ x)
    have hxh : x * h * x⁻¹ = h := by rw [← commute_of_scalar ρ hc x, mul_inv_cancel_right]
    rw [hxh, hc] at hr
    have hr' : ρ (preElem ρ (x * h) * (preElem ρ x)⁻¹) =
        ((preScalar ρ (x * h) * (preScalar ρ x)⁻¹ * Units.mk0 c hc0 : ℂˣ) : ℂ) •
          endOf ρ 1 := by
      rw [hr, endOf_one, Units.val_mul _ (Units.mk0 c hc0), Units.val_mk0, mul_smul]
    rw [coindCharacter_eval ρ hψ F A.one_mem hr']
    have h1 : ψ ⟨1, A.one_mem⟩ = 1 := map_one ψ
    rw [h1]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
    have h0 : ((preScalar ρ (x * h) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp⟩

include hχ in
/-- Functions on the normalized image, as an induced character line of `S`. -/
def toCoindCharacter (y : tautPart ρ (Representation.coind A.subtype χ)) :
    Representation.coindV (scalarPreimage ρ A).subtype
      (FiniteRepresentation.characterLine.{uS, uW} (scalarCharacter ρ hψ)).representation :=
  ⟨fun s => ULift.up ((liftScalar ρ s : ℂ) * (y : Representation.coindV A.subtype χ).1
      (liftElem ρ s)), by
    intro t s
    obtain ⟨a, ha, w, hw⟩ := t.2
    apply ULift.ext
    change _ = (scalarCharacter ρ hψ t : ℂ) * ((liftScalar ρ s : ℂ) *
      (y : Representation.coindV A.subtype χ).1 (liftElem ρ s))
    rw [scalarCharacter_spec ρ hψ t ha hw]
    change (liftScalar ρ ((t : S) * s) : ℂ) *
        (y : Representation.coindV A.subtype χ).1 (liftElem ρ ((t : S) * s)) = _
    have hts := rho_mul_of_eq ρ hw (lift_spec ρ s)
    rw [lift_spec ρ ((t : S) * s)] at hts
    rw [taut_coind_eval ρ χ y.2 hts, Units.val_mul]
    have := coindV_apply_mul ρ χ hχ (y : Representation.coindV A.subtype χ) ⟨a, ha⟩
      (liftElem ρ s)
    change (y : Representation.coindV A.subtype χ).1 (a * liftElem ρ s) = _ at this
    rw [this, Units.val_mul]
    ring⟩

include hχ in
/-- The scalar lift of `Ind_A ψ` is `Ind_T θ`, in the tautological case. -/
def coindScalarLiftEquiv :
    Representation.Equiv (scalarLift ρ (Representation.coind A.subtype χ))
      (coindCharacter.{uS, uV, uW} ρ hψ) :=
  Representation.Equiv.mk
    { toFun := toCoindCharacter ρ χ hχ hψ
      invFun := toCoindFun ρ χ hχ hψ
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change ((preScalar ρ x)⁻¹ : ℂˣ) * ((liftScalar ρ (preElem ρ x) : ℂ) *
            (y : Representation.coindV A.subtype χ).1 (liftElem ρ (preElem ρ x))) =
          (y : Representation.coindV A.subtype χ).1 x
        have he := (lift_spec ρ (preElem ρ x)).symm.trans (pre_spec ρ x)
        rw [taut_coind_eval ρ χ y.2 he, ← mul_assoc, Units.val_inv_eq_inv_val,
          inv_mul_cancel₀ (Units.ne_zero _), one_mul]
      right_inv := by
        intro F
        apply Subtype.ext
        funext s
        apply ULift.ext
        change (liftScalar ρ s : ℂ) * (((preScalar ρ (liftElem ρ s))⁻¹ : ℂˣ) *
            (F.1 (preElem ρ (liftElem ρ s))).down) = (F.1 s).down
        have hr := rho_mul_inv_of_eq ρ (lift_spec ρ s) (pre_spec ρ (liftElem ρ s))
        rw [mul_inv_cancel] at hr
        rw [coindCharacter_eval ρ hψ F A.one_mem hr]
        have h1 : ψ ⟨1, A.one_mem⟩ = 1 := map_one ψ
        rw [h1]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
        have h0 : ((preScalar ρ (liftElem ρ s) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      map_add' := by
        intro y y'
        apply Subtype.ext
        funext s
        apply ULift.ext
        change (liftScalar ρ s : ℂ) * ((y : Representation.coindV A.subtype χ).1
            (liftElem ρ s) + (y' : Representation.coindV A.subtype χ).1 (liftElem ρ s)) =
          (liftScalar ρ s : ℂ) * (y : Representation.coindV A.subtype χ).1 (liftElem ρ s) +
            (liftScalar ρ s : ℂ) * (y' : Representation.coindV A.subtype χ).1 (liftElem ρ s)
        ring
      map_smul' := by
        intro r y
        apply Subtype.ext
        funext s
        apply ULift.ext
        change (liftScalar ρ s : ℂ) * (r * (y : Representation.coindV A.subtype χ).1
            (liftElem ρ s)) =
          r * ((liftScalar ρ s : ℂ) * (y : Representation.coindV A.subtype χ).1 (liftElem ρ s))
        ring }
    (by
      intro s'
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      funext s
      apply ULift.ext
      change (liftScalar ρ s : ℂ) *
          ((scalarLift ρ (Representation.coind A.subtype χ) s' y :
            tautPart ρ (Representation.coind A.subtype χ)) :
              Representation.coindV A.subtype χ).1 (liftElem ρ s) =
        (liftScalar ρ (s * s') : ℂ) *
          (y : Representation.coindV A.subtype χ).1 (liftElem ρ (s * s'))
      rw [scalarLift_of_eq ρ _ (lift_spec ρ s')]
      change (liftScalar ρ s : ℂ) * ((liftScalar ρ s' : ℂ) *
          (y : Representation.coindV A.subtype χ).1 (liftElem ρ s * liftElem ρ s')) = _
      have hss := rho_mul_of_eq ρ (lift_spec ρ s) (lift_spec ρ s')
      rw [lift_spec ρ (s * s')] at hss
      rw [taut_coind_eval ρ χ y.2 hss, Units.val_mul, mul_assoc])

end InducedEquivalence

section Topology

variable [TopologicalSpace S] [IsTopologicalGroup S] [Nontrivial V] [FiniteDimensional ℂ V]

/-- The normalized trace, which recovers `c` from `c • 1`. -/
def scalarTrace : Module.End ℂ V →ₗ[ℂ] ℂ :=
  ((Module.finrank ℂ V : ℂ)⁻¹) • LinearMap.trace ℂ V

omit [Nontrivial V] in
theorem scalarTrace_smul_one [Nontrivial V] (c : ℂ) : scalarTrace (V := V) (c • 1) = c := by
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [scalarTrace, LinearMap.smul_apply, map_smul, LinearMap.trace_one, smul_eq_mul]
  field_simp

omit [IsTopologicalGroup S] [Nontrivial V] in
theorem continuous_scalarTrace_comp (hρ : (FiniteRepresentation.of ρ).IsContinuous) :
    Continuous (fun s => scalarTrace (ρ s)) := by
  let _ : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  have : IsModuleTopology ℂ (Module.End ℂ V) := ⟨rfl⟩
  have hρ' : Continuous ρ := hρ
  exact (IsModuleTopology.continuous_of_linearMap scalarTrace).comp hρ'

/-- A scalar lift is continuous when `ρ` is continuous and scalar on an open subgroup. -/
theorem isContinuous_scalarLift {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] (σ : Representation ℂ (normalizedImage ρ) Y)
    (hρ : (FiniteRepresentation.of ρ).IsContinuous) {N : Subgroup S}
    (hNo : IsOpen (N : Set S)) (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1) :
    (FiniteRepresentation.of (scalarLift ρ σ)).IsContinuous := by
  let _ : TopologicalSpace (Module.End ℂ (tautPart ρ σ)) :=
    moduleTopology ℂ (Module.End ℂ (tautPart ρ σ))
  have : IsModuleTopology ℂ (Module.End ℂ (tautPart ρ σ)) := ⟨rfl⟩
  have : IsTopologicalRing (Module.End ℂ (tautPart ρ σ)) :=
    IsModuleTopology.isTopologicalRing ℂ (Module.End ℂ (tautPart ρ σ))
  have : ContinuousSMul ℂ (Module.End ℂ (tautPart ρ σ)) :=
    IsModuleTopology.toContinuousSMul ℂ (Module.End ℂ (tautPart ρ σ))
  let f : S → Module.End ℂ (tautPart ρ σ) := fun s => scalarTrace (ρ s) • 1
  have hf : Continuous f := (continuous_scalarTrace_comp ρ hρ).smul continuous_const
  have heq : ∀ n ∈ N, f n = scalarLift ρ σ n := by
    intro n hn
    obtain ⟨c, hc⟩ := hN n hn
    have hc0 := scalar_ne_zero ρ hc
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [scalarLift_of_eq ρ σ (c := Units.mk0 c hc0) (h := 1)
      (by rw [hc, Units.val_mk0, endOf_one])]
    simp only [f, hc, scalarTrace_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      map_one, Units.val_mk0]
    rfl
  change Continuous (scalarLift ρ σ)
  exact continuous_of_continuousAt_one (scalarLift ρ σ)
    (hf.continuousAt.congr (Filter.eventually_of_mem (hNo.mem_nhds N.one_mem) heq))

/-- The character `θ` is continuous when `ρ` is continuous and scalar on an open
subgroup. -/
theorem continuous_scalarCharacter {A : Subgroup (normalizedImage ρ)} {ψ : A →* ℂˣ}
    (hψ : IsTautOn ρ A ψ) (hρ : (FiniteRepresentation.of ρ).IsContinuous) {N : Subgroup S}
    (hNo : IsOpen (N : Set S)) (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1) :
    Continuous (scalarCharacter ρ hψ) := by
  let θ' : scalarPreimage ρ A →* ℂ := (Units.coeHom ℂ).comp (scalarCharacter ρ hψ)
  have hθ' : Continuous θ' := by
    refine continuous_of_continuousAt_one θ' ?_
    have hf : Continuous (fun t : scalarPreimage ρ A => scalarTrace (ρ t)) :=
      (continuous_scalarTrace_comp ρ hρ).comp continuous_subtype_val
    have hNT : IsOpen ((N.subgroupOf (scalarPreimage ρ A) : Set (scalarPreimage ρ A))) :=
      hNo.preimage continuous_subtype_val
    refine hf.continuousAt.congr (Filter.eventually_of_mem (hNT.mem_nhds (Subgroup.one_mem _)) ?_)
    intro t ht
    obtain ⟨c, hc⟩ := hN t (Subgroup.mem_subgroupOf.mp ht)
    have hc0 := scalar_ne_zero ρ hc
    change scalarTrace (ρ t) = ((scalarCharacter ρ hψ t : ℂˣ) : ℂ)
    rw [scalarCharacter_spec ρ hψ t A.one_mem (z := Units.mk0 c hc0)
      (by rw [hc, Units.val_mk0, endOf_one]), hc, scalarTrace_smul_one]
    have h1 : ψ ⟨1, A.one_mem⟩ = 1 := map_one ψ
    rw [h1, mul_one, Units.val_mk0]
  refine Units.continuous_iff.mpr ⟨hθ', ?_⟩
  have h : (fun t => (((scalarCharacter ρ hψ t)⁻¹ : ℂˣ) : ℂ)) = θ' ∘ (fun t => t⁻¹) := by
    funext t
    simp [θ', map_inv]
  rw [h]
  exact hθ'.comp continuous_inv

/-- The character `θ` as a continuous homomorphism. -/
def continuousScalarCharacter {A : Subgroup (normalizedImage ρ)} {ψ : A →* ℂˣ}
    (hψ : IsTautOn ρ A ψ) (hρ : (FiniteRepresentation.of ρ).IsContinuous) {N : Subgroup S}
    (hNo : IsOpen (N : Set S)) (hN : ∀ n ∈ N, ∃ c : ℂ, ρ n = c • 1) :
    scalarPreimage ρ A →ₜ* ℂˣ :=
  ⟨scalarCharacter ρ hψ, continuous_scalarCharacter ρ hψ hρ hNo hN⟩

end Topology

end Langlands.VirtualRepresentation.ScalarKernel
