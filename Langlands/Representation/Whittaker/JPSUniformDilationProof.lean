import Langlands.Representation.Whittaker.JPSUniformDilationStatement
import Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceProof
import Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof
import Langlands.Representation.Smooth.FiniteOperatorExpansionProof
import Langlands.LocalField.SmoothCharacterNormProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Proof of uniform small-coordinate dilation for actual JPS function spaces

From the open norm-one subgroup of uniform coordinate-unit invariance, a basis of
the finite coordinate operator span made of bounded dilations gives the finite
functions and operators, and the published uniform-region recurrence for powers of
the uniformizer gives one threshold for all `|b| ≤ 1`. See the paired Markdown for
the route.
-/

noncomputable section

namespace Langlands.Whittaker

open JPSFunctionSpace LocalFactor.PadicAbelian

universe uF

namespace JPSUniformDilationProof

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

section AbsoluteValue

variable (T : F.TopologicalData)

theorem normalizedAbs_uniformizerUnit_pow_le_one (m : ℕ) :
    T.normalizedAbs ((uniformizerUnit T ^ m : F.Carrierˣ) : F.Carrier) ≤ 1 := by
  have hq : (1 : ℝ) ≤ T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one.le
  rw [← zpow_natCast, uniformizerUnit_zpow_abs]
  exact zpow_le_one_of_nonpos₀ hq (by omega)

theorem normalizedAbs_uniformizerUnit_le_one :
    T.normalizedAbs (uniformizerUnit T : F.Carrier) ≤ 1 := by
  simpa using normalizedAbs_uniformizerUnit_pow_le_one T 1


/-- A bounded unit is a nonnegative power of the uniformizer times a norm-one unit. -/
theorem exists_uniformizerUnit_pow_mul_normOne (b : F.Carrierˣ)
    (hb : T.normalizedAbs (b : F.Carrier) ≤ 1) :
    ∃ (m : ℕ) (w : F.Carrierˣ), T.normalizedAbs (w : F.Carrier) = 1 ∧
      b = uniformizerUnit T ^ m * w := by
  have hq1 : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hq0 : (T.residueCardinality : ℝ) ≠ 0 := (lt_trans zero_lt_one hq1).ne'
  have hk0 : 0 ≤ T.ord (b : F.Carrier) := by
    rw [T.normalizedAbs_of_ne_zero b.ne_zero, zpow_le_one_iff_right₀ hq1] at hb
    omega
  refine ⟨(T.ord (b : F.Carrier)).toNat, b * uniformizerUnit T ^ (-T.ord (b : F.Carrier)),
    ?_, ?_⟩
  · rw [Units.val_mul, T.normalizedAbs_mul, T.normalizedAbs_of_ne_zero b.ne_zero,
      uniformizerUnit_zpow_abs, neg_neg, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]
  · rw [← zpow_natCast, Int.toNat_of_nonneg hk0, mul_left_comm, ← zpow_add,
      add_neg_cancel, zpow_zero, mul_one]

/-- Finitely many translates of an open subgroup cover the norm-one units. -/
theorem exists_finset_unit_cover (U : Subgroup F.Carrierˣ)
    (hUo : letI := T.topology; IsOpen (U : Set F.Carrierˣ)) :
    ∃ R : Finset F.Carrierˣ, ∀ w : F.Carrierˣ, T.normalizedAbs (w : F.Carrier) = 1 →
      ∃ r ∈ R, r⁻¹ * w ∈ U := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨R, hR⟩ := T.isCompact_normalizedAbs_eq_one_units.elim_finite_subcover
    (fun r : F.Carrierˣ => (fun y => r⁻¹ * y) ⁻¹' (U : Set F.Carrierˣ))
    (fun r => hUo.preimage (continuous_const_mul r⁻¹))
    (fun w _ => Set.mem_iUnion.mpr ⟨w, by simp⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, hrw⟩ := Set.mem_iUnion₂.mp (hR hw)
  exact ⟨r, hr, hrw⟩

end AbsoluteValue

open JPSBoundedDilationRecurrenceProof
  (exists_common_threshold smallVanishing mem_smallVanishing_iff smallVanishing_anti
    germMap_eq_zero_of_mem_smallVanishing exists_mem_smallVanishing
    exists_threshold_of_finiteDimensional)

section OperatorBasis

variable {n : ℕ} (W : FunctionSpace F n) (T : F.TopologicalData) (i : Fin n)

/-- The finite operator span is spanned by bounded dilations, so it has a basis of
operators `σ(β k)` with `|β k| ≤ 1`; `η` are the coordinates of `σ(b)` in it. -/
theorem exists_bounded_operator_basis (hS : HasFiniteCoordinateOperatorSpan W T i) :
    ∃ (κ : Type uF) (_ : Fintype κ) (β : κ → F.Carrierˣ) (η : κ → F.Carrierˣ → ℂ),
      (∀ k, T.normalizedAbs (β k : F.Carrier) ≤ 1) ∧
      (∀ b, sigma W T i b = ∑ k, η k b • sigma W T i (β k)) ∧
      Function.Injective η ∧
      (∀ b b', sigma W T i b = sigma W T i b' → ∀ k, η k b = η k b') ∧
      (∀ k b a, η k (b * a) = ∑ l, η l a * η k (b * β l)) := by
  classical
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (sigma W T i))) := hS
  let S := Submodule.span ℂ (Set.range (sigma W T i))
  let τ : F.Carrierˣ → S := fun b => ⟨sigma W T i b, Submodule.subset_span ⟨b, rfl⟩⟩
  have hτ : ∀ b, (τ b : Module.End ℂ (CoordinateGerm W T i)) = sigma W T i b := fun _ => rfl
  let E := Module.End ℂ (CoordinateGerm W T i)
  let Vq : Submodule ℂ E := Submodule.span ℂ
    {x | ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ sigma W T i b = x}
  have hVq : ∀ b, sigma W T i b ∈ Vq := fun b => by
    rw [show Vq = S from boundedSpan_eq_span T (sigma W T i)]
    exact Submodule.subset_span ⟨b, rfl⟩
  let B := {b : F.Carrierˣ // T.normalizedAbs (b : F.Carrier) ≤ 1}
  let τB : B → S := fun b => τ b.1
  let Vp : Submodule ℂ S := Submodule.span ℂ (Set.range τB)
  have hlift : ∀ x ∈ Vq, ∃ y ∈ Vp, (y : E) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨τ b, Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩, rfl⟩
    | zero => exact ⟨0, Vp.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨z', hz', rfl⟩ := hz
      exact ⟨y' + z', Vp.add_mem hy' hz', rfl⟩
    | smul c y _ hy =>
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨c • y', Vp.smul_mem c hy', rfl⟩
  have hall : ∀ b, τ b ∈ Vp := fun b => by
    obtain ⟨y, hy, hye⟩ := hlift _ (hVq b)
    rwa [show y = τ b from Subtype.ext hye] at hy
  have htop : Vp = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact hall b
    | zero => exact Vp.zero_mem
    | add y z _ _ ihy ihz => exact Vp.add_mem ihy ihz
    | smul c y _ ihy => exact Vp.smul_mem c ihy
  obtain ⟨κ, β', -, hspan, hli⟩ := exists_linearIndependent' ℂ τB
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range (τB ∘ β')) := by
    rw [hspan]
    exact htop.ge
  let e : Module.Basis κ ℂ S := Module.Basis.mk hli hsp
  have : Finite κ := Module.Finite.finite_basis e
  let : Fintype κ := Fintype.ofFinite κ
  let β : κ → F.Carrierˣ := fun k => (β' k).1
  let η : κ → F.Carrierˣ → ℂ := fun k b => e.repr (τ b) k
  have he : ∀ k, e k = τ (β k) := fun k => Module.Basis.mk_apply hli hsp k
  have hexp : ∀ b, τ b = ∑ k, η k b • τ (β k) := fun b => by
    conv_lhs => rw [← e.sum_repr (τ b)]
    simp only [he, η]
  have hσexp : ∀ b, sigma W T i b = ∑ k, η k b • sigma W T i (β k) := fun b => by
    have h := congrArg Subtype.val (hexp b)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hτ] using h
  refine ⟨κ, inferInstance, β, η, fun k => (β' k).2, hσexp, ?_, ?_, ?_⟩
  · intro k l hkl
    have h : η k (β l) = η l (β l) := congrFun hkl (β l)
    simp only [η, ← he, Module.Basis.repr_self, Finsupp.single_eq_same] at h
    by_contra hne
    rw [Finsupp.single_eq_of_ne hne] at h
    exact zero_ne_one h
  · intro b b' hbb' k
    show e.repr (τ b) k = e.repr (τ b') k
    rw [show τ b = τ b' from Subtype.ext hbb']
  · intro k b a
    have h1 : τ (b * a) = ∑ l, η l a • τ (b * β l) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, hτ]
      rw [map_mul, hσexp a, Finset.mul_sum]
      simp only [mul_smul_comm, map_mul]
    show e.repr (τ (b * a)) k = ∑ l, e.repr (τ a) l * e.repr (τ (b * β l)) k
    rw [h1, map_sum]
    simp only [η, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]


end OperatorBasis

/-- The uniform dilation expansion for one actual space and coordinate, from the data of
uniform coordinate-unit invariance and of the uniformizer recurrence. -/
theorem uniformDilation_of_unitSubgroup (T : F.TopologicalData) {n : ℕ}
    (W : FunctionSpace F n) (i : Fin n) (hS : HasFiniteCoordinateOperatorSpan W T i)
    (U : Subgroup F.Carrierˣ) (hUo : letI := T.topology; IsOpen (U : Set F.Carrierˣ))
    (hU1 : ∀ u ∈ U, T.normalizedAbs (u : F.Carrier) = 1)
    (hUσ : ∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q)
    (hUf : ∀ f : W.toSubmodule, ∃ ε : ℝ, 0 < ε ∧ ∀ a : Torus F n,
      T.normalizedAbs (a i : F.Carrier) < ε →
      ∀ u ∈ U, (coordinateRepresentation W i u f).val a = f.val a)
    (D : ℕ) (d : ℕ → Fin D → ℂ)
    (hd : ∀ f : W.toSubmodule, ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (a : Torus F n),
      T.normalizedAbs (a i : F.Carrier) < δ →
      (coordinateRepresentation W i (uniformizerUnit T ^ m) f).val a =
        ∑ j : Fin D, d m j *
          (coordinateRepresentation W i (uniformizerUnit T ^ (j : ℕ)) f).val a) :
    letI := T.topology
    ∃ (Y : Finset (F.Carrierˣ → ℂ))
      (A : (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule),
      (∀ η ∈ Y, Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) ∧
      (∀ η ∈ Y, A η ∈ Submodule.span ℂ {B : Module.End ℂ W.toSubmodule |
        ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧
          coordinateRepresentation W i b = B}) ∧
      (∀ (b : F.Carrierˣ) (f : W.toSubmodule),
        sigma W T i b (germMap W T i f) =
          germMap W T i (∑ η ∈ Y, η b • A η f)) ∧
      ∀ f : W.toSubmodule,
        ∃ ε : ℝ, 0 < ε ∧
          ∀ a : Torus F n,
            T.normalizedAbs (a i : F.Carrier) < ε →
            ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
              (coordinateRepresentation W i b f).val a =
                ∑ η ∈ Y, η b * (A η f).val a := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨κ, _, β, η, hβ, hσ, hinj, hfac, htr⟩ := exists_bounded_operator_basis W T i hS
  have hσU : ∀ u ∈ U, sigma W T i u = 1 := fun u hu => LinearMap.ext (hUσ u hu)
  have hηU : ∀ b, ∀ u ∈ U, ∀ k, η k (b * u) = η k b := by
    intro b u hu k
    apply hfac
    rw [map_mul, hσU u hu, mul_one]
  obtain ⟨Y, hY⟩ : ∃ Y : Finset (F.Carrierˣ → ℂ), Y = Finset.univ.image η := ⟨_, rfl⟩
  let A : (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule := fun χ =>
    if h : ∃ k, η k = χ then coordinateRepresentation W i (β h.choose) else 0
  have hA : ∀ k, A (η k) = coordinateRepresentation W i (β k) := by
    intro k
    have h : ∃ l, η l = η k := ⟨k, rfl⟩
    simp only [A, h, dite_true]
    rw [hinj h.choose_spec]
  have hexpand : ∀ b f, ∑ χ ∈ Y, χ b • A χ f =
      ∑ k, η k b • coordinateRepresentation W i (β k) f := by
    intro b f
    rw [hY, Finset.sum_image (fun k _ l _ hkl => hinj hkl)]
    simp only [hA]
  have hexpand' : ∀ b f a, ∑ χ ∈ Y, χ b * (A χ f).val a =
      ∑ k, η k b * (coordinateRepresentation W i (β k) f).val a := by
    intro b f a
    rw [hY, Finset.sum_image (fun k _ l _ hkl => hinj hkl)]
    simp only [hA]
  have hgerm : ∀ b f, germMap W T i (coordinateRepresentation W i b f) =
      germMap W T i (∑ k, η k b • coordinateRepresentation W i (β k) f) := by
    intro b f
    rw [← sigma_apply_mk, hσ b, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, map_smul, sigma_apply_mk]
  -- Clause 1: continuity and finite translates.
  have hclause1 : ∀ χ ∈ Y, Continuous χ ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => χ (b * a))) := by
    intro χ hχ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (hY ▸ hχ)
    refine ⟨?_, ?_⟩
    · apply IsLocallyConstant.continuous
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hopen : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set F.Carrierˣ)) :=
        hUo.preimage (continuous_const_mul x⁻¹)
      have hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set F.Carrierˣ) := by simp
      filter_upwards [hopen.mem_nhds hx] with y hy
      calc η k y = η k (x * (x⁻¹ * y)) := by rw [mul_inv_cancel_left]
        _ = η k x := hηU x _ hy k
    · have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range η)) :=
        FiniteDimensional.span_of_finite ℂ (Set.finite_range η)
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range η))
        (Submodule.span_le.mpr ?_)
      rintro _ ⟨b, rfl⟩
      have h : (fun a => η k (b * a)) = ∑ l, η k (b * β l) • η l := by
        funext a
        rw [htr k b a, Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      show (fun a => η k (b * a)) ∈ _
      rw [h]
      exact sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  -- Clause 2: bounded-span operators.
  have hclause2 : ∀ χ ∈ Y, A χ ∈ Submodule.span ℂ {B : Module.End ℂ W.toSubmodule |
      ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧
        coordinateRepresentation W i b = B} := by
    intro χ hχ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (hY ▸ hχ)
    rw [hA]
    exact Submodule.subset_span ⟨β k, hβ k, rfl⟩
  -- Clause 3: the expansion on the quotient.
  have hclause3 : ∀ (b : F.Carrierˣ) (f : W.toSubmodule),
      sigma W T i b (germMap W T i f) = germMap W T i (∑ χ ∈ Y, χ b • A χ f) := by
    intro b f
    rw [hexpand, sigma_apply_mk, hgerm]
  refine ⟨Y, A, hclause1, hclause2, hclause3, fun f => ?_⟩
  -- Clause 4: one threshold for all bounded dilations.
  obtain ⟨R, hR⟩ := exists_finset_unit_cover T U hUo
  obtain ⟨ε₀, hε₀, hf₀⟩ := hUf f
  obtain ⟨δ₁, hδ₁, hδ₁R⟩ := exists_common_threshold R
    (fun r δ => ∀ (m : ℕ) (a : Torus F n), T.normalizedAbs (a i : F.Carrier) < δ →
      (coordinateRepresentation W i (uniformizerUnit T ^ m)
          (coordinateRepresentation W i r f)).val a =
        ∑ j : Fin D, d m j * (coordinateRepresentation W i (uniformizerUnit T ^ (j : ℕ))
          (coordinateRepresentation W i r f)).val a)
    (fun _ _ _ _ hle h m a ha => h m a (lt_of_lt_of_le ha hle))
    (fun r _ => hd (coordinateRepresentation W i r f))
  let G₁ : R × Fin D → W.toSubmodule := fun x =>
    coordinateRepresentation W i (uniformizerUnit T ^ (x.2 : ℕ))
      (coordinateRepresentation W i (x.1 : F.Carrierˣ) f)
  let G₂ : κ → W.toSubmodule := fun k => coordinateRepresentation W i (β k) f
  let L : Submodule ℂ W.toSubmodule :=
    Submodule.span ℂ (Set.range G₁) ⊔ Submodule.span ℂ (Set.range G₂)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range G₁)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range G₁)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range G₂)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range G₂)
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_sup _ _
  let P : Submodule ℂ W.toSubmodule := L ⊓ (coordinateVanishing W T i).toSubmodule
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨δ₂, hδ₂, hP⟩ := exists_threshold_of_finiteDimensional W T i P
    (fun h hh => (germMap_eq_zero_iff W T i h).mpr (Submodule.mem_inf.mp hh).2)
  refine ⟨min ε₀ (min δ₁ δ₂), lt_min hε₀ (lt_min hδ₁ hδ₂), fun a ha b hb => ?_⟩
  have haε₀ : T.normalizedAbs (a i : F.Carrier) < ε₀ :=
    lt_of_lt_of_le ha (min_le_left _ _)
  have haδ₁ : T.normalizedAbs (a i : F.Carrier) < δ₁ :=
    lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have haδ₂ : T.normalizedAbs (a i : F.Carrier) < δ₂ :=
    lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨m, w, hw, rfl⟩ := exists_uniformizerUnit_pow_mul_normOne T b hb
  obtain ⟨r, hr, hu⟩ := hR w hw
  have hb_eq : uniformizerUnit T ^ m * w = (uniformizerUnit T ^ m * r) * (r⁻¹ * w) := by
    rw [mul_assoc, mul_inv_cancel_left]
  have hb₀ : T.normalizedAbs ((uniformizerUnit T ^ m * r : F.Carrierˣ) : F.Carrier) ≤ 1 := by
    have h1 := hb
    rw [hb_eq, Units.val_mul, T.normalizedAbs_mul, hU1 (r⁻¹ * w) hu, mul_one] at h1
    exact h1
  rw [hexpand', hb_eq]
  have step1 : (coordinateRepresentation W i
      ((uniformizerUnit T ^ m * r) * (r⁻¹ * w)) f).val a =
      (coordinateRepresentation W i (uniformizerUnit T ^ m * r) f).val a := by
    rw [map_mul, Module.End.mul_apply,
      coordinateRepresentation_apply W i (uniformizerUnit T ^ m * r) _ a,
      coordinateRepresentation_apply W i (uniformizerUnit T ^ m * r) f a]
    apply hf₀ _ _ _ hu
    rw [Pi.mul_apply, coordinateEmbedding_same, Units.val_mul, T.normalizedAbs_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (T.normalizedAbs_nonneg _) hb₀) haε₀
  rw [step1]
  simp only [hηU (uniformizerUnit T ^ m * r) _ hu]
  have hrec : ∀ a' : Torus F n, T.normalizedAbs (a' i : F.Carrier) < δ₁ →
      (coordinateRepresentation W i (uniformizerUnit T ^ m * r) f).val a' =
        ∑ j : Fin D, d m j * (G₁ (⟨r, hr⟩, j)).val a' := by
    intro a' ha'
    rw [map_mul, Module.End.mul_apply]
    exact hδ₁R r hr m a' ha'
  let x := coordinateRepresentation W i (uniformizerUnit T ^ m * r) f
  let y := ∑ j : Fin D, d m j • G₁ (⟨r, hr⟩, j)
  let z := ∑ k, η k (uniformizerUnit T ^ m * r) • G₂ k
  have hxy : x - y ∈ smallVanishing W T i δ₁ := by
    rw [mem_smallVanishing_iff]
    intro a' ha'
    simp only [x, y, Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact sub_eq_zero.mpr (hrec a' ha')
  have hxz : germMap W T i (x - z) = 0 := by
    rw [map_sub, hgerm, sub_self]
  have hyz : y - z ∈ P := by
    refine Submodule.mem_inf.mpr ⟨sub_mem ?_ ?_, ?_⟩
    · exact Submodule.mem_sup_left (sum_mem fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · exact Submodule.mem_sup_right (sum_mem fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
    · change VanishesNearCoordinateZero T i (y - z).val
      rw [← germMap_eq_zero_iff, ← sub_sub_sub_cancel_left z y x, map_sub, hxz,
        germMap_eq_zero_of_mem_smallVanishing W T i hδ₁ hxy, sub_zero]
  have hyz2 := (mem_smallVanishing_iff W T i δ₂ (y - z)).mp (hP hyz) a haδ₂
  simp only [y, z, G₂, Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at hyz2
  rw [hrec a haδ₁]
  exact sub_eq_zero.mp hyz2

/-- Uniform coordinate-unit invariance and the uniform-region recurrence for powers of a
bounded coordinate dilation imply uniform small-coordinate dilation. -/
theorem jpsUniformDilation_of_unitInvariance_of_recurrence
    (hU : JPSCoordinateUnitInvarianceStatement.{uF})
    (hrec : JPSBoundedDilationRecurrenceStatement.{uF}) :
    JPSUniformDilationStatement.{uF} := by
  intro p _ F T n W i hloc hS
  obtain ⟨U, hUo, -, hU1, hUσ, hUf⟩ := hU p F T n W i hloc hS
  obtain ⟨D, d, hd⟩ := hrec p F T n W i hS (uniformizerUnit T)
    (normalizedAbs_uniformizerUnit_le_one T)
  exact uniformDilation_of_unitSubgroup T W i hS U hUo hU1 hUσ hUf D d hd

end JPSUniformDilationProof

/-- Uniform small-coordinate dilation for actual JPS function spaces, from the
published proofs of uniform coordinate-unit invariance and of the uniform-region
recurrence for powers of a bounded coordinate dilation. -/
theorem jpsUniformDilation : JPSUniformDilationStatement.{uF} :=
  JPSUniformDilationProof.jpsUniformDilation_of_unitInvariance_of_recurrence
    jpsCoordinateUnitInvariance jpsBoundedDilationRecurrence

end Langlands.Whittaker
