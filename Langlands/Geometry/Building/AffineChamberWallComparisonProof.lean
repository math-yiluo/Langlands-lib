import Langlands.Geometry.Building.AffineChamberWallComparisonStatement
import Langlands.Geometry.Building.AffineChamberSeparation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-! # Proof of the chamber-simple and separating wall reflection comparison -/

noncomputable section

universe uV uA

open Filter Topology

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-! ### Real sign arithmetic -/

/-- Equal signs of a nonzero number and another number give a positive product. -/
theorem mul_pos_of_sign_eq {a b : ℝ} (ha : a ≠ 0)
    (h : SignType.sign a = SignType.sign b) : 0 < a * b := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [sign_neg ha, eq_comm, sign_eq_neg_one_iff] at h
    exact mul_pos_of_neg_of_neg ha h
  · rw [sign_pos ha, eq_comm, sign_eq_one_iff] at h
    exact mul_pos ha h

/-- A positive product gives equal signs. -/
theorem sign_eq_of_mul_pos {a b : ℝ} (h : 0 < a * b) :
    SignType.sign a = SignType.sign b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [sign_pos ha, sign_pos hb]
  · rw [sign_neg ha, sign_neg hb]

/-- A perturbation smaller than the absolute value keeps the sign. -/
theorem sign_add_eq_of_abs_lt {a b : ℝ} (h : |b| < |a|) :
    SignType.sign (a + b) = SignType.sign a := by
  apply sign_eq_of_mul_pos
  have hpos : 0 < |a| * (|a| - |b|) :=
    mul_pos (lt_of_le_of_lt (abs_nonneg b) h) (sub_pos.2 h)
  nlinarith [abs_mul_abs_self a, neg_abs_le (a * b), abs_mul a b]

/-! ### Affine functionals, coroots and reflections -/

/-- Evaluation of an affine functional after a translation. -/
theorem apply_smul_vadd (η : A →ᵃ[ℝ] ℝ) (c : ℝ) (v : V) (x : A) :
    η (c • v +ᵥ x) = c * η.linear v + η x := by
  rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]

/-- Scaling a root by `c ≠ 0` scales its coroot by `c⁻¹`. -/
theorem IsCoroot.smul {ψ : A →ᵃ[ℝ] ℝ} {v : V} (hv : IsCoroot Ψ ψ v) {c : ℝ}
    (hc : c ≠ 0) : IsCoroot Ψ (c • ψ) (c⁻¹ • v) := by
  refine ⟨?_, fun η hη => ?_⟩
  · rw [AffineMap.smul_linear, LinearMap.smul_apply, map_smul, hv.1, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · have h : (η.linear (c⁻¹ • v)) • (c • ψ) = η.linear v • ψ := by
      rw [map_smul, smul_eq_mul, smul_smul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc,
        one_mul]
    rw [h]
    exact hv.2 η hη

/-- A root hyperplane is unchanged by a nonzero scalar. -/
theorem hyperplane_smul (ψ : A →ᵃ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0) :
    hyperplane (c • ψ) = hyperplane ψ :=
  SetLike.ext fun z => by
    rw [mem_hyperplane, mem_hyperplane, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_eq_zero, or_iff_right hc]

/-- The reflection of a rescaled root with the rescaled coroot is the same reflection. -/
theorem affineReflection_smul (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2) {c : ℝ}
    (hc : c ≠ 0) (hcv : (c • ψ).linear (c⁻¹ • v) = 2) :
    affineReflection (c • ψ) hcv = affineReflection ψ hv := by
  ext z
  rw [affineReflection_apply, affineReflection_apply, AffineMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, smul_smul]
  congr 2
  field_simp

/-- In an affine root system, a root that is a nonzero multiple of another root has the same
reflection: the coroots are related by the inverse scalar (coroot uniqueness). -/
theorem affineReflection_eq_of_eq_smul (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ η : A →ᵃ[ℝ] ℝ} {v w : V} (hv : IsCoroot Ψ ψ v) (hw : IsCoroot Ψ η w)
    {c : ℝ} (hc : c ≠ 0) (hη : η = c • ψ) :
    affineReflection η hw.1 = affineReflection ψ hv.1 := by
  subst hη
  have hwv : w = c⁻¹ • v := hΨ.isCoroot_unique hw (hv.smul hc)
  subst hwv
  exact affineReflection_smul ψ hv.1 hc hw.1

/-- A functional vanishing on the hyperplane of a root with a coroot is a multiple of it. -/
theorem eq_smul_of_hyperplane_le {ψ η : A →ᵃ[ℝ] ℝ} {v : V} (hv : ψ.linear v = 2)
    (h : hyperplane ψ ≤ hyperplane η) : η = (η.linear v / 2) • ψ := by
  have hψ0 : ψ.linear ≠ 0 := by
    intro h0
    rw [h0, LinearMap.zero_apply] at hv
    norm_num at hv
  obtain ⟨p, hp⟩ := exists_apply_eq_zero hψ0
  have hηp : η p = 0 := h hp
  have hlin : ∀ u : V, η.linear u = (η.linear v / 2) * ψ.linear u := by
    intro u
    have hu0 : ψ ((u - (ψ.linear u / 2) • v) +ᵥ p) = 0 := by
      rw [AffineMap.map_vadd, hp, vadd_eq_add, add_zero, map_sub, map_smul, hv,
        smul_eq_mul]
      ring
    have hη0 : η ((u - (ψ.linear u / 2) • v) +ᵥ p) = 0 := h hu0
    rw [AffineMap.map_vadd, hηp, vadd_eq_add, add_zero, map_sub, map_smul,
      smul_eq_mul] at hη0
    linarith
  ext z
  have hz := η.linearMap_vsub z p
  have hz' := ψ.linearMap_vsub z p
  rw [hlin, hz', vsub_eq_sub, vsub_eq_sub, hηp, hp, sub_zero, sub_zero] at hz
  rw [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, hz]

/-- Equal reflections have the same fixed hyperplane. -/
theorem hyperplane_le_of_affineReflection_eq {ψ η : A →ᵃ[ℝ] ℝ} {v w : V}
    (hv : ψ.linear v = 2) (hw : η.linear w = 2)
    (h : affineReflection η hw = affineReflection ψ hv) :
    hyperplane ψ ≤ hyperplane η := by
  intro p hp
  have h1 : affineReflection η hw p = p := by
    rw [h]
    exact affineReflection_apply_of_mem ψ hv hp
  have h2 := apply_affineReflection η hw p
  rw [h1] at h2
  change η p = 0
  linarith

/-! ### The two inclusions -/

/-- A chamber-simple reflection is the unique reflection separating the chamber point from its
image. -/
theorem chamberSimple_mem_wallReflections (hΨ : IsAffineRootSystemWithRankZero Ψ) {x : A}
    {s : affineWeylGroup Ψ} (hs : s ∈ chamberSimpleReflections Ψ (facet Ψ x)) :
    (s : A ≃ᵃ[ℝ] A) ∈ wallReflections Ψ x := by
  obtain ⟨ψ, ⟨⟨hψΨ, hpos⟩, _, _, _, Fa, ⟨⟨y, rfl⟩, x', hx', hFa⟩, hspan⟩, v, hv, hsv⟩ := hs
  have hψx : 0 < ψ x := hpos x (mem_facet_self Ψ x)
  rw [hsv]
  refine ⟨⟨ψ, hψΨ, v, hv, rfl, ?_⟩, ?_⟩
  · rw [apply_affineReflection]
    nlinarith
  · rintro t ⟨η, hηΨ, w, hw, rfl, hsep⟩
    have hyH : y ∈ hyperplane ψ := hspan ▸ subset_affineSpan ℝ _ (mem_facet_self Ψ y)
    have hcl : y ∈ facetClosure Ψ x := by
      rw [← facetClosure_eq_of_facetRel (facet_eq_facet_iff.1 hx')]
      exact hFa (mem_facet_self Ψ y)
    by_cases hηy : η y = 0
    · have hle : hyperplane ψ ≤ hyperplane η := by
        rw [← hspan]
        exact affineSpan_le.2 (facet_subset_hyperplane ⟨hηΨ, hηy⟩)
      have heq := eq_smul_of_hyperplane_le hv.1 hle
      have hc : η.linear v / 2 ≠ 0 := by
        intro hc0
        have h2 := hw.1
        rw [heq, hc0, zero_smul, AffineMap.zero_linear, LinearMap.zero_apply] at h2
        norm_num at h2
      exact affineReflection_eq_of_eq_smul hΨ hv hw hc heq
    · exfalso
      have h1 : SignType.sign (η y) = SignType.sign (η x) :=
        (hcl η hηΨ).resolve_left (sign_ne_zero.2 hηy)
      have hη' : η.comp (affineReflection ψ hv.1 : A →ᵃ[ℝ] A) ∈ Ψ := by
        rw [comp_affineReflection]
        exact hv.2 η hηΨ
      have hry : affineReflection ψ hv.1 y = y := affineReflection_apply_of_mem ψ hv.1 hyH
      have hcomp : ∀ z, (η.comp (affineReflection ψ hv.1 : A →ᵃ[ℝ] A)) z =
          η (affineReflection ψ hv.1 z) := fun _ => rfl
      have h2 : SignType.sign (η y) = SignType.sign (η (affineReflection ψ hv.1 x)) := by
        have h3 := hcl _ hη'
        rw [hcomp, hcomp, hry] at h3
        exact h3.resolve_left (sign_ne_zero.2 hηy)
      have p1 := mul_pos_of_sign_eq hηy h1
      have p2 := mul_pos_of_sign_eq hηy h2
      nlinarith [mul_pos p1 p2, mul_nonneg (sq_nonneg (η y)) (le_of_lt (neg_pos.2 hsep))]

/-- A unique separating reflection is the image of a chamber-simple reflection. -/
theorem exists_chamberSimple_of_mem_wallReflections (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {x : A} (hx : ∀ ψ ∈ Ψ, ψ x ≠ 0) {s : A ≃ᵃ[ℝ] A} (hs : s ∈ wallReflections Ψ x) :
    s ∈ (affineWeylGroup Ψ).subtype '' chamberSimpleReflections Ψ (facet Ψ x) := by
  obtain ⟨⟨ψ, hψΨ, v, hv, rfl, -⟩, huniq⟩ := hs
  -- The midpoint of `x` and its reflection.
  set m : A := (-(ψ x) / 2) • v +ᵥ x with hm
  have hψm : ψ m = 0 := by
    rw [hm, apply_smul_vadd, hv.1]
    ring
  have hrx : ∀ η : A →ᵃ[ℝ] ℝ, η (affineReflection ψ hv.1 x) = 2 * η m - η x := by
    intro η
    rw [affineReflection_apply, hm, apply_smul_vadd, apply_smul_vadd]
    ring
  clear_value m
  -- A root not of the same strict sign at `m` and `x` separates `x` from its reflection.
  have hkey : ∀ η ∈ Ψ, η m * η x ≤ 0 → hyperplane ψ ≤ hyperplane η := by
    intro η hηΨ hle
    obtain ⟨w, hw⟩ := hΨ.exists_isCoroot η hηΨ
    have hsep : reflectionSeparates Ψ (affineReflection η hw.1) x
        (affineReflection ψ hv.1 x) := by
      refine ⟨η, hηΨ, w, hw, rfl, ?_⟩
      rw [hrx]
      nlinarith [mul_self_pos.2 (hx η hηΨ)]
    exact hyperplane_le_of_affineReflection_eq hv.1 hw.1 (huniq _ hsep)
  -- The facet of `m` is a face of the chamber.
  have hmcl : m ∈ facetClosure Ψ x := by
    intro η hηΨ
    by_cases hle : η m * η x ≤ 0
    · exact Or.inl (sign_eq_zero_iff.2 (hkey η hηΨ hle hψm))
    · exact Or.inr (sign_eq_of_mul_pos (lt_of_not_ge hle))
  -- Every direction in the hyperplane is realized inside the facet of `m`.
  have hker : ∀ u : V, ψ.linear u = 0 → u ∈ (affineSpan ℝ (facet Ψ m)).direction := by
    intro u hu
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ η ∈ Ψ, |η.linear u| ≤ K := by
      obtain ⟨K, hK⟩ :=
        (hΨ.finite_derivativeRoots.image (fun a : Module.Dual ℝ V => |a u|)).bddAbove
      exact ⟨K, fun η hη => hK ⟨η.linear, linear_mem_derivativeRoots hη, rfl⟩⟩
    have hS : {η | η ∈ Ψ ∧ |η m| ≤ K}.Finite := hΨ.finite_bounded_at m (fun _ => K)
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ η ∈ {η | η ∈ Ψ ∧ |η m| ≤ K}, η m ≠ 0 →
        |t * η.linear u| < |η m| := by
      rw [Filter.eventually_all_finite hS]
      intro η _
      by_cases h0 : η m = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
      · have hc : Continuous fun t : ℝ => |t * η.linear u| :=
          (continuous_id.mul continuous_const).abs
        have hlim := hc.tendsto 0
        simp only [zero_mul, abs_zero] at hlim
        exact (hlim.eventually (gt_mem_nhds (abs_pos.2 h0))).mono fun _ ht _ => ht
    have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 := by
      have hlim := continuous_abs.tendsto (0 : ℝ)
      simp only [abs_zero] at hlim
      exact hlim.eventually (gt_mem_nhds one_pos)
    obtain ⟨t, ⟨h1, h2⟩, ht⟩ :=
      (((hev.and hev1).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hmem : t • u +ᵥ m ∈ facet Ψ m := by
      intro η hηΨ
      by_cases hle : η m * η x ≤ 0
      · have hH := hkey η hηΨ hle
        have hmη : η m = 0 := hH hψm
        have hz : ψ (t • u +ᵥ m) = 0 := by
          rw [apply_smul_vadd, hu, hψm, mul_zero, add_zero]
        have hzη : η (t • u +ᵥ m) = 0 := hH hz
        rw [hzη, hmη]
      · have hm0 : η m ≠ 0 := by
          intro h
          apply hle
          rw [h, zero_mul]
        rw [apply_smul_vadd, add_comm]
        symm
        apply sign_add_eq_of_abs_lt
        by_cases hSm : |η m| ≤ K
        · exact h1 η ⟨hηΨ, hSm⟩ hm0
        · push Not at hSm
          calc |t * η.linear u| = |t| * |η.linear u| := abs_mul _ _
            _ ≤ 1 * |η.linear u| := by gcongr
            _ ≤ K := by rw [one_mul]; exact hK η hηΨ
            _ < |η m| := hSm
    have hd : t • u ∈ (affineSpan ℝ (facet Ψ m)).direction := by
      rw [direction_affineSpan]
      have h := vsub_mem_vectorSpan ℝ hmem (mem_facet_self Ψ m)
      rwa [vadd_vsub] at h
    have h := Submodule.smul_mem _ t⁻¹ hd
    rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h
  -- The face spans the reflecting hyperplane.
  have hspan : affineSpan ℝ (facet Ψ m) = hyperplane ψ := by
    apply le_antisymm
    · exact affineSpan_le.2 (facet_subset_hyperplane ⟨hψΨ, hψm⟩)
    · intro p hp
      have hp' : ψ p = 0 := hp
      have hdir : p -ᵥ m ∈ (affineSpan ℝ (facet Ψ m)).direction := by
        apply hker
        rw [AffineMap.linearMap_vsub, vsub_eq_sub, hp', hψm, sub_zero]
      have h := AffineSubspace.vadd_mem_of_mem_direction hdir
        (mem_affineSpan ℝ (mem_facet_self Ψ m))
      rwa [vsub_vadd] at h
  -- Normalize the root: positive at `x`.
  obtain ⟨ψ₁, hψ₁Ψ, v₁, hv₁, hψ₁x, hr₁, hH₁⟩ : ∃ ψ₁ ∈ Ψ, ∃ (v₁ : V) (hv₁ : IsCoroot Ψ ψ₁ v₁),
      0 < ψ₁ x ∧ affineReflection ψ₁ hv₁.1 = affineReflection ψ hv.1 ∧
        hyperplane ψ₁ = hyperplane ψ := by
    rcases lt_or_gt_of_ne (hx ψ hψΨ) with hneg | hpos
    · have hc : (-1 : ℝ) ≠ 0 := by norm_num
      refine ⟨(-1 : ℝ) • ψ, ?_, (-1 : ℝ)⁻¹ • v, hv.smul hc, ?_,
        affineReflection_smul ψ hv.1 hc _, hyperplane_smul ψ hc⟩
      · rw [neg_one_smul]
        exact hΨ.neg_mem hψΨ
      · rw [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        linarith
    · exact ⟨ψ, hψΨ, v, hv, hpos, rfl, rfl⟩
  -- Normalize the root: indivisible, using integrality to exclude `ψ₁ / 4`.
  obtain ⟨ψ₂, hψ₂Ψ, v₂, hv₂, hψ₂x, hnd, hr₂, hH₂⟩ : ∃ ψ₂ ∈ Ψ,
      ∃ (v₂ : V) (hv₂ : IsCoroot Ψ ψ₂ v₂), 0 < ψ₂ x ∧ (2 : ℝ)⁻¹ • ψ₂ ∉ Ψ ∧
        affineReflection ψ₂ hv₂.1 = affineReflection ψ hv.1 ∧
          hyperplane ψ₂ = hyperplane ψ := by
    by_cases hdiv : (2 : ℝ)⁻¹ • ψ₁ ∈ Ψ
    · have hc : (2 : ℝ)⁻¹ ≠ 0 := by norm_num
      refine ⟨(2 : ℝ)⁻¹ • ψ₁, hdiv, (2 : ℝ)⁻¹⁻¹ • v₁, hv₁.smul hc, ?_, ?_, ?_, ?_⟩
      · rw [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        positivity
      · intro h4
        obtain ⟨n, hn⟩ := hΨ.coroot_integral _ h4 ψ₁ hψ₁Ψ v₁ hv₁
        rw [AffineMap.smul_linear, AffineMap.smul_linear, LinearMap.smul_apply,
          LinearMap.smul_apply, hv₁.1, smul_eq_mul, smul_eq_mul] at hn
        have h2n : ((2 * n : ℤ) : ℝ) = 1 := by
          push_cast
          linarith
        have h2n' : 2 * n = 1 := by exact_mod_cast h2n
        omega
      · rw [affineReflection_smul ψ₁ hv₁.1 hc]
        exact hr₁
      · rw [hyperplane_smul ψ₁ hc]
        exact hH₁
    · exact ⟨ψ₁, hψ₁Ψ, v₁, hv₁, hψ₁x, hdiv, hr₁, hH₁⟩
  refine ⟨⟨affineReflection ψ hv.1, affineReflection_mem_affineWeylGroup hψΨ hv⟩,
    ⟨ψ₂, ⟨⟨hψ₂Ψ, ?_⟩, ⟨hψ₂Ψ, hnd⟩, ?_⟩, v₂, hv₂, hr₂.symm⟩, rfl⟩
  · intro z hz
    have h := hz ψ₂ hψ₂Ψ
    rw [sign_pos hψ₂x, eq_comm, sign_eq_one_iff] at h
    exact h
  · refine ⟨⟨x, hx, rfl⟩, ⟨ψ₂, hψ₂Ψ, hΨ.linear_ne_zero ψ₂ hψ₂Ψ, rfl⟩, facet Ψ m,
      ⟨⟨m, rfl⟩, x, rfl, facet_subset_facetClosure_iff.2 hmcl⟩, ?_⟩
    rw [hH₂]
    exact hspan

end AffineRootSystem

/-- For an affine root system and a regular point, the actual images of the positive
indivisible face-span reflections of its chamber are exactly the unique separating wall
reflections. -/
theorem affineChamberWallComparison : AffineChamberWallComparisonStatement.{uV, uA} := by
  intro V A _ _ _ Ψ hΨ x hx
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact AffineRootSystem.chamberSimple_mem_wallReflections hΨ ht
  · intro hs
    exact AffineRootSystem.exists_chamberSimple_of_mem_wallReflections hΨ hx hs

end Langlands.Geometry.Building
