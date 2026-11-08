import Langlands.Geometry.Building.AffineChamberSimpleCone
import Langlands.Geometry.Building.AffineSimpleFixedAdmissible

/-!
# The Gram matrix of the simple affine roots of a chamber

For an affine root system (rank zero allowed) and a chamber, choose for each simple
reflection its simple affine root and coroot. Using the finite set of all coroot vectors we
define a positive semidefinite symmetric form on `V*` satisfying the reflection identity
`2 β(α, ψ̇) = α(ψ̇∨) β(ψ̇, ψ̇)`. For distinct simple reflections the Cartan integer
`ψ̇_s(ψ̇_t∨)` is nonpositive, the Gram entry is nonpositive, and it is nonzero for
noncommuting reflections.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Langlands.Group.TitsSystem GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-! ### Chosen simple roots and coroots -/

section Chosen

variable {C : Set A}

/-- A simple affine root whose reflection is the given chamber-simple reflection. -/
def chamberSimpleRoot (s : chamberSimpleReflections Ψ C) : A →ᵃ[ℝ] ℝ :=
  s.2.choose

theorem chamberSimpleRoot_mem (s : chamberSimpleReflections Ψ C) :
    chamberSimpleRoot s ∈ simpleAffineRoots Ψ C :=
  s.2.choose_spec.1

/-- The coroot of the chosen simple affine root. -/
def chamberSimpleCoroot (s : chamberSimpleReflections Ψ C) : V :=
  s.2.choose_spec.2.choose

theorem isCoroot_chamberSimpleCoroot (s : chamberSimpleReflections Ψ C) :
    IsCoroot Ψ (chamberSimpleRoot s) (chamberSimpleCoroot s) :=
  s.2.choose_spec.2.choose_spec.choose

theorem coe_eq_affineReflection_chamberSimpleRoot (s : chamberSimpleReflections Ψ C) :
    ((s : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) =
      affineReflection (chamberSimpleRoot s) (isCoroot_chamberSimpleCoroot s).1 :=
  s.2.choose_spec.2.choose_spec.choose_spec

theorem apply_eq_self_iff_chamberSimpleRoot (s : chamberSimpleReflections Ψ C) (x : A) :
    ((s : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) x = x ↔ chamberSimpleRoot s x = 0 := by
  rw [coe_eq_affineReflection_chamberSimpleRoot, affineReflection_apply_eq_self_iff]

end Chosen

/-! ### Coroot vectors -/

/-- All coroot vectors of roots of `Ψ`. -/
def corootSet (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set V :=
  {v | ∃ ψ ∈ Ψ, IsCoroot Ψ ψ v}

/-- The reflection of a coroot in another root is a coroot of the reflected root. -/
theorem IsCoroot.reflect {ψ η : A →ᵃ[ℝ] ℝ} {u v : V} (hu : IsCoroot Ψ ψ u)
    (hv : IsCoroot Ψ η v) :
    IsCoroot Ψ (η - η.linear u • ψ) (v - ψ.linear v • u) := by
  have hψu := hu.1
  refine ⟨?_, fun ζ hζ => ?_⟩
  · rw [AffineMap.sub_linear, AffineMap.smul_linear, LinearMap.sub_apply,
      LinearMap.smul_apply, map_sub, map_sub, map_smul, map_smul, hψu, hv.1, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring
  · have h1 := hu.2 ζ hζ
    have h2 := hv.2 _ h1
    have h3 := hu.2 _ h2
    convert h3 using 1
    ext x
    simp only [AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, AffineMap.sub_linear, AffineMap.smul_linear, LinearMap.sub_apply,
      LinearMap.smul_apply, map_sub, map_smul, hψu]
    ring

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

/-- Roots with the same derivative have the same coroot. -/
theorem coroot_eq_of_linear_eq {ψ η : A →ᵃ[ℝ] ℝ} {v w : V} (hv : IsCoroot Ψ ψ v)
    (hw : IsCoroot Ψ η w) (hlin : η.linear = ψ.linear) : v = w := by
  have hmaps : ∀ (ζ : A →ᵃ[ℝ] ℝ) (u : V), IsCoroot Ψ ζ u →
      Set.MapsTo (Module.preReflection ζ.linear (Module.Dual.eval ℝ V u))
        (derivativeRoots Ψ) (derivativeRoots Ψ) := by
    rintro ζ u hu _ ⟨θ, hθ, rfl⟩
    refine ⟨θ - θ.linear u • ζ, hu.2 θ hθ, ?_⟩
    simp [Module.preReflection_apply]
  have hw' := hmaps η w hw
  rw [hlin] at hw'
  have hw1 : ψ.linear w = 2 := hlin ▸ hw.1
  have h := Module.Dual.eq_of_preReflection_mapsTo hΨ.finite_derivativeRoots
    hΨ.span_derivativeRoots_eq_top (by simpa using hv.1) (hmaps ψ v hv)
    (by simpa using hw1) hw'
  exact Module.eval_apply_injective ℝ h

/-- There are only finitely many coroot vectors. -/
theorem finite_corootSet : (corootSet Ψ).Finite := by
  refine (hΨ.finite_derivativeRoots.biUnion fun a _ =>
    (?_ : Set.Subsingleton {v : V | ∃ ψ ∈ Ψ, ψ.linear = a ∧ IsCoroot Ψ ψ v}).finite).subset ?_
  · rintro v ⟨ψ, -, hψ, hv⟩ w ⟨η, -, hη, hw⟩
    exact hΨ.coroot_eq_of_linear_eq hv hw (hη.trans hψ.symm)
  · rintro v ⟨ψ, hψ, hv⟩
    exact Set.mem_biUnion (linear_mem_derivativeRoots hψ) ⟨ψ, hψ, rfl, hv⟩

/-- The symmetric form `β(α, α') = Σ_v α(v) α'(v)` over all coroot vectors `v`. -/
def corootForm (α α' : Module.Dual ℝ V) : ℝ :=
  ∑ v ∈ hΨ.finite_corootSet.toFinset, α v * α' v

theorem corootForm_comm (α α' : Module.Dual ℝ V) :
    hΨ.corootForm α α' = hΨ.corootForm α' α := by
  unfold corootForm
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem corootForm_self_nonneg (α : Module.Dual ℝ V) : 0 ≤ hΨ.corootForm α α :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- The form is positive on the derivative of every root. -/
theorem corootForm_self_pos {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    0 < hΨ.corootForm ψ.linear ψ.linear := by
  obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ hψ
  have hmem : u ∈ hΨ.finite_corootSet.toFinset :=
    hΨ.finite_corootSet.mem_toFinset.2 ⟨ψ, hψ, hu⟩
  have hle := Finset.single_le_sum (f := fun v => ψ.linear v * ψ.linear v)
    (fun v _ => mul_self_nonneg _) hmem
  simp only [hu.1] at hle
  unfold corootForm
  linarith

/-- Invariance of the form under the linear reflection of a root, in the form
`2 β(α, ψ̇) = α(ψ̇∨) β(ψ̇, ψ̇)`. -/
theorem two_mul_corootForm {ψ : A →ᵃ[ℝ] ℝ} {u : V} (hu : IsCoroot Ψ ψ u)
    (α : Module.Dual ℝ V) :
    2 * hΨ.corootForm α ψ.linear = α u * hΨ.corootForm ψ.linear ψ.linear := by
  set T := hΨ.finite_corootSet.toFinset
  let r : V → V := fun v => v - ψ.linear v • u
  have hr : ∀ v ∈ T, r v ∈ T := by
    intro v hv
    obtain ⟨η, hη, hηv⟩ := hΨ.finite_corootSet.mem_toFinset.1 hv
    exact hΨ.finite_corootSet.mem_toFinset.2 ⟨_, hu.2 η hη, hu.reflect hηv⟩
  have hrr : ∀ v, r (r v) = v := by
    intro v
    simp only [r, map_sub, map_smul, hu.1, smul_eq_mul]
    module
  have hsum : ∑ v ∈ T, α v * ψ.linear v = ∑ v ∈ T, α (r v) * ψ.linear (r v) :=
    Finset.sum_nbij' r r hr hr (fun v _ => hrr v) (fun v _ => hrr v) (fun v _ => by rw [hrr v])
  have hexp : ∀ v, α (r v) * ψ.linear (r v) =
      -(α v * ψ.linear v) + α u * (ψ.linear v * ψ.linear v) := by
    intro v
    simp only [r, map_sub, map_smul, hu.1, smul_eq_mul]
    ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  unfold corootForm
  linarith

/-! ### Simple roots of a chamber -/

section Chamber

variable {c : A}

/-- Simple reflections whose chosen roots are proportional are equal. -/
theorem eq_of_chamberSimpleRoot_eq_smul {C : Set A} {s t : chamberSimpleReflections Ψ C}
    {r : ℝ} (h : chamberSimpleRoot t = r • chamberSimpleRoot s) : t = s := by
  have hr : r ≠ 0 := by
    rintro rfl
    apply hΨ.linear_ne_zero _ (chamberSimpleRoot_mem t).1.1
    rw [h, zero_smul, AffineMap.zero_linear]
  have heq := affineReflection_eq_of_eq_smul hΨ (isCoroot_chamberSimpleCoroot s)
    (isCoroot_chamberSimpleCoroot t) hr h
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_eq_affineReflection_chamberSimpleRoot t, coe_eq_affineReflection_chamberSimpleRoot s,
    heq]

/-- A point on the wall of a simple root, in the closure of the chamber, at which every other
simple root is positive (a point of the panel). -/
theorem exists_panel_point (hc : IsRegular Ψ c) (s : chamberSimpleReflections Ψ (facet Ψ c)) :
    ∃ p ∈ facetClosure Ψ c, chamberSimpleRoot s p = 0 ∧
      ∀ t : chamberSimpleReflections Ψ (facet Ψ c), t ≠ s → 0 < chamberSimpleRoot t p := by
  obtain ⟨-, -, Fa, ⟨⟨y, rfl⟩, x, hx, hsub⟩, hspan⟩ := (chamberSimpleRoot_mem s).2.2
  have hyc : y ∈ facetClosure Ψ c := by
    rw [← facetClosure_eq_of_facetRel (facet_eq_facet_iff.1 hx)]
    exact hsub (mem_facet_self Ψ y)
  refine ⟨y, hyc, ?_, fun t hts => ?_⟩
  · have hy : y ∈ affineSpan ℝ (facet Ψ y) := subset_affineSpan ℝ _ (mem_facet_self Ψ y)
    rw [hspan] at hy
    exact mem_hyperplane.1 hy
  · have hnn := (mem_facetClosure_iff_simple_nonneg hΨ hc y).1 hyc _ (chamberSimpleRoot_mem t)
    refine lt_of_le_of_ne hnn fun h0 => hts ?_
    have hsubH : facet Ψ y ⊆ hyperplane (chamberSimpleRoot t) := by
      intro z hz
      have := hz _ (chamberSimpleRoot_mem t).1.1
      rw [← h0, sign_zero, eq_comm, sign_eq_zero_iff] at this
      exact mem_hyperplane.2 this
    have hle : hyperplane (chamberSimpleRoot s) ≤ hyperplane (chamberSimpleRoot t) := by
      rw [← hspan]
      exact affineSpan_le.2 hsubH
    exact eq_of_chamberSimpleRoot_eq_smul hΨ
      (eq_smul_of_hyperplane_le (isCoroot_chamberSimpleCoroot s).1 hle)

/-- For distinct simple reflections the Cartan integer `ψ̇_s(ψ̇_t∨)` is nonpositive. -/
theorem linear_chamberSimpleCoroot_nonpos (hc : IsRegular Ψ c)
    {s t : chamberSimpleReflections Ψ (facet Ψ c)} (hst : s ≠ t) :
    (chamberSimpleRoot s).linear (chamberSimpleCoroot t) ≤ 0 := by
  by_contra hk
  rw [not_le] at hk
  set k := (chamberSimpleRoot s).linear (chamberSimpleCoroot t) with hk_def
  set η := chamberSimpleRoot s - k • chamberSimpleRoot t with hη_def
  have hη : η ∈ Ψ := (isCoroot_chamberSimpleCoroot t).2 _ (chamberSimpleRoot_mem s).1.1
  have happ : ∀ y, η y = chamberSimpleRoot s y - k * chamberSimpleRoot t y := by
    intro y
    simp only [hη_def, AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  obtain ⟨p, hp, hsp, hpos⟩ := exists_panel_point hΨ hc s
  obtain ⟨q, hq, htq, hpos'⟩ := exists_panel_point hΨ hc t
  have hηp : η p < 0 := by
    rw [happ, hsp]
    have := hpos t (Ne.symm hst)
    nlinarith
  have hηq : 0 < η q := by
    rw [happ, htq, mul_zero, sub_zero]
    exact hpos' s hst
  have h1 := (hp η hη).resolve_left (by rw [sign_neg hηp]; decide)
  have h2 := (hq η hη).resolve_left (by rw [sign_pos hηq]; decide)
  rw [sign_neg hηp] at h1
  rw [sign_pos hηq, ← h1] at h2
  exact absurd h2 (by decide)

omit hΨ in
/-- Simple reflections whose Cartan integers vanish in both orders commute. -/
theorem mul_comm_of_linear_chamberSimpleCoroot_eq_zero {C : Set A}
    {s t : chamberSimpleReflections Ψ C}
    (hst : (chamberSimpleRoot s).linear (chamberSimpleCoroot t) = 0)
    (hts : (chamberSimpleRoot t).linear (chamberSimpleCoroot s) = 0) :
    (s : affineWeylGroup Ψ) * t = t * s := by
  apply Subtype.ext
  change ((s : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) * ((t : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) =
    ((t : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) * ((s : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A)
  rw [coe_eq_affineReflection_chamberSimpleRoot s, coe_eq_affineReflection_chamberSimpleRoot t]
  ext x
  rw [AffineEquiv.coe_mul, AffineEquiv.coe_mul, Function.comp_apply, Function.comp_apply,
    affineReflection_apply, affineReflection_apply (chamberSimpleRoot t),
    affineReflection_apply (chamberSimpleRoot t), affineReflection_apply (chamberSimpleRoot s),
    AffineMap.map_vadd, AffineMap.map_vadd, map_smul, map_smul, hst, hts, smul_eq_mul,
    smul_eq_mul, mul_zero, mul_zero, vadd_eq_add, vadd_eq_add, zero_add, zero_add,
    vadd_vadd, vadd_vadd, add_comm]

/-- The Gram matrix `β(ψ̇_s, ψ̇_t)` of the chosen simple roots. -/
def chamberSimpleGram {C : Set A} (s t : chamberSimpleReflections Ψ C) : ℝ :=
  hΨ.corootForm (chamberSimpleRoot s).linear (chamberSimpleRoot t).linear

theorem chamberSimpleGram_comm {C : Set A} (s t : chamberSimpleReflections Ψ C) :
    hΨ.chamberSimpleGram s t = hΨ.chamberSimpleGram t s :=
  hΨ.corootForm_comm _ _

theorem chamberSimpleGram_self_pos {C : Set A} (s : chamberSimpleReflections Ψ C) :
    0 < hΨ.chamberSimpleGram s s :=
  hΨ.corootForm_self_pos (chamberSimpleRoot_mem s).1.1

theorem two_mul_chamberSimpleGram {C : Set A} (s t : chamberSimpleReflections Ψ C) :
    2 * hΨ.chamberSimpleGram s t =
      (chamberSimpleRoot s).linear (chamberSimpleCoroot t) * hΨ.chamberSimpleGram t t :=
  hΨ.two_mul_corootForm (isCoroot_chamberSimpleCoroot t) _

/-- Off-diagonal Gram entries are nonpositive. -/
theorem chamberSimpleGram_nonpos (hc : IsRegular Ψ c)
    {s t : chamberSimpleReflections Ψ (facet Ψ c)} (hst : s ≠ t) :
    hΨ.chamberSimpleGram s t ≤ 0 := by
  have h2 := hΨ.two_mul_chamberSimpleGram s t
  have hk := linear_chamberSimpleCoroot_nonpos hΨ hc hst
  have hpos := hΨ.chamberSimpleGram_self_pos t
  nlinarith

/-- The Gram entry of two noncommuting simple reflections is nonzero. -/
theorem chamberSimpleGram_ne_zero {C : Set A} {s t : chamberSimpleReflections Ψ C}
    (h : (s : affineWeylGroup Ψ) * t ≠ t * s) : hΨ.chamberSimpleGram s t ≠ 0 := by
  intro h0
  apply h
  have h1 := hΨ.two_mul_chamberSimpleGram s t
  have h2 := hΨ.two_mul_chamberSimpleGram t s
  rw [h0, mul_zero, eq_comm, mul_eq_zero] at h1
  rw [hΨ.chamberSimpleGram_comm t s, h0, mul_zero, eq_comm, mul_eq_zero] at h2
  exact mul_comm_of_linear_chamberSimpleCoroot_eq_zero
    (h1.resolve_right (hΨ.chamberSimpleGram_self_pos t).ne')
    (h2.resolve_right (hΨ.chamberSimpleGram_self_pos s).ne')

end Chamber

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
