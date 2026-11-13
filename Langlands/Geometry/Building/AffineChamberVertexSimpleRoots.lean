import Langlands.Geometry.Building.AffineChamberCartanMarks
import Langlands.Geometry.Building.SimplexFixedPointTransitivity

/-!
# The vertices of a chamber and its simple affine roots

Let `Ψ` be a nonempty affine root system and `C` a chamber whose simple affine roots are
linearly independent affine functionals (KP Proposition 1.3.22(5), a consequence of
irreducibility; here an explicit hypothesis).
Each simple affine root `ψ` determines the vertex of `C` at which all the other simple affine
roots vanish, and this is a bijection between the simple affine roots and the vertices of the
closure of `C` (KP Proposition 1.3.22(6)). The bijection is natural for root-preserving affine
automorphisms stabilizing `C`. A group of such automorphisms with at most one fixed point in
the closure of `C` therefore acts transitively on the simple affine roots.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-! ### Linear algebra -/

section LinearAlgebra

/-- A linearly independent finite family of linear functionals takes arbitrary prescribed
values at some vector. -/
theorem exists_forall_apply_eq_of_linearIndependent {W : Type*} [AddCommGroup W]
    [Module ℝ W] {κ : Type*} [Fintype κ] {f : κ → Module.Dual ℝ W}
    (hf : LinearIndependent ℝ f) (t : κ → ℝ) : ∃ w : W, ∀ k, f k w = t k := by
  classical
  let F : W →ₗ[ℝ] (κ → ℝ) := LinearMap.pi f
  have hinj : Function.Injective F.dualMap := by
    rw [injective_iff_map_eq_zero]
    intro ℓ hℓ
    have hcoef : ∀ k, ℓ (fun j => if k = j then (1 : ℝ) else 0) = 0 := by
      have hsum : ∑ k, ℓ (fun j => if k = j then (1 : ℝ) else 0) • f k = 0 := by
        apply LinearMap.ext
        intro w
        have h1 : ℓ (F w) = 0 := by simpa using LinearMap.congr_fun hℓ w
        rw [LinearMap.pi_apply_eq_sum_univ ℓ (F w)] at h1
        rw [LinearMap.sum_apply, LinearMap.zero_apply]
        refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
        simp only [LinearMap.smul_apply, smul_eq_mul, F, LinearMap.pi_apply]
        ring
      exact Fintype.linearIndependent_iff.1 hf _ hsum
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ ℓ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [hcoef k, smul_zero]
  obtain ⟨w, hw⟩ := LinearMap.dualMap_injective_iff.1 hinj t
  exact ⟨w, fun k => by simpa [F] using congrFun hw k⟩

/-- Evaluation of a finite sum of affine functionals. -/
theorem affineMap_sum_apply {ι : Type*} (s : Finset ι) (f : ι → A →ᵃ[ℝ] ℝ) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, AffineMap.coe_add, Pi.add_apply, ih]

variable {ι : Type*} [Fintype ι]

/-- A linear relation among the derivatives makes the combination of the affine functionals
constant. -/
theorem sum_mul_apply_eq_of_sum_smul_linear_eq_zero (f : ι → A →ᵃ[ℝ] ℝ) {a : ι → ℝ}
    (ha : ∑ i, a i • (f i).linear = 0) (x y : A) :
    ∑ i, a i * f i x = ∑ i, a i * f i y := by
  have h := LinearMap.congr_fun ha (x -ᵥ y)
  rw [LinearMap.sum_apply, LinearMap.zero_apply] at h
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [LinearMap.smul_apply, AffineMap.linearMap_vsub, vsub_eq_sub, smul_eq_mul, mul_sub]

/-- For linearly independent affine functionals, a linear relation among the derivatives
whose combination vanishes at one point is trivial. -/
theorem eq_zero_of_linearIndependent_of_sum_eq_zero {f : ι → A →ᵃ[ℝ] ℝ}
    (hf : LinearIndependent ℝ f) {a : ι → ℝ} (ha : ∑ i, a i • (f i).linear = 0) {x : A}
    (hx : ∑ i, a i * f i x = 0) : a = 0 := by
  have hsum : ∑ i, a i • f i = 0 := by
    ext y
    rw [affineMap_sum_apply, AffineMap.coe_zero, Pi.zero_apply]
    simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [sum_mul_apply_eq_of_sum_smul_linear_eq_zero f ha y x, hx]
  funext i
  exact Fintype.linearIndependent_iff.1 hf a hsum i

/-- For linearly independent affine functionals, any two linear relations among the
derivatives are proportional. -/
theorem smul_eq_smul_of_linearIndependent {f : ι → A →ᵃ[ℝ] ℝ} (hf : LinearIndependent ℝ f)
    {a b : ι → ℝ} (ha : ∑ i, a i • (f i).linear = 0) (hb : ∑ i, b i • (f i).linear = 0)
    (x : A) : (∑ i, a i * f i x) • b = (∑ i, b i * f i x) • a := by
  set κa := ∑ i, a i * f i x
  set κb := ∑ i, b i * f i x
  have hd : ∑ i, (κa • b - κb • a) i • (f i).linear = 0 := by
    have h : ∀ i, (κa • b - κb • a) i • (f i).linear =
        κa • (b i • (f i).linear) - κb • (a i • (f i).linear) := fun i => by
      ext v
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
        LinearMap.smul_apply]
      ring
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.smul_sum,
      ← Finset.smul_sum, ha, hb, smul_zero, smul_zero, sub_zero]
  have hdx : ∑ i, (κa • b - κb • a) i * f i x = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show ∑ i, b i * f i x = κb from rfl, show ∑ i, a i * f i x = κa from rfl]
    ring
  exact sub_eq_zero.1 (eq_zero_of_linearIndependent_of_sum_eq_zero hf hd hdx)

/-- For linearly independent affine functionals, the derivatives become linearly independent
after removing one index in the support of a nonzero linear relation among them. -/
theorem linearIndependent_linear_ne [DecidableEq ι] [Nonempty A] {f : ι → A →ᵃ[ℝ] ℝ}
    (hf : LinearIndependent ℝ f) {a : ι → ℝ} (ha : ∑ i, a i • (f i).linear = 0)
    (ha0 : a ≠ 0) {i₀ : ι} (hi₀ : a i₀ ≠ 0) :
    LinearIndependent ℝ fun i : {i // i ≠ i₀} => (f i).linear := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let b : ι → ℝ := fun i => if h : i = i₀ then 0 else g ⟨i, h⟩
  have hb : ∑ i, b i • (f i).linear = 0 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ≠ i₀)]
    have h1 : ∑ i : {i // i ≠ i₀}, b i • (f i).linear = ∑ i : {i // i ≠ i₀}, g i • (f i).linear :=
      Finset.sum_congr rfl fun i _ => by simp [b, i.2]
    have h2 : ∑ i : {i // ¬i ≠ i₀}, b i • (f i).linear = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [b, not_not.1 i.2]
    rw [h1, h2, hg, add_zero]
  obtain ⟨x⟩ := ‹Nonempty A›
  have hprop := smul_eq_smul_of_linearIndependent hf ha hb x
  have hκa : ∑ i, a i * f i x ≠ 0 := fun h0 =>
    ha0 (eq_zero_of_linearIndependent_of_sum_eq_zero hf ha h0)
  have hκb : ∑ i, b i * f i x = 0 := by
    have h := congrFun hprop i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [show b i₀ = 0 by simp [b], mul_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_right hi₀
  rw [hκb, zero_smul] at hprop
  intro i
  have h := congrFun hprop i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [show b i = g i by simp [b, i.2]] at h
  exact (mul_eq_zero.1 h).resolve_left hκa

end LinearAlgebra

/-! ### The vertex opposite to a simple affine root -/

open Classical in
/-- The vertex of `C` opposite to the wall of `ψ`: a point at which every other simple affine
root of `C` vanishes (KP Proposition 1.3.22(6)), chosen when one exists. Under the hypotheses
of `IsAffineRootSystemWithRankZero.eq_simpleVertex_iff` such a point exists and is unique. -/
def simpleVertex (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (ψ : A →ᵃ[ℝ] ℝ) : A :=
  if h : ∃ x : A, ∀ η ∈ simpleAffineRoots Ψ C, η ≠ ψ → η x = 0 then h.choose
  else Classical.arbitrary A

theorem simpleVertex_spec {Ψ : Set (A →ᵃ[ℝ] ℝ)} {C : Set A} {ψ : A →ᵃ[ℝ] ℝ}
    (h : ∃ x : A, ∀ η ∈ simpleAffineRoots Ψ C, η ≠ ψ → η x = 0) :
    ∀ η ∈ simpleAffineRoots Ψ C, η ≠ ψ → η (simpleVertex Ψ C ψ) = 0 := by
  classical
  simp only [simpleVertex, h, dite_true]
  exact h.choose_spec

/-- A root-preserving automorphism stabilizing `C` maps simple affine roots of `C` to simple
affine roots of `C` by `ψ ↦ ψ ∘ e⁻¹`. -/
theorem comp_symm_mem_simpleAffineRoots {Ψ : Set (A →ᵃ[ℝ] ℝ)} {C : Set A}
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) (hC : e '' C = C) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ C) :
    ψ.comp (e.symm : A →ᵃ[ℝ] A) ∈ simpleAffineRoots Ψ C := by
  have h := (affineFunctionalTransport_mem_simpleAffineRoots_iff e Ψ C ψ).2 hψ
  rw [transportedRoots_eq_self_of_mem_rootStabilizer he, hC] at h
  exact h

theorem symm_mem_rootStabilizer {Ψ : Set (A →ᵃ[ℝ] ℝ)} {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) : e.symm ∈ rootStabilizer Ψ := by
  rw [← AffineEquiv.inv_def]
  exact inv_mem he

theorem symm_image_eq_of_image_eq {e : A ≃ᵃ[ℝ] A} {C : Set A} (hC : e '' C = C) :
    e.symm '' C = C := by
  conv_lhs => rw [← hC]
  rw [Set.image_image]
  simp

/-- The evaluation of a combination of the simple affine roots of `C` with coefficients `m` at
a point where all simple roots but `ψ` vanish. -/
theorem sum_mul_apply_eq_of_forall_ne {Ψ : Set (A →ᵃ[ℝ] ℝ)} {C : Set A}
    [Fintype (simpleAffineRoots Ψ C)] (m : simpleAffineRoots Ψ C → ℝ)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ C) {x : A}
    (hx : ∀ η ∈ simpleAffineRoots Ψ C, η ≠ ψ → η x = 0) :
    ∑ η, m η * (η : A →ᵃ[ℝ] ℝ) x = m ⟨ψ, hψ⟩ * ψ x :=
  Fintype.sum_eq_single (f := fun η : simpleAffineRoots Ψ C =>
      m η * (η : A →ᵃ[ℝ] ℝ) x) (⟨ψ, hψ⟩ : simpleAffineRoots Ψ C)
    (fun b hb => by
      show m b * (b : A →ᵃ[ℝ] ℝ) x = 0
      rw [hx b.1 b.2 fun h => hb (Subtype.ext h), mul_zero])

/-- A point of the closure of the facet of `x` is on the same closed side as `x` of every root
hyperplane. -/
theorem mul_nonneg_of_mem_facetClosure {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x y : A}
    (hy : y ∈ facetClosure Ψ x) {ζ : A →ᵃ[ℝ] ℝ} (hζ : ζ ∈ Ψ) : 0 ≤ ζ y * ζ x := by
  rcases hy ζ hζ with h | h
  · rw [sign_eq_zero_iff.1 h, zero_mul]
  · rcases lt_trichotomy (ζ y) 0 with hlt | heq | hgt
    · rw [sign_neg hlt, eq_comm, sign_eq_neg_one_iff] at h
      exact (mul_pos_of_neg_of_neg hlt h).le
    · rw [heq, zero_mul]
    · rw [sign_pos hgt, eq_comm, sign_eq_one_iff] at h
      exact (mul_pos hgt h).le

namespace IsAffineRootSystemWithRankZero

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A}

include hΨ

/-- Two points at which all simple affine roots of a chamber take the same values coincide. -/
theorem eq_of_forall_simpleAffineRoots_apply_eq (hc : IsRegular Ψ c) {x y : A}
    (h : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), ψ x = ψ y) : x = y := by
  have hv : x -ᵥ y = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc fun ψ hψ =>
    le_of_eq (by rw [AffineMap.linearMap_vsub, h ψ hψ, vsub_self])
  exact vsub_eq_zero_iff_eq.1 hv

/-- A chamber of a nonempty affine root system has a simple affine root. -/
theorem simpleAffineRoots_nonempty (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) :
    (simpleAffineRoots Ψ (facet Ψ c)).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  obtain ⟨ζ, hζ⟩ := hne
  apply hΨ.linear_ne_zero ζ hζ
  apply LinearMap.ext
  intro v
  have hv : v = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc (v := v)
    (by simp [hemp])
  simp [hv]

section Finite

variable [Fintype (simpleAffineRoots Ψ (facet Ψ c))]

/-- The derivatives of the simple affine roots of a chamber of a nonempty affine root system
satisfy a nontrivial linear relation. -/
theorem exists_ne_zero_linear_relation (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) :
    ∃ a : simpleAffineRoots Ψ (facet Ψ c) → ℝ, a ≠ 0 ∧
      ∑ η, a η • (η : A →ᵃ[ℝ] ℝ).linear = 0 := by
  classical
  obtain ⟨ψ₀, hψ₀⟩ := hΨ.simpleAffineRoots_nonempty hc hne
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent ℝ
      fun η : simpleAffineRoots Ψ (facet Ψ c) => (η : A →ᵃ[ℝ] ℝ).linear := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hg0
    exact hcon g (fun h0 => hg0 fun i => by rw [h0, Pi.zero_apply]) hg
  obtain ⟨v, hv⟩ := exists_forall_apply_eq_of_linearIndependent hli
    (fun η => if η = ⟨ψ₀, hψ₀⟩ then 1 else 0)
  have hv0 : v = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc fun η hη => by
    show 0 ≤ ((⟨η, hη⟩ : simpleAffineRoots Ψ (facet Ψ c)) : A →ᵃ[ℝ] ℝ).linear v
    rw [hv]
    split_ifs <;> norm_num
  have h := hv ⟨ψ₀, hψ₀⟩
  rw [hv0, map_zero] at h
  simp at h

variable (hli : LinearIndependent ℝ
  fun ψ : simpleAffineRoots Ψ (facet Ψ c) => (ψ : A →ᵃ[ℝ] ℝ))

include hli

/-- The real marks (KP Proposition 1.3.47(1)–(2), as corrected): if the simple affine roots of
a chamber are linearly independent, some strictly positive combination of them is a positive
constant. -/
theorem exists_pos_linear_relation (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) :
    ∃ m : simpleAffineRoots Ψ (facet Ψ c) → ℝ, (∀ η, 0 < m η) ∧
      ∑ η, m η • (η : A →ᵃ[ℝ] ℝ).linear = 0 ∧
      ∀ x : A, 0 < ∑ η, m η * (η : A →ᵃ[ℝ] ℝ) x := by
  classical
  obtain ⟨a, ha0, ha⟩ := hΨ.exists_ne_zero_linear_relation hc hne
  obtain ⟨ψ, hψ⟩ := Function.ne_iff.1 ha0
  have hind := linearIndependent_linear_ne (f := fun η : simpleAffineRoots Ψ (facet Ψ c) =>
    (η : A →ᵃ[ℝ] ℝ)) hli ha ha0 hψ
  have hsign : ∀ η, 0 < a η * a ψ := by
    intro η
    by_cases hηψ : η = ψ
    · rw [hηψ]
      exact mul_self_pos.2 hψ
    by_contra hle
    push Not at hle
    obtain ⟨v, hv⟩ := exists_forall_apply_eq_of_linearIndependent hind
      (fun j => if (j : simpleAffineRoots Ψ (facet Ψ c)) = η then 1 else 0)
    have hvη : (η : A →ᵃ[ℝ] ℝ).linear v = 1 := by
      have := hv ⟨η, hηψ⟩
      simpa using this
    have hrel := LinearMap.congr_fun ha v
    rw [LinearMap.sum_apply, LinearMap.zero_apply,
      Fintype.sum_eq_add ψ η (Ne.symm hηψ) ?_] at hrel
    · simp only [LinearMap.smul_apply, smul_eq_mul, hvη, mul_one] at hrel
      have hψv : 0 ≤ (ψ : A →ᵃ[ℝ] ℝ).linear v := by
        by_contra hneg
        push Not at hneg
        have h1 : a ψ * a ψ * (ψ : A →ᵃ[ℝ] ℝ).linear v = -(a η * a ψ) := by
          linear_combination a ψ * hrel
        have h2 := mul_neg_of_pos_of_neg (mul_self_pos.2 hψ) hneg
        linarith
      have hv0 : v = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc fun θ hθ => by
        by_cases hθψ : (⟨θ, hθ⟩ : simpleAffineRoots Ψ (facet Ψ c)) = ψ
        · rw [← hθψ] at hψv
          exact hψv
        · have := hv ⟨⟨θ, hθ⟩, hθψ⟩
          simp only at this
          rw [this]
          split_ifs <;> norm_num
      rw [hv0, map_zero] at hvη
      exact zero_ne_one hvη
    · rintro θ ⟨hθψ, hθη⟩
      have := hv ⟨θ, hθψ⟩
      simp only [hθη, ↓reduceIte] at this
      rw [LinearMap.smul_apply, this, smul_zero]
  refine ⟨fun η => a η * a ψ, hsign, ?_, ?_⟩
  · simp_rw [mul_comm (a _) (a ψ), mul_smul]
    rw [← Finset.smul_sum, ha, smul_zero]
  · intro x
    rw [sum_mul_apply_eq_of_sum_smul_linear_eq_zero
      (fun η : simpleAffineRoots Ψ (facet Ψ c) => (η : A →ᵃ[ℝ] ℝ)) (a := fun η => a η * a ψ)
      (by simp_rw [mul_comm (a _) (a ψ), mul_smul]; rw [← Finset.smul_sum, ha, smul_zero])
      x c]
    obtain ⟨ψ₀, hψ₀⟩ := hΨ.simpleAffineRoots_nonempty hc hne
    have : Nonempty (simpleAffineRoots Ψ (facet Ψ c)) := ⟨⟨ψ₀, hψ₀⟩⟩
    exact Finset.sum_pos (fun η _ => mul_pos (hsign η)
      (pos_of_mem_simpleAffineRoots η.2 (mem_facet_self Ψ c))) Finset.univ_nonempty

end Finite

variable (hli : LinearIndependent ℝ
  fun ψ : simpleAffineRoots Ψ (facet Ψ c) => (ψ : A →ᵃ[ℝ] ℝ))

include hli

/-- Existence of the vertex opposite to the wall of a simple affine root. -/
theorem exists_forall_apply_eq_zero_of_ne (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ x : A, ∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ → η x = 0 := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  obtain ⟨m, hm, hrel, -⟩ := hΨ.exists_pos_linear_relation hli hc hne
  have hm0 : m ≠ 0 := fun h => (hm ⟨ψ, hψ⟩).ne' (by rw [h, Pi.zero_apply])
  have hind := linearIndependent_linear_ne (f := fun η : simpleAffineRoots Ψ (facet Ψ c) =>
    (η : A →ᵃ[ℝ] ℝ)) hli hrel hm0 (hm ⟨ψ, hψ⟩).ne'
  obtain ⟨v, hv⟩ := exists_forall_apply_eq_of_linearIndependent hind
    (fun j => -((j : simpleAffineRoots Ψ (facet Ψ c)) : A →ᵃ[ℝ] ℝ) c)
  refine ⟨v +ᵥ c, fun η hη hηψ => ?_⟩
  have h := hv ⟨⟨η, hη⟩, fun h => hηψ (congrArg Subtype.val h)⟩
  simp only at h
  rw [AffineMap.map_vadd, h, vadd_eq_add, neg_add_cancel]

/-- Uniqueness of the vertex opposite to the wall of a simple affine root. -/
theorem eq_of_forall_apply_eq_zero_of_ne (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) {x y : A}
    (hx : ∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ → η x = 0)
    (hy : ∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ → η y = 0) : x = y := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  obtain ⟨m, hm, hrel, -⟩ := hΨ.exists_pos_linear_relation hli hc hne
  apply hΨ.eq_of_forall_simpleAffineRoots_apply_eq hc
  intro η hη
  by_cases h : η = ψ
  · subst h
    have hconst := sum_mul_apply_eq_of_sum_smul_linear_eq_zero
      (fun θ : simpleAffineRoots Ψ (facet Ψ c) => (θ : A →ᵃ[ℝ] ℝ)) hrel x y
    rw [sum_mul_apply_eq_of_forall_ne m hη hx,
      sum_mul_apply_eq_of_forall_ne m hη hy] at hconst
    exact mul_left_cancel₀ (hm _).ne' hconst
  · rw [hx η hη h, hy η hη h]

/-- The vertex of `C` opposite to the wall of `ψ` is the unique point at which all simple
affine roots of `C` other than `ψ` vanish. -/
theorem eq_simpleVertex_iff (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) {x : A} :
    x = simpleVertex Ψ (facet Ψ c) ψ ↔
      ∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ → η x = 0 := by
  have hspec := simpleVertex_spec (hΨ.exists_forall_apply_eq_zero_of_ne hli hc hne hψ)
  constructor
  · rintro rfl
    exact hspec
  · intro hx
    exact hΨ.eq_of_forall_apply_eq_zero_of_ne hli hc hne hψ hx hspec

theorem apply_simpleVertex_of_ne (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {ψ η : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) (hη : η ∈ simpleAffineRoots Ψ (facet Ψ c))
    (hηψ : η ≠ ψ) : η (simpleVertex Ψ (facet Ψ c) ψ) = 0 :=
  (hΨ.eq_simpleVertex_iff hli hc hne hψ).1 rfl η hη hηψ

/-- A simple affine root is positive at the opposite vertex. -/
theorem apply_simpleVertex_pos (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) : 0 < ψ (simpleVertex Ψ (facet Ψ c) ψ) := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  obtain ⟨m, hm, -, hpos⟩ := hΨ.exists_pos_linear_relation hli hc hne
  have h := hpos (simpleVertex Ψ (facet Ψ c) ψ)
  rw [sum_mul_apply_eq_of_forall_ne m hψ ((hΨ.eq_simpleVertex_iff hli hc hne hψ).1 rfl)] at h
  by_contra hle
  push Not at hle
  have := mul_nonpos_of_nonneg_of_nonpos (hm ⟨ψ, hψ⟩).le hle
  linarith

/-- The opposite vertex lies in the closure of the chamber. -/
theorem simpleVertex_mem_facetClosure (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    simpleVertex Ψ (facet Ψ c) ψ ∈ facetClosure Ψ c := by
  rw [mem_facetClosure_iff_simple_nonneg hΨ hc]
  intro η hη
  by_cases h : η = ψ
  · rw [h]
    exact (hΨ.apply_simpleVertex_pos hli hc hne hψ).le
  · exact (hΨ.apply_simpleVertex_of_ne hli hc hne hψ hη h).ge

/-- The opposite vertex is a vertex: its facet is a single point. -/
theorem isVertex_simpleVertex (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    IsVertex Ψ (simpleVertex Ψ (facet Ψ c) ψ) := by
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    rw [hΨ.eq_simpleVertex_iff hli hc hne hψ]
    intro η hη hηψ
    have h := (mem_facet.1 hy) η hη.1.1
    rw [hΨ.apply_simpleVertex_of_ne hli hc hne hψ hη hηψ, sign_zero, eq_comm,
      sign_eq_zero_iff] at h
    exact h
  · rintro rfl
    exact mem_facet_self Ψ _

/-- Distinct simple affine roots have distinct opposite vertices. -/
theorem simpleVertex_injOn (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {ψ η : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) (hη : η ∈ simpleAffineRoots Ψ (facet Ψ c))
    (h : simpleVertex Ψ (facet Ψ c) ψ = simpleVertex Ψ (facet Ψ c) η) : ψ = η := by
  by_contra hψη
  have h1 := hΨ.apply_simpleVertex_pos hli hc hne hψ
  rw [h, hΨ.apply_simpleVertex_of_ne hli hc hne hη hψ hψη] at h1
  exact lt_irrefl 0 h1

/-- The vertices of a chamber are affinely independent. -/
theorem affineIndependent_simpleVertex (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) :
    AffineIndependent ℝ
      fun ψ : simpleAffineRoots Ψ (facet Ψ c) => simpleVertex Ψ (facet Ψ c) ψ := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs i
  have h1 := congrArg ((i : A →ᵃ[ℝ] ℝ).linear) hs
  rw [Finset.weightedVSub_apply, map_sum, map_zero] at h1
  simp only [map_smul, AffineMap.linearMap_vsub, vsub_eq_sub, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hw, zero_mul, sub_zero] at h1
  rw [Finset.sum_eq_single i (fun j _ hji => by
      rw [hΨ.apply_simpleVertex_of_ne hli hc hne j.2 i.2 fun h => hji (Subtype.ext h).symm,
        mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hΨ.apply_simpleVertex_pos hli hc hne i.2).ne'

/-- KP Proposition 1.3.22(6), converse direction: every vertex of the closure of the chamber
is the vertex opposite to some simple affine root. -/
theorem exists_eq_simpleVertex_of_isVertex (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {x : A}
    (hx : x ∈ facetClosure Ψ c) (hv : IsVertex Ψ x) :
    ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), x = simpleVertex Ψ (facet Ψ c) ψ := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  have hnn := (mem_facetClosure_iff_simple_nonneg hΨ hc x).1 hx
  obtain ⟨m, hm, -, hpos⟩ := hΨ.exists_pos_linear_relation hli hc hne
  obtain ⟨ψ₁, hψ₁, hψ₁x⟩ : ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 < ψ x := by
    by_contra h
    push Not at h
    have h0 : ∑ η : simpleAffineRoots Ψ (facet Ψ c), m η * (η : A →ᵃ[ℝ] ℝ) x ≤ 0 :=
      Finset.sum_nonpos fun η _ => mul_nonpos_of_nonneg_of_nonpos (hm η).le (h η η.2)
    exact (hpos x).not_ge h0
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ₂, hψ₂, hψ₂₁, hψ₂x⟩ :
      ∃ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ₁ ∧ 0 < η x := by
    have h := hcon ψ₁ hψ₁
    rw [Ne, hΨ.eq_simpleVertex_iff hli hc hne hψ₁] at h
    push Not at h
    obtain ⟨η, hη, hηψ, hηx⟩ := h
    exact ⟨η, hη, hηψ, lt_of_le_of_ne (hnn η hη) (Ne.symm hηx)⟩
  set u : V := simpleVertex Ψ (facet Ψ c) ψ₁ -ᵥ simpleVertex Ψ (facet Ψ c) ψ₂ with hu
  have hlin : ∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ₁ → η ≠ ψ₂ → η.linear u = 0 := by
    intro η hη h1 h2
    rw [hu, AffineMap.linearMap_vsub, hΨ.apply_simpleVertex_of_ne hli hc hne hψ₁ hη h1,
      hΨ.apply_simpleVertex_of_ne hli hc hne hψ₂ hη h2, vsub_eq_sub, sub_zero]
  have hu₁ : 0 < ψ₁.linear u := by
    rw [hu, AffineMap.linearMap_vsub,
      hΨ.apply_simpleVertex_of_ne hli hc hne hψ₂ hψ₁ (Ne.symm hψ₂₁), vsub_eq_sub, sub_zero]
    exact hΨ.apply_simpleVertex_pos hli hc hne hψ₁
  have happ : ∀ (ζ : A →ᵃ[ℝ] ℝ) (t : ℝ) (w : V), ζ (t • w +ᵥ x) = t * ζ.linear w + ζ x :=
    fun ζ t w => by rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
  obtain ⟨ε, hε, hp, hn⟩ := exists_pos_of_eventually
    ((eventually_sign_smul_vadd hΨ.isLocallyFiniteReflectionArrangement x u).and
      (eventually_sign_smul_vadd hΨ.isLocallyFiniteReflectionArrangement x (-u)))
  -- both points `x ± ε u` lie in the closure of the chamber
  have hmem : ∀ w : V, (∀ η ∈ simpleAffineRoots Ψ (facet Ψ c), η ≠ ψ₁ → η ≠ ψ₂ →
      η.linear w = 0) → (∀ η ∈ Ψ, η x ≠ 0 →
        SignType.sign (η (ε • w +ᵥ x)) = SignType.sign (η x)) →
      ε • w +ᵥ x ∈ facetClosure Ψ c := by
    intro w hw hsign
    rw [mem_facetClosure_iff_simple_nonneg hΨ hc]
    intro η hη
    by_cases hηx : η x = 0
    · have h1 : η ≠ ψ₁ := fun h => by rw [h] at hηx; exact hψ₁x.ne' hηx
      have h2 : η ≠ ψ₂ := fun h => by rw [h] at hηx; exact hψ₂x.ne' hηx
      rw [happ, hw η hη h1 h2, hηx, mul_zero, add_zero]
    · have h := hsign η hη.1.1 hηx
      rw [sign_pos (lt_of_le_of_ne (hnn η hη) (Ne.symm hηx)), sign_eq_one_iff] at h
      exact h.le
  have hplus := hmem u hlin hp
  have hminus := hmem (-u) (fun η hη h1 h2 => by rw [map_neg, hlin η hη h1 h2, neg_zero]) hn
  have hzero : ∀ ζ ∈ Ψ, ζ x = 0 → ζ.linear u = 0 := by
    intro ζ hζ hζx
    have h1 := mul_nonneg_of_mem_facetClosure hplus hζ
    have h2 := mul_nonneg_of_mem_facetClosure hminus hζ
    rw [happ, hζx, add_zero] at h1 h2
    rw [map_neg] at h2
    have h3 : ε * ζ.linear u * ζ c = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (mul_eq_zero.1 h4).resolve_left hε.ne'
    · exact absurd h4 (hc ζ hζ)
  have hy : ε • u +ᵥ x ∈ facet Ψ x := by
    intro ζ hζ
    by_cases hζx : ζ x = 0
    · rw [happ, hzero ζ hζ hζx, mul_zero, zero_add]
    · exact (hp ζ hζ hζx).symm
  rw [hv, Set.mem_singleton_iff] at hy
  have hεu : ε • u = 0 := by
    rw [← vsub_eq_zero_iff_eq, vadd_vsub] at hy
    exact hy
  rw [(smul_eq_zero.1 hεu).resolve_left hε.ne', map_zero] at hu₁
  exact lt_irrefl 0 hu₁

/-- KP Proposition 1.3.22(6): the vertices of the closure of the chamber are exactly the
vertices opposite to the simple affine roots. -/
theorem mem_facetClosure_and_isVertex_iff (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {x : A} :
    x ∈ facetClosure Ψ c ∧ IsVertex Ψ x ↔
      ∃ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), x = simpleVertex Ψ (facet Ψ c) ψ := by
  constructor
  · rintro ⟨hx, hv⟩
    exact hΨ.exists_eq_simpleVertex_of_isVertex hli hc hne hx hv
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨hΨ.simpleVertex_mem_facetClosure hli hc hne hψ, hΨ.isVertex_simpleVertex hli hc hne hψ⟩

/-- KP Proposition 1.3.22(6): `ψ ↦ simpleVertex Ψ C ψ` is a bijection from the simple affine
roots of the chamber `C` onto the vertices of its closure. -/
def simpleVertexEquiv (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) :
    simpleAffineRoots Ψ (facet Ψ c) ≃ {x : A // x ∈ facetClosure Ψ c ∧ IsVertex Ψ x} :=
  Equiv.ofBijective
    (fun ψ => ⟨simpleVertex Ψ (facet Ψ c) ψ,
      hΨ.simpleVertex_mem_facetClosure hli hc hne ψ.2, hΨ.isVertex_simpleVertex hli hc hne ψ.2⟩)
    ⟨fun ψ η h => Subtype.ext
        (hΨ.simpleVertex_injOn hli hc hne ψ.2 η.2 (congrArg Subtype.val h)),
      fun x => by
        obtain ⟨ψ, hψ, h⟩ := (hΨ.mem_facetClosure_and_isVertex_iff hli hc hne).1 x.2
        exact ⟨⟨ψ, hψ⟩, Subtype.ext h.symm⟩⟩

@[simp]
theorem coe_simpleVertexEquiv_apply (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (ψ : simpleAffineRoots Ψ (facet Ψ c)) :
    (hΨ.simpleVertexEquiv hli hc hne ψ : A) = simpleVertex Ψ (facet Ψ c) ψ :=
  rfl

/-- Naturality: a root-preserving automorphism stabilizing the chamber maps the vertex
opposite to `ψ` to the vertex opposite to `ψ ∘ e⁻¹`. -/
theorem apply_simpleVertex (hc : IsRegular Ψ c) (hne : Ψ.Nonempty) {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (hC : e '' facet Ψ c = facet Ψ c) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    e (simpleVertex Ψ (facet Ψ c) ψ) =
      simpleVertex Ψ (facet Ψ c) (ψ.comp (e.symm : A →ᵃ[ℝ] A)) := by
  rw [hΨ.eq_simpleVertex_iff hli hc hne (comp_symm_mem_simpleAffineRoots he hC hψ)]
  intro η hη hηne
  have hη' : η.comp (e : A →ᵃ[ℝ] A) ∈ simpleAffineRoots Ψ (facet Ψ c) := by
    have h := comp_symm_mem_simpleAffineRoots (symm_mem_rootStabilizer he)
      (symm_image_eq_of_image_eq hC) hη
    have hss : ((e.symm.symm : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A) = e := AffineMap.ext fun _ => rfl
    rwa [hss] at h
  have hne2 : η.comp (e : A →ᵃ[ℝ] A) ≠ ψ := by
    intro h
    apply hηne
    rw [← h]
    ext x
    simp
  have h := hΨ.apply_simpleVertex_of_ne hli hc hne hψ hη' hne2
  simpa using h

/-! ### Transitivity on the simple affine roots -/

/-- KP §9.2.4 and Proposition 1.3.22(6): if a group of root-preserving affine automorphisms
stabilizing a chamber has at most one fixed point in the closure of the chamber, then it acts
transitively on the simple affine roots of the chamber. -/
theorem exists_mem_eq_comp_symm_of_subsingleton (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (Γ : Subgroup (A ≃ᵃ[ℝ] A)) (hΓ : Γ ≤ rootStabilizer Ψ)
    (hΓC : ∀ e ∈ Γ, e '' facet Ψ c = facet Ψ c)
    (hfix : {y | y ∈ facetClosure Ψ c ∧ ∀ e ∈ Γ, e y = y}.Subsingleton)
    {ψ η : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ (facet Ψ c))
    (hη : η ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ e ∈ Γ, η = ψ.comp (e.symm : A →ᵃ[ℝ] A) := by
  classical
  have := (finite_simpleAffineRoots hΨ hc).fintype
  let _ : MulAction Γ (simpleAffineRoots Ψ (facet Ψ c)) :=
    { smul := fun γ ψ => ⟨(ψ : A →ᵃ[ℝ] ℝ).comp ((γ : A ≃ᵃ[ℝ] A).symm : A →ᵃ[ℝ] A),
        comp_symm_mem_simpleAffineRoots (hΓ γ.2) (hΓC γ γ.2) ψ.2⟩
      one_smul := fun ψ => Subtype.ext (AffineMap.ext fun x => rfl)
      mul_smul := fun γ₁ γ₂ ψ => Subtype.ext (AffineMap.ext fun x => rfl) }
  let p : simpleAffineRoots Ψ (facet Ψ c) → V := fun ψ => simpleVertex Ψ (facet Ψ c) ψ -ᵥ c
  let ρ : Γ → V →ᵃ[ℝ] V := fun γ =>
    ((((AffineEquiv.vaddConst ℝ c).trans (γ : A ≃ᵃ[ℝ] A)).trans
      (AffineEquiv.vaddConst ℝ c).symm : V ≃ᵃ[ℝ] V) : V →ᵃ[ℝ] V)
  have hρ : ∀ γ v, ρ γ v = (γ : A ≃ᵃ[ℝ] A) (v +ᵥ c) -ᵥ c := fun γ v => rfl
  have hp : AffineIndependent ℝ p := by
    have h := (hΨ.affineIndependent_simpleVertex hli hc hne).map'
      ((AffineEquiv.vaddConst ℝ c).symm : A →ᵃ[ℝ] V) (AffineEquiv.injective _)
    exact h
  have heq : ∀ (γ : Γ) (i : simpleAffineRoots Ψ (facet Ψ c)), ρ γ (p i) = p (γ • i) := by
    intro γ i
    rw [hρ]
    simp only [p, vsub_vadd]
    rw [hΨ.apply_simpleVertex hli hc hne (hΓ γ.2) (hΓC γ γ.2) i.2]
    rfl
  have hconv : convexHull ℝ (Set.range p) ⊆ {v : V | v +ᵥ c ∈ facetClosure Ψ c} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      show (simpleVertex Ψ (facet Ψ c) i -ᵥ c) +ᵥ c ∈ facetClosure Ψ c
      rw [vsub_vadd]
      exact hΨ.simpleVertex_mem_facetClosure hli hc hne i.2
    · intro v hv w hw a b ha hb hab
      simp only [Set.mem_ofPred_eq, mem_facetClosure_iff_simple_nonneg hΨ hc] at hv hw ⊢
      intro θ hθ
      rw [AffineMap.map_vadd, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
        vadd_eq_add]
      have h1 := hv θ hθ
      have h2 := hw θ hθ
      rw [AffineMap.map_vadd, vadd_eq_add] at h1 h2
      have : a * θ.linear v + b * θ.linear w + θ c =
          a * (θ.linear v + θ c) + b * (θ.linear w + θ c) := by
        linear_combination (-θ c) * hab
      rw [this]
      exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  have hsub : SimplexFixedPointSubsingleton p ρ := by
    rintro v ⟨hv, hvfix⟩ w ⟨hw, hwfix⟩
    have hfixA : ∀ u : V, (∀ γ : Γ, ρ γ u = u) → ∀ e ∈ Γ, e (u +ᵥ c) = u +ᵥ c := by
      intro u hu e he
      have h := hu ⟨e, he⟩
      rw [hρ] at h
      exact (eq_vadd_iff_vsub_eq _ _ _).2 h
    have := hfix ⟨hconv hv, hfixA v hvfix⟩ ⟨hconv hw, hfixA w hwfix⟩
    exact vadd_right_cancel c this
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_simplexFixedPointSubsingleton p hp ρ heq hsub
    ⟨ψ, hψ⟩ ⟨η, hη⟩
  exact ⟨γ, γ.2, (congrArg Subtype.val hγ).symm⟩

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
