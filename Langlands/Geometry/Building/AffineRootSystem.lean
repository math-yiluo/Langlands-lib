import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Sign.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Reflection

/-!
# Kaletha–Prasad affine root systems: hyperplanes, special points and facets

For a real affine space `A` under a real vector space `V` (an `AddTorsor V A`, with no chosen
origin) and a set `Ψ` of affine functionals `A →ᵃ[ℝ] ℝ`, this file defines the notions of
Kaletha–Prasad §1.3: derivative roots `Φ = ∇Ψ`, the affine root system axioms AR 1–AR 4
(Definition 1.3.1), reduced systems and `Ψ_nd`, `Ψ_nm` (Definition 1.3.4, Remark 1.3.5),
affine root hyperplanes (Definition 1.3.7), the affine reflections and the affine Weyl group
(Definition 1.3.1, Remark 1.3.2), `Ψ_x` (Proposition 1.3.35), special and extra special points
(Definition 1.3.39), and the facets, chambers and vertices of the hyperplane arrangement
(Remark 1.3.16, in the Bourbaki formulation by sign conditions that the 2024 corrections
recall for Proposition 1.3.35), facet closures, faces and positive roots (Definition 1.3.18).

Nothing here refers to a reductive group, a valuation or a building.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

open scoped Affine

universe uV uA

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-! ### Derivatives and affine root hyperplanes -/

/-- The derivative root set `Φ = ∇Ψ = {ψ̇ | ψ ∈ Ψ} ⊆ V*` (KP Definition 1.3.1, AR 1). -/
def derivativeRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set (Module.Dual ℝ V) :=
  (fun ψ : A →ᵃ[ℝ] ℝ => ψ.linear) '' Ψ

theorem mem_derivativeRoots {Ψ : Set (A →ᵃ[ℝ] ℝ)} {a : Module.Dual ℝ V} :
    a ∈ derivativeRoots Ψ ↔ ∃ ψ ∈ Ψ, ψ.linear = a :=
  Iff.rfl

theorem linear_mem_derivativeRoots {Ψ : Set (A →ᵃ[ℝ] ℝ)} {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ψ.linear ∈ derivativeRoots Ψ :=
  ⟨ψ, hψ, rfl⟩

theorem derivativeRoots_mono {Ψ Ψ' : Set (A →ᵃ[ℝ] ℝ)} (h : Ψ ⊆ Ψ') :
    derivativeRoots Ψ ⊆ derivativeRoots Ψ' :=
  Set.image_mono h

/-- The affine root hyperplane `H_ψ = {x ∈ A | ψ(x) = 0}` (KP Definition 1.3.7). -/
def hyperplane (ψ : A →ᵃ[ℝ] ℝ) : AffineSubspace ℝ A where
  carrier := {x | ψ x = 0}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ := by
    simp only [Set.mem_ofPred_eq] at h₁ h₂ h₃ ⊢
    rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub, h₁, h₂, h₃]
    simp

@[simp]
theorem mem_hyperplane {ψ : A →ᵃ[ℝ] ℝ} {x : A} : x ∈ hyperplane ψ ↔ ψ x = 0 :=
  Iff.rfl

/-- A non-constant affine functional vanishes somewhere. -/
theorem exists_apply_eq_zero {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ.linear ≠ 0) : ∃ x : A, ψ x = 0 := by
  obtain ⟨v, hv⟩ : ∃ v : V, ψ.linear v ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  obtain ⟨p⟩ : Nonempty A := inferInstance
  refine ⟨(-ψ p / ψ.linear v) • v +ᵥ p, ?_⟩
  rw [AffineMap.map_vadd, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv, vadd_eq_add,
    neg_add_cancel]

theorem hyperplane_ne_bot {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ.linear ≠ 0) : hyperplane ψ ≠ ⊥ :=
  (AffineSubspace.nonempty_iff_ne_bot _).1 (exists_apply_eq_zero hψ)

/-- The direction of `H_ψ` is the root hyperplane `ker ψ̇ ⊆ V` (KP Definition 1.3.7). -/
theorem direction_hyperplane {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ.linear ≠ 0) :
    (hyperplane ψ).direction = LinearMap.ker ψ.linear := by
  obtain ⟨p, hp⟩ := exists_apply_eq_zero hψ
  have hp' : p ∈ hyperplane ψ := hp
  ext v
  have h := AffineSubspace.vsub_right_mem_direction_iff_mem hp' (v +ᵥ p)
  rw [vadd_vsub] at h
  rw [h, mem_hyperplane, AffineMap.map_vadd, hp, vadd_eq_add, add_zero, LinearMap.mem_ker]

/-- Two affine root hyperplanes of non-constant functionals are parallel exactly when the
derivatives have the same kernel. -/
theorem hyperplane_parallel_iff {ψ ψ' : A →ᵃ[ℝ] ℝ} (hψ : ψ.linear ≠ 0) (hψ' : ψ'.linear ≠ 0) :
    hyperplane ψ ∥ hyperplane ψ' ↔ LinearMap.ker ψ.linear = LinearMap.ker ψ'.linear := by
  rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, direction_hyperplane hψ,
    direction_hyperplane hψ']
  simp [hyperplane_ne_bot hψ, hyperplane_ne_bot hψ']

/-- The hyperplane of a pulled-back functional is the preimage hyperplane. -/
theorem hyperplane_comp (ψ : A →ᵃ[ℝ] ℝ) (e : A ≃ᵃ[ℝ] A) :
    hyperplane (ψ.comp (e : A →ᵃ[ℝ] A)) = (hyperplane ψ).comap (e : A →ᵃ[ℝ] A) :=
  SetLike.ext fun _ => Iff.rfl

/-- Parallelism of affine subspaces is preserved by an affine automorphism. -/
theorem parallel_map_affineEquiv {s₁ s₂ : AffineSubspace ℝ A} (h : s₁ ∥ s₂) (e : A ≃ᵃ[ℝ] A) :
    s₁.map (e : A →ᵃ[ℝ] A) ∥ s₂.map (e : A →ᵃ[ℝ] A) := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨e.linear v, ?_⟩
  rw [AffineSubspace.map_map, AffineSubspace.map_map]
  congr 1
  ext x
  simp [AffineEquiv.map_vadd]

theorem parallel_comap_affineEquiv {s₁ s₂ : AffineSubspace ℝ A} (h : s₁ ∥ s₂)
    (e : A ≃ᵃ[ℝ] A) : s₁.comap (e : A →ᵃ[ℝ] A) ∥ s₂.comap (e : A →ᵃ[ℝ] A) := by
  rw [← AffineSubspace.map_symm, ← AffineSubspace.map_symm]
  exact parallel_map_affineEquiv h e.symm

/-! ### Reduced systems -/

/-- `Ψ` is reduced if `ψ ∈ Ψ` implies `2ψ ∉ Ψ` (KP Definition 1.3.4). -/
def IsReduced (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop :=
  ∀ ψ ∈ Ψ, (2 : ℝ) • ψ ∉ Ψ

/-- The non-divisible affine roots `Ψ_nd = {ψ ∈ Ψ | ψ/2 ∉ Ψ}` (KP Remark 1.3.5). -/
def nonDivisibleRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ ∈ Ψ | (2 : ℝ)⁻¹ • ψ ∉ Ψ}

/-- The non-multipliable affine roots `Ψ_nm = {ψ ∈ Ψ | 2ψ ∉ Ψ}` (KP Remark 1.3.5). -/
def nonMultipliableRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ ∈ Ψ | (2 : ℝ) • ψ ∉ Ψ}

theorem nonDivisibleRoots_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) : nonDivisibleRoots Ψ ⊆ Ψ :=
  fun _ h => h.1

theorem nonMultipliableRoots_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) : nonMultipliableRoots Ψ ⊆ Ψ :=
  fun _ h => h.1

theorem nonMultipliableRoots_eq_self_iff {Ψ : Set (A →ᵃ[ℝ] ℝ)} :
    nonMultipliableRoots Ψ = Ψ ↔ IsReduced Ψ := by
  refine ⟨fun h ψ hψ => ?_, fun h => ?_⟩
  · rw [← h] at hψ
    exact hψ.2
  · exact Set.Subset.antisymm (nonMultipliableRoots_subset Ψ) fun ψ hψ => ⟨hψ, h ψ hψ⟩

theorem nonDivisibleRoots_eq_self_iff {Ψ : Set (A →ᵃ[ℝ] ℝ)} :
    nonDivisibleRoots Ψ = Ψ ↔ IsReduced Ψ := by
  refine ⟨fun h ψ hψ h2 => ?_, fun h => ?_⟩
  · rw [← h] at h2
    refine h2.2 ?_
    rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  · refine Set.Subset.antisymm (nonDivisibleRoots_subset Ψ) fun ψ hψ => ⟨hψ, fun h2 => ?_⟩
    refine h _ h2 ?_
    rwa [smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

/-! ### Affine reflections and the affine Weyl group -/

/-- `v ∈ V` is a coroot vector for `ψ` in the sense of AR 2: `ψ̇(v) = 2` and the reflection
`η ↦ η - η̇(v) ψ` of `A*` preserves `Ψ` (KP Definition 1.3.1). -/
def IsCoroot (Ψ : Set (A →ᵃ[ℝ] ℝ)) (ψ : A →ᵃ[ℝ] ℝ) (v : V) : Prop :=
  ψ.linear v = 2 ∧ ∀ η ∈ Ψ, η - η.linear v • ψ ∈ Ψ

/-- The reflection `x ↦ x - ψ(x) v` of `A` for `ψ̇(v) = 2` (KP Remark 1.3.2(3)); its
derivative is `Module.reflection`. -/
def affineReflection (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2) : A ≃ᵃ[ℝ] A where
  toFun x := (-ψ x) • v +ᵥ x
  invFun x := (-ψ x) • v +ᵥ x
  left_inv x := by
    have h : ψ ((-ψ x) • v +ᵥ x) = -ψ x := by
      rw [AffineMap.map_vadd, map_smul, hv, smul_eq_mul, vadd_eq_add]
      ring
    simp only
    rw [h, vadd_vadd, ← add_smul, neg_neg, add_neg_cancel, zero_smul, zero_vadd]
  right_inv x := by
    have h : ψ ((-ψ x) • v +ᵥ x) = -ψ x := by
      rw [AffineMap.map_vadd, map_smul, hv, smul_eq_mul, vadd_eq_add]
      ring
    simp only
    rw [h, vadd_vadd, ← add_smul, neg_neg, add_neg_cancel, zero_smul, zero_vadd]
  linear := Module.reflection hv
  map_vadd' p w := by
    show (-ψ (w +ᵥ p)) • v +ᵥ (w +ᵥ p) = Module.reflection hv w +ᵥ ((-ψ p) • v +ᵥ p)
    rw [Module.reflection_apply, AffineMap.map_vadd, vadd_vadd, vadd_vadd, vadd_eq_add]
    congr 1
    rw [neg_add, add_smul, neg_smul, neg_smul]
    abel

section Reflection

variable (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2)

@[simp]
theorem affineReflection_apply (x : A) : affineReflection ψ hv x = (-ψ x) • v +ᵥ x :=
  rfl

@[simp]
theorem affineReflection_linear : (affineReflection ψ hv).linear = Module.reflection hv :=
  rfl

/-- `ψ(r_ψ x) = -ψ(x)`. -/
theorem apply_affineReflection (x : A) : ψ (affineReflection ψ hv x) = -ψ x := by
  rw [affineReflection_apply, AffineMap.map_vadd, map_smul, hv, smul_eq_mul, vadd_eq_add]
  ring

/-- The reflection fixes the hyperplane `H_ψ` pointwise. -/
theorem affineReflection_apply_of_mem {x : A} (hx : x ∈ hyperplane ψ) :
    affineReflection ψ hv x = x := by
  rw [affineReflection_apply, (mem_hyperplane).1 hx, neg_zero, zero_smul, zero_vadd]

theorem affineReflection_involutive : Function.Involutive (affineReflection ψ hv) :=
  (affineReflection ψ hv).left_inv

theorem affineReflection_mul_self : affineReflection ψ hv * affineReflection ψ hv = 1 :=
  AffineEquiv.ext fun x => affineReflection_involutive ψ hv x

/-- Pulling back by `r_ψ` is KP's reflection `η ↦ η - η̇(v) ψ` of `A*` (AR 2). -/
theorem comp_affineReflection (η : A →ᵃ[ℝ] ℝ) :
    η.comp (affineReflection ψ hv : A →ᵃ[ℝ] A) = η - η.linear v • ψ := by
  ext x
  simp only [AffineMap.coe_comp, AffineEquiv.coe_toAffineMap, Function.comp_apply,
    affineReflection_apply, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add,
    AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply]
  ring

end Reflection

/-- The affine automorphisms of `A` whose pull-back permutes `Ψ`. -/
def rootStabilizer (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Subgroup (A ≃ᵃ[ℝ] A) where
  carrier := {e | ∀ η : A →ᵃ[ℝ] ℝ, η.comp (e : A →ᵃ[ℝ] A) ∈ Ψ ↔ η ∈ Ψ}
  one_mem' η := by
    have : η.comp ((1 : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A) = η := AffineMap.ext fun _ => rfl
    rw [this]
  mul_mem' {e₁ e₂} h₁ h₂ η := by
    have : η.comp ((e₁ * e₂ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A) =
        (η.comp (e₁ : A →ᵃ[ℝ] A)).comp (e₂ : A →ᵃ[ℝ] A) := AffineMap.ext fun _ => rfl
    rw [this, h₂, h₁]
  inv_mem' {e} h η := by
    have : (η.comp ((e⁻¹ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A)).comp (e : A →ᵃ[ℝ] A) = η :=
      AffineMap.ext fun x => by
        simp [AffineEquiv.inv_def]
    rw [← h, this]

theorem mem_rootStabilizer {Ψ : Set (A →ᵃ[ℝ] ℝ)} {e : A ≃ᵃ[ℝ] A} :
    e ∈ rootStabilizer Ψ ↔ ∀ η : A →ᵃ[ℝ] ℝ, η.comp (e : A →ᵃ[ℝ] A) ∈ Ψ ↔ η ∈ Ψ :=
  Iff.rfl

/-- The affine Weyl group `W(Ψ)`: the subgroup of affine automorphisms of `A` generated by the
reflections `r_ψ` attached to coroot vectors of `ψ ∈ Ψ` (KP Definition 1.3.1, Remark 1.3.2). -/
def affineWeylGroup (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Subgroup (A ≃ᵃ[ℝ] A) :=
  Subgroup.closure
    {e | ∃ ψ ∈ Ψ, ∃ (v : V) (hv : IsCoroot Ψ ψ v), e = affineReflection ψ hv.1}

theorem affineReflection_mem_affineWeylGroup {Ψ : Set (A →ᵃ[ℝ] ℝ)} {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ Ψ) {v : V} (hv : IsCoroot Ψ ψ v) :
    affineReflection ψ hv.1 ∈ affineWeylGroup Ψ :=
  Subgroup.subset_closure ⟨ψ, hψ, v, hv, rfl⟩

theorem affineReflection_mem_rootStabilizer {Ψ : Set (A →ᵃ[ℝ] ℝ)} {ψ : A →ᵃ[ℝ] ℝ}
    {v : V} (hv : IsCoroot Ψ ψ v) : affineReflection ψ hv.1 ∈ rootStabilizer Ψ := by
  intro η
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := hv.2 _ h
    rwa [← comp_affineReflection ψ hv.1, AffineMap.comp_assoc,
      show ((affineReflection ψ hv.1 : A →ᵃ[ℝ] A).comp (affineReflection ψ hv.1 : A →ᵃ[ℝ] A))
        = AffineMap.id ℝ A from AffineMap.ext fun x => affineReflection_involutive ψ hv.1 x,
      AffineMap.comp_id] at h2
  · rw [comp_affineReflection ψ hv.1]
    exact hv.2 η h

/-- Every element of `W(Ψ)` permutes `Ψ` by pull-back. -/
theorem affineWeylGroup_le_rootStabilizer (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    affineWeylGroup Ψ ≤ rootStabilizer Ψ :=
  (Subgroup.closure_le _).2 fun _ ⟨_, _, _, hv, he⟩ =>
    he ▸ affineReflection_mem_rootStabilizer hv

/-! ### The affine root system axioms -/

/-- `Ψ ⊆ A*` is an affine root system (KP Definition 1.3.1):

* AR 1: `Ψ` spans `A*`, consists of non-constant functionals, and `Φ = ∇Ψ` is finite;
* AR 2: every `ψ ∈ Ψ` has a coroot vector `ψ̇∨ ∈ V` (`IsCoroot`);
* AR 3: `ψ̇(η̇∨) ∈ ℤ` for all `ψ, η ∈ Ψ`;
* AR 4 (as corrected in 2024): for each `a ∈ Φ`, `{ψ ∈ Ψ | ψ̇ = a}` is infinite and has no
  accumulation point; the latter is stated as: for each `ψ ∈ Ψ` and `M`, only finitely many
  `η ∈ Ψ` with `η̇ = ψ̇` satisfy `|η - ψ| ≤ M`. -/
structure IsAffineRootSystem (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop where
  span_eq_top : Submodule.span ℝ Ψ = ⊤
  linear_ne_zero : ∀ ψ ∈ Ψ, ψ.linear ≠ 0
  finite_derivativeRoots : (derivativeRoots Ψ).Finite
  exists_isCoroot : ∀ ψ ∈ Ψ, ∃ v : V, IsCoroot Ψ ψ v
  coroot_integral : ∀ ψ ∈ Ψ, ∀ η ∈ Ψ, ∀ v : V, IsCoroot Ψ η v → ∃ n : ℤ, ψ.linear v = n
  infinite_fiber : ∀ ψ ∈ Ψ, {η | η ∈ Ψ ∧ η.linear = ψ.linear}.Infinite
  finite_bounded : ∀ ψ ∈ Ψ, ∀ M : ℝ,
    {η | η ∈ Ψ ∧ η.linear = ψ.linear ∧ ∀ x : A, |η x - ψ x| ≤ M}.Finite

/-- An affine root system is stable under negation (AR 2 applied to `ψ` itself). -/
theorem IsAffineRootSystem.neg_mem {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystem Ψ)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) : -ψ ∈ Ψ := by
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  have h := hv.2 ψ hψ
  rwa [hv.1, two_smul, sub_add_cancel_left] at h

/-! ### Vanishing roots, special and extra special points -/

/-- `Ψ_x = {ψ ∈ Ψ | ψ(x) = 0}` (KP Proposition 1.3.35). -/
def vanishingRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ψ x = 0}

@[simp]
theorem mem_vanishingRoots {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x : A} {ψ : A →ᵃ[ℝ] ℝ} :
    ψ ∈ vanishingRoots Ψ x ↔ ψ ∈ Ψ ∧ ψ x = 0 :=
  Iff.rfl

theorem vanishingRoots_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : vanishingRoots Ψ x ⊆ Ψ :=
  fun _ h => h.1

theorem mem_vanishingRoots_iff_mem_hyperplane {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x : A}
    {ψ : A →ᵃ[ℝ] ℝ} : ψ ∈ vanishingRoots Ψ x ↔ ψ ∈ Ψ ∧ x ∈ hyperplane ψ :=
  Iff.rfl

/-- `x` is special if every affine root hyperplane is parallel to an affine root hyperplane
through `x` (KP Definition 1.3.39(1)). -/
def IsSpecialPoint (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Prop :=
  ∀ ψ ∈ Ψ, ∃ ψ' ∈ vanishingRoots Ψ x, hyperplane ψ ∥ hyperplane ψ'

/-- For non-constant roots, special means: every root derivative has the kernel of the
derivative of some root vanishing at `x`. -/
theorem isSpecialPoint_iff_ker {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : ∀ ψ ∈ Ψ, ψ.linear ≠ 0) (x : A) :
    IsSpecialPoint Ψ x ↔
      ∀ ψ ∈ Ψ, ∃ ψ' ∈ vanishingRoots Ψ x, LinearMap.ker ψ.linear = LinearMap.ker ψ'.linear :=
  forall₂_congr fun ψ hψ => exists_congr fun ψ' => and_congr_right fun hψ' =>
    hyperplane_parallel_iff (hΨ ψ hψ) (hΨ ψ' hψ'.1)

/-- A base of a finite root system `Φ` in `V*` (Bourbaki, Lie VI §1 no. 6, Definition 2):
a subset `B ⊆ Φ` that is a basis of `V*` such that every root is an integral combination of
`B` with coefficients all of the same sign. -/
structure IsRootBasis (Φ B : Set (Module.Dual ℝ V)) : Prop where
  subset : B ⊆ Φ
  linearIndependent : LinearIndependent ℝ (fun b : B => (b : Module.Dual ℝ V))
  span_eq_top : Submodule.span ℝ B = ⊤
  exists_coeffs : ∀ a ∈ Φ, ∃ c : B →₀ ℤ, ((∀ b, 0 ≤ c b) ∨ (∀ b, c b ≤ 0)) ∧
    a = Finsupp.linearCombination ℤ (fun b : B => (b : Module.Dual ℝ V)) c

/-- `x` is extra special if some roots vanishing at `x` have derivatives forming a basis of
`Φ = ∇Ψ` (KP Definition 1.3.39(2)). -/
def IsExtraSpecialPoint (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Prop :=
  ∃ Ψ₀ ⊆ vanishingRoots Ψ x, IsRootBasis (derivativeRoots Ψ) (derivativeRoots Ψ₀)

/-! ### Facets, chambers and vertices -/

/-- Bourbaki's facet relation for the hyperplanes `H_ψ`: `x` and `y` lie on the same
hyperplanes and on the same open side of every other one, i.e. `sign ψ(x) = sign ψ(y)` for
every `ψ ∈ Ψ` (KP Remark 1.3.16 and the 2024 corrections to Proposition 1.3.35, recalling
Bourbaki, Lie V §1 no. 2). -/
def facetRel (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x y : A) : Prop :=
  ∀ ψ ∈ Ψ, SignType.sign (ψ x) = SignType.sign (ψ y)

theorem facetRel_equivalence (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Equivalence (facetRel Ψ) :=
  ⟨fun _ _ _ => rfl, fun h ψ hψ => (h ψ hψ).symm, fun h₁ h₂ ψ hψ => (h₁ ψ hψ).trans (h₂ ψ hψ)⟩

/-- The facet relation as a setoid; facets are its classes. -/
def facetSetoid (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Setoid A :=
  ⟨facetRel Ψ, facetRel_equivalence Ψ⟩

/-- The facet of `A` containing `x`. -/
def facet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Set A :=
  {y | facetRel Ψ x y}

/-- `F` is a facet: a class of the facet relation. -/
def IsFacet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (F : Set A) : Prop :=
  ∃ x, facet Ψ x = F

/-- `C` is a chamber: the facet of a point lying on no affine root hyperplane. -/
def IsChamber (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Prop :=
  ∃ x, (∀ ψ ∈ Ψ, ψ x ≠ 0) ∧ facet Ψ x = C

/-- `x` is a vertex: its facet is the single point `x` (a facet of dimension `0`). -/
def IsVertex (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Prop :=
  facet Ψ x = {x}

/-- The closure of the facet of `x`, by the formula `⋂_{x ∈ H} H ∩ ⋂_{x ∉ H} closure D_H(x)`
recalled in the 2024 corrections to KP Proposition 1.3.35: `y` lies on every root hyperplane
through `x` and in the closed side containing `x` of every other one. -/
def facetClosure (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Set A :=
  {y | ∀ ψ ∈ Ψ, SignType.sign (ψ y) = 0 ∨ SignType.sign (ψ y) = SignType.sign (ψ x)}

/-- `F'` is a face of `F`: a facet contained in the closure of the facet `F` (KP Remark 1.3.16). -/
def IsFaceOf (Ψ : Set (A →ᵃ[ℝ] ℝ)) (F' F : Set A) : Prop :=
  IsFacet Ψ F' ∧ ∃ x, facet Ψ x = F ∧ F' ⊆ facetClosure Ψ x

/-- The affine roots positive on `C`, `Ψ(C)^+` (KP Definition 1.3.18). -/
def positiveRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ∀ x ∈ C, 0 < ψ x}

/-- The affine roots negative on `C`, `Ψ(C)^-` (KP Definition 1.3.18). -/
def negativeRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ∀ x ∈ C, ψ x < 0}

section Facets

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x y : A}

@[simp]
theorem mem_facet : y ∈ facet Ψ x ↔ facetRel Ψ x y :=
  Iff.rfl

theorem mem_facet_self (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : x ∈ facet Ψ x :=
  (facetRel_equivalence Ψ).refl x

theorem facet_eq_facet_iff : facet Ψ x = facet Ψ y ↔ facetRel Ψ x y := by
  refine ⟨fun h => ?_, fun h => Set.ext fun z => ?_⟩
  · have : y ∈ facet Ψ x := h ▸ mem_facet_self Ψ y
    exact this
  · exact ⟨fun hz => (facetRel_equivalence Ψ).trans ((facetRel_equivalence Ψ).symm h) hz,
      fun hz => (facetRel_equivalence Ψ).trans h hz⟩

theorem facet_eq_of_mem (h : y ∈ facet Ψ x) : facet Ψ y = facet Ψ x :=
  facet_eq_facet_iff.2 ((facetRel_equivalence Ψ).symm h)

theorem isFacet_facet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : IsFacet Ψ (facet Ψ x) :=
  ⟨x, rfl⟩

theorem IsChamber.isFacet {C : Set A} (h : IsChamber Ψ C) : IsFacet Ψ C :=
  let ⟨x, _, hx⟩ := h
  ⟨x, hx⟩

/-- `Ψ_x` depends only on the facet of `x` (KP Proposition 1.3.35(3)). -/
theorem vanishingRoots_eq_of_facetRel (h : facetRel Ψ x y) :
    vanishingRoots Ψ x = vanishingRoots Ψ y := by
  ext ψ
  refine and_congr_right fun hψ => ?_
  rw [← sign_eq_zero_iff, h ψ hψ, sign_eq_zero_iff]

theorem facet_subset_hyperplane {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ vanishingRoots Ψ x) :
    facet Ψ x ⊆ hyperplane ψ := fun y hy => by
  have := (vanishingRoots_eq_of_facetRel hy ▸ hψ : ψ ∈ vanishingRoots Ψ y)
  exact this.2

theorem facet_subset_facetClosure (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    facet Ψ x ⊆ facetClosure Ψ x :=
  fun _ hy ψ hψ => Or.inr (hy ψ hψ).symm

theorem mem_facetClosure_self (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : x ∈ facetClosure Ψ x :=
  facet_subset_facetClosure Ψ x (mem_facet_self Ψ x)

/-- The closure of a facet depends only on the facet. -/
theorem facetClosure_eq_of_facetRel (h : facetRel Ψ x y) :
    facetClosure Ψ x = facetClosure Ψ y := by
  ext z
  exact forall₂_congr fun ψ hψ => by rw [h ψ hψ]

/-- A facet lies in the closure of the facet of `x` as soon as one of its points does. -/
theorem facet_subset_facetClosure_iff : facet Ψ y ⊆ facetClosure Ψ x ↔ y ∈ facetClosure Ψ x := by
  refine ⟨fun h => h (mem_facet_self Ψ y), fun h z hz ψ hψ => ?_⟩
  rw [← hz ψ hψ]
  exact h ψ hψ

/-- `y ≺ x` and `z ≺ y` give `z ≺ x` (KP Notation 1.3.34). -/
theorem mem_facetClosure_trans {z : A} (hy : y ∈ facetClosure Ψ x) (hz : z ∈ facetClosure Ψ y) :
    z ∈ facetClosure Ψ x := fun ψ hψ => by
  rcases hz ψ hψ with h | h
  · exact Or.inl h
  · rcases hy ψ hψ with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')

/-- Every root is positive or negative on a chamber (KP after Definition 1.3.18). -/
theorem IsChamber.mem_positiveRoots_or_mem_negativeRoots {C : Set A} (hC : IsChamber Ψ C)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) : ψ ∈ positiveRoots Ψ C ∨ ψ ∈ negativeRoots Ψ C := by
  obtain ⟨x, hx, rfl⟩ := hC
  rcases lt_or_gt_of_ne (hx ψ hψ) with h | h
  · refine Or.inr ⟨hψ, fun y hy => ?_⟩
    have := hy ψ hψ
    rw [sign_neg h, eq_comm, sign_eq_neg_one_iff] at this
    exact this
  · refine Or.inl ⟨hψ, fun y hy => ?_⟩
    have := hy ψ hψ
    rw [sign_pos h, eq_comm, sign_eq_one_iff] at this
    exact this

/-- Being special depends only on the facet. -/
theorem isSpecialPoint_congr (h : facetRel Ψ x y) :
    IsSpecialPoint Ψ x ↔ IsSpecialPoint Ψ y := by
  unfold IsSpecialPoint
  rw [vanishingRoots_eq_of_facetRel h]

/-- Being extra special depends only on the facet. -/
theorem isExtraSpecialPoint_congr (h : facetRel Ψ x y) :
    IsExtraSpecialPoint Ψ x ↔ IsExtraSpecialPoint Ψ y := by
  unfold IsExtraSpecialPoint
  rw [vanishingRoots_eq_of_facetRel h]

end Facets

/-! ### Transport by root-preserving automorphisms -/

section Transport

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} {e : A ≃ᵃ[ℝ] A}

theorem comp_mem_iff (he : e ∈ rootStabilizer Ψ) (η : A →ᵃ[ℝ] ℝ) :
    η.comp (e : A →ᵃ[ℝ] A) ∈ Ψ ↔ η ∈ Ψ :=
  he η

theorem comp_inv_comp (e : A ≃ᵃ[ℝ] A) (η : A →ᵃ[ℝ] ℝ) :
    (η.comp ((e⁻¹ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A)).comp (e : A →ᵃ[ℝ] A) = η :=
  AffineMap.ext fun x => by simp [AffineEquiv.inv_def]

theorem mem_vanishingRoots_apply (he : e ∈ rootStabilizer Ψ) (x : A) (η : A →ᵃ[ℝ] ℝ) :
    η ∈ vanishingRoots Ψ (e x) ↔ η.comp (e : A →ᵃ[ℝ] A) ∈ vanishingRoots Ψ x := by
  simp only [mem_vanishingRoots, comp_mem_iff he]
  rfl

theorem facetRel_apply_iff (he : e ∈ rootStabilizer Ψ) (x y : A) :
    facetRel Ψ (e x) (e y) ↔ facetRel Ψ x y := by
  refine ⟨fun h ψ hψ => ?_, fun h ψ hψ => ?_⟩
  · have hψ' : ψ.comp ((e⁻¹ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A) ∈ Ψ :=
      (comp_mem_iff (inv_mem he) ψ).2 hψ
    have := h _ hψ'
    simpa [AffineEquiv.inv_def] using this
  · exact h _ ((comp_mem_iff he ψ).2 hψ)

/-- A root-preserving affine automorphism maps special points to special points. -/
theorem IsSpecialPoint.of_apply (he : e ∈ rootStabilizer Ψ) {x : A}
    (h : IsSpecialPoint Ψ (e x)) : IsSpecialPoint Ψ x := by
  intro ψ hψ
  have hφ : ψ.comp ((e⁻¹ : A ≃ᵃ[ℝ] A) : A →ᵃ[ℝ] A) ∈ Ψ := (comp_mem_iff (inv_mem he) ψ).2 hψ
  obtain ⟨φ', hφ', hpar⟩ := h _ hφ
  refine ⟨φ'.comp (e : A →ᵃ[ℝ] A), (mem_vanishingRoots_apply he x φ').1 hφ', ?_⟩
  have := parallel_comap_affineEquiv hpar e
  rwa [← hyperplane_comp, ← hyperplane_comp, comp_inv_comp] at this

theorem isSpecialPoint_apply_iff (he : e ∈ rootStabilizer Ψ) (x : A) :
    IsSpecialPoint Ψ (e x) ↔ IsSpecialPoint Ψ x := by
  refine ⟨IsSpecialPoint.of_apply he, fun h => ?_⟩
  refine IsSpecialPoint.of_apply (inv_mem he) ?_
  simpa [AffineEquiv.inv_def] using h

end Transport

end Langlands.Geometry.Building.AffineRootSystem
