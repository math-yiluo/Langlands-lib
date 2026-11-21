import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Scalar functions with poles along finitely many hyperplanes

Local form of the singularities in Bernstein–Lapid, Theorem 2.3 (6) and the Corollary of §8.6:
a scalar function `f` on a finite-dimensional complex vector space `X`, given on a domain `D`,
has poles along the hyperplanes of a family of linear forms `L β`, `β ∈ R`, when near every
point `λ₀`, in every linear coordinate system, a power of a finite product of the forms
`λ ↦ L β (λ - λ₀)` times `f` agrees on `D` with a holomorphic function.

The module proves the closure properties used to assemble such functions (sums, products,
holomorphic multiples, pullback along linear maps, proportional forms, transfer from a dense
subdomain), the choice of one root set, exponent and neighborhood for finitely many functions
and for every finite linear combination of them, the passage between expansions
`∑ i, c i λ * ψ i g` and their coefficients through finitely many points `g`, and the
one-variable criterion: a meromorphic function invariant under translation by the kernel of
one form `ℓ` has poles along the hyperplanes of `ℓ`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter
open scoped Topology Manifold

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}

/-- Local pole data at the point `s₀` of the coordinates `e`: on the open neighborhood `W` of
`s₀`, the function `(∏ β ∈ S, L β (e s - e s₀)) ^ m * f (e s)` agrees on `e ⁻¹' D` with a
function complex differentiable on `W`. -/
def HasRootPoleDataAt (L : ι → X →ₗ[ℂ] ℂ) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    (s₀ : Fin n → ℂ) (f : X → ℂ) (D : Set X) (S : Finset ι) (m : ℕ)
    (W : Set (Fin n → ℂ)) : Prop :=
  IsOpen W ∧ s₀ ∈ W ∧ ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
    ∀ s ∈ W, e s ∈ D → h s = (∏ β ∈ S, L β (e s - e s₀)) ^ m * f (e s)

/-- A scalar function `f` on `X`, considered on the domain `D`, has poles along the
hyperplanes of the linear forms `L β`, `β ∈ R`, when for every linear coordinate system
`e : ℂⁿ ≃ X` and every point `s₀` there are finitely many indices `S ⊆ R`, an exponent `m` and
an open neighborhood `W` of `s₀` such that `(∏ β ∈ S, L β (e s - e s₀)) ^ m * f (e s)` agrees
for `e s ∈ D` with a function complex differentiable on `W`. -/
def HasRootHyperplanePoles (L : ι → X →ₗ[ℂ] ℂ) (R : Set ι) (f : X → ℂ) (D : Set X) :
    Prop :=
  ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ),
    ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin n → ℂ)),
      (S : Set ι) ⊆ R ∧ HasRootPoleDataAt L e s₀ f D S m W

section Basic

variable {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {n : ℕ} {e : (Fin n → ℂ) ≃ₗ[ℂ] X}
  {s₀ : Fin n → ℂ} {f f₁ f₂ : X → ℂ} {D D' : Set X}

/-- An affine form `s ↦ ℓ (e s - e s₀)` on `ℂⁿ` is complex differentiable. -/
theorem differentiable_linearForm_sub (ℓ : X →ₗ[ℂ] ℂ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    (s₀ : Fin n → ℂ) : Differentiable ℂ (fun s => ℓ (e s - e s₀)) := by
  have h : (fun s => ℓ (e s - e s₀)) =
      fun s => LinearMap.toContinuousLinearMap (ℓ ∘ₗ e.toLinearMap) s - ℓ (e s₀) := by
    funext s
    simp [map_sub]
  rw [h]
  exact (ContinuousLinearMap.differentiable _).sub_const _

/-- The product of affine root forms is complex differentiable. -/
theorem differentiable_prod_linearForm_sub (S : Finset ι) (L : ι → X →ₗ[ℂ] ℂ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ) :
    Differentiable ℂ (fun s => ∏ β ∈ S, L β (e s - e s₀)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    simp only [Finset.prod_insert hj]
    exact (differentiable_linearForm_sub (L j) e s₀).mul ih

/-- Pole data may be enlarged: a larger index set, a larger exponent and a smaller open
neighborhood still work. -/
theorem HasRootPoleDataAt.enlarge {S S' : Finset ι} {m m' : ℕ} {W W' : Set (Fin n → ℂ)}
    (hd : HasRootPoleDataAt L e s₀ f D S m W) (hS : S ⊆ S') (hm : m ≤ m')
    (hW' : IsOpen W') (hs₀ : s₀ ∈ W') (hWW : W' ⊆ W) :
    HasRootPoleDataAt L e s₀ f D S' m' W' := by
  classical
  obtain ⟨-, -, h, hh, hEq⟩ := hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨hW', hs₀, fun s => (∏ β ∈ S' \ S, L β (e s - e s₀)) ^ (m + k) *
    (∏ β ∈ S, L β (e s - e s₀)) ^ k * h s, ?_, ?_⟩
  · exact ((((differentiable_prod_linearForm_sub _ L e s₀).pow _).mul
      ((differentiable_prod_linearForm_sub _ L e s₀).pow _)).differentiableOn.mul
        (hh.mono hWW))
  · intro s hs hsD
    dsimp only
    rw [hEq s (hWW hs) hsD, ← Finset.prod_sdiff hS]
    ring

/-- Pole data for `f` on `D` are pole data on any smaller domain. -/
theorem HasRootPoleDataAt.mono {S : Finset ι} {m : ℕ} {W : Set (Fin n → ℂ)}
    (hd : HasRootPoleDataAt L e s₀ f D S m W) (hD : D' ⊆ D) :
    HasRootPoleDataAt L e s₀ f D' S m W := by
  obtain ⟨hW, hs₀, h, hh, hEq⟩ := hd
  exact ⟨hW, hs₀, h, hh, fun s hs hsD => hEq s hs (hD hsD)⟩

/-- Pole data are unchanged when `f` is modified off the domain. -/
theorem HasRootPoleDataAt.congr {S : Finset ι} {m : ℕ} {W : Set (Fin n → ℂ)}
    (hd : HasRootPoleDataAt L e s₀ f₁ D S m W) (hf : ∀ x ∈ D, f₁ x = f₂ x) :
    HasRootPoleDataAt L e s₀ f₂ D S m W := by
  obtain ⟨hW, hs₀, h, hh, hEq⟩ := hd
  exact ⟨hW, hs₀, h, hh, fun s hs hsD => by rw [hEq s hs hsD, hf _ hsD]⟩

theorem HasRootPoleDataAt.add {S : Finset ι} {m : ℕ} {W : Set (Fin n → ℂ)}
    (h₁ : HasRootPoleDataAt L e s₀ f₁ D S m W) (h₂ : HasRootPoleDataAt L e s₀ f₂ D S m W) :
    HasRootPoleDataAt L e s₀ (f₁ + f₂) D S m W := by
  obtain ⟨hW, hs₀, a, ha, haEq⟩ := h₁
  obtain ⟨-, -, b, hb, hbEq⟩ := h₂
  refine ⟨hW, hs₀, a + b, ha.add hb, fun s hs hsD => ?_⟩
  simp only [Pi.add_apply, haEq s hs hsD, hbEq s hs hsD]
  ring

theorem HasRootPoleDataAt.const_mul {S : Finset ι} {m : ℕ} {W : Set (Fin n → ℂ)}
    (hd : HasRootPoleDataAt L e s₀ f D S m W) (c : ℂ) :
    HasRootPoleDataAt L e s₀ (fun x => c * f x) D S m W := by
  obtain ⟨hW, hs₀, a, ha, haEq⟩ := hd
  refine ⟨hW, hs₀, fun s => c * a s, (differentiableOn_const c).mul ha, fun s hs hsD => ?_⟩
  simp only [haEq s hs hsD]
  ring

theorem HasRootPoleDataAt.mul_const {S : Finset ι} {m : ℕ} {W : Set (Fin n → ℂ)}
    (hd : HasRootPoleDataAt L e s₀ f D S m W) (c : ℂ) :
    HasRootPoleDataAt L e s₀ (fun x => f x * c) D S m W := by
  simpa [mul_comm] using hd.const_mul c

theorem HasRootPoleDataAt.mul {S₁ S₂ : Finset ι} {m₁ m₂ : ℕ} {W₁ W₂ : Set (Fin n → ℂ)}
    (h₁ : HasRootPoleDataAt L e s₀ f₁ D S₁ m₁ W₁)
    (h₂ : HasRootPoleDataAt L e s₀ f₂ D S₂ m₂ W₂) [DecidableEq ι] :
    HasRootPoleDataAt L e s₀ (f₁ * f₂) D (S₁ ∪ S₂) (m₁ + m₂) (W₁ ∩ W₂) := by
  have hW : IsOpen (W₁ ∩ W₂) := h₁.1.inter h₂.1
  have hs : s₀ ∈ W₁ ∩ W₂ := ⟨h₁.2.1, h₂.2.1⟩
  obtain ⟨-, -, a, ha, haEq⟩ :=
    h₁.enlarge Finset.subset_union_left le_rfl hW hs inter_subset_left
  obtain ⟨-, -, b, hb, hbEq⟩ :=
    h₂.enlarge Finset.subset_union_right le_rfl hW hs inter_subset_right
  refine ⟨hW, hs, a * b, ha.mul hb, fun s hs' hsD => ?_⟩
  simp only [Pi.mul_apply, haEq s hs' hsD, hbEq s hs' hsD]
  ring

/-- Pole data for a finite family on one common index set, exponent and neighborhood give
pole data for every linear combination. -/
theorem HasRootPoleDataAt.sum_mul {κ : Type*} (T : Finset κ) {S : Finset ι} {m : ℕ}
    {W : Set (Fin n → ℂ)} (hW : IsOpen W) (hs₀ : s₀ ∈ W) {c : κ → X → ℂ}
    (hc : ∀ i ∈ T, HasRootPoleDataAt L e s₀ (c i) D S m W) (a : κ → ℂ) :
    HasRootPoleDataAt L e s₀ (fun x => ∑ i ∈ T, c i x * a i) D S m W := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨hW, hs₀, fun _ => 0, differentiableOn_const 0, fun s _ _ => by simp⟩
  | insert j T hj ih =>
    have h1 := (hc j (Finset.mem_insert_self j T)).mul_const (a j)
    have h2 := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have h3 := h1.add h2
    refine h3.congr fun x _ => ?_
    simp [Finset.sum_insert hj]

end Basic

section Global

variable {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {f f₁ f₂ : X → ℂ} {D D' : Set X}

theorem HasRootHyperplanePoles.mono (hf : HasRootHyperplanePoles L R f D) (hD : D' ⊆ D) :
    HasRootHyperplanePoles L R f D' := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hd⟩ := hf n e s₀
  exact ⟨S, m, W, hSR, hd.mono hD⟩

theorem HasRootHyperplanePoles.mono_set {R' : Set ι} (hf : HasRootHyperplanePoles L R f D)
    (hR : R ⊆ R') : HasRootHyperplanePoles L R' f D := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hd⟩ := hf n e s₀
  exact ⟨S, m, W, hSR.trans hR, hd⟩

theorem HasRootHyperplanePoles.congr (hf : HasRootHyperplanePoles L R f₁ D)
    (h : ∀ x ∈ D, f₁ x = f₂ x) : HasRootHyperplanePoles L R f₂ D := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hd⟩ := hf n e s₀
  exact ⟨S, m, W, hSR, hd.congr h⟩

/-- A function holomorphic everywhere in linear coordinates has no poles. -/
theorem hasRootHyperplanePoles_of_differentiable
    (hf : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), Differentiable ℂ (f ∘ e)) :
    HasRootHyperplanePoles L R f D := fun n e s₀ =>
  ⟨∅, 0, univ, by simp, isOpen_univ, mem_univ _, f ∘ e, (hf n e).differentiableOn,
    fun s _ _ => by simp⟩

theorem hasRootHyperplanePoles_const (c : ℂ) :
    HasRootHyperplanePoles L R (fun _ => c) D :=
  hasRootHyperplanePoles_of_differentiable fun _ _ => differentiable_const c

theorem HasRootHyperplanePoles.mul (h₁ : HasRootHyperplanePoles L R f₁ D)
    (h₂ : HasRootHyperplanePoles L R f₂ D) : HasRootHyperplanePoles L R (f₁ * f₂) D :=
  fun n e s₀ => by
  classical
  obtain ⟨S₁, m₁, W₁, hS₁, hd₁⟩ := h₁ n e s₀
  obtain ⟨S₂, m₂, W₂, hS₂, hd₂⟩ := h₂ n e s₀
  exact ⟨S₁ ∪ S₂, m₁ + m₂, W₁ ∩ W₂, by simp [hS₁, hS₂], hd₁.mul hd₂⟩

theorem HasRootHyperplanePoles.add (h₁ : HasRootHyperplanePoles L R f₁ D)
    (h₂ : HasRootHyperplanePoles L R f₂ D) : HasRootHyperplanePoles L R (f₁ + f₂) D :=
  fun n e s₀ => by
  classical
  obtain ⟨S₁, m₁, W₁, hS₁, hd₁⟩ := h₁ n e s₀
  obtain ⟨S₂, m₂, W₂, hS₂, hd₂⟩ := h₂ n e s₀
  have hW : IsOpen (W₁ ∩ W₂) := hd₁.1.inter hd₂.1
  have hs : s₀ ∈ W₁ ∩ W₂ := ⟨hd₁.2.1, hd₂.2.1⟩
  exact ⟨S₁ ∪ S₂, max m₁ m₂, W₁ ∩ W₂, by simp [hS₁, hS₂],
    (hd₁.enlarge Finset.subset_union_left (le_max_left _ _) hW hs inter_subset_left).add
      (hd₂.enlarge Finset.subset_union_right (le_max_right _ _) hW hs inter_subset_right)⟩

theorem HasRootHyperplanePoles.const_mul (hf : HasRootHyperplanePoles L R f D) (c : ℂ) :
    HasRootHyperplanePoles L R (fun x => c * f x) D := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hd⟩ := hf n e s₀
  exact ⟨S, m, W, hSR, hd.const_mul c⟩

theorem HasRootHyperplanePoles.neg (hf : HasRootHyperplanePoles L R f D) :
    HasRootHyperplanePoles L R (-f) D :=
  (hf.const_mul (-1)).congr fun x _ => by simp

theorem HasRootHyperplanePoles.sub (h₁ : HasRootHyperplanePoles L R f₁ D)
    (h₂ : HasRootHyperplanePoles L R f₂ D) : HasRootHyperplanePoles L R (f₁ - f₂) D :=
  (h₁.add h₂.neg).congr fun x _ => by simp [sub_eq_add_neg]

/-- Common pole data for finitely many functions: one index set, one exponent and one
neighborhood for the whole family. -/
theorem exists_common_hasRootPoleDataAt {κ : Type*} (T : Finset κ) {c : κ → X → ℂ}
    (hc : ∀ i ∈ T, HasRootHyperplanePoles L R (c i) D) (n : ℕ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ) :
    ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin n → ℂ)), (S : Set ι) ⊆ R ∧ IsOpen W ∧ s₀ ∈ W ∧
      ∀ i ∈ T, HasRootPoleDataAt L e s₀ (c i) D S m W := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨∅, 0, univ, by simp, isOpen_univ, mem_univ _, by simp⟩
  | insert j T hj ih =>
    obtain ⟨S, m, W, hSR, hW, hs, hT⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    obtain ⟨S₁, m₁, W₁, hS₁, hd₁⟩ := hc j (Finset.mem_insert_self j T) n e s₀
    have hW' : IsOpen (W₁ ∩ W) := hd₁.1.inter hW
    have hs' : s₀ ∈ W₁ ∩ W := ⟨hd₁.2.1, hs⟩
    refine ⟨S₁ ∪ S, max m₁ m, W₁ ∩ W, by simp [hS₁, hSR], hW', hs', fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hd₁.enlarge Finset.subset_union_left (le_max_left _ _) hW' hs' inter_subset_left
    · exact (hT i hi).enlarge Finset.subset_union_right (le_max_right _ _) hW' hs'
        inter_subset_right

/-- Common pole data with holomorphic numerators for a finite family `c i`: one index set, one
exponent and one neighborhood, and for each `i` a numerator `h i`. -/
theorem exists_rootPoleData_family {κ : Type*} [Finite κ] {c : κ → X → ℂ}
    (hc : ∀ i, HasRootHyperplanePoles L R (c i) D) (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    (s₀ : Fin n → ℂ) :
    ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin n → ℂ)), (S : Set ι) ⊆ R ∧ IsOpen W ∧ s₀ ∈ W ∧
      ∃ h : κ → (Fin n → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (h i) W) ∧
        ∀ i, ∀ s ∈ W, e s ∈ D → h i s = (∏ β ∈ S, L β (e s - e s₀)) ^ m * c i (e s) := by
  have := Fintype.ofFinite κ
  obtain ⟨S, m, W, hSR, hW, hs, hT⟩ :=
    exists_common_hasRootPoleDataAt Finset.univ (fun i _ => hc i) n e s₀
  choose h hh hEq using fun i => (hT i (Finset.mem_univ i)).2.2
  exact ⟨S, m, W, hSR, hW, hs, h, hh, hEq⟩

/-- Finite linear combinations of functions with poles along the hyperplanes of `L β`,
`β ∈ R`, have poles along the same hyperplanes. -/
theorem HasRootHyperplanePoles.sum_mul {κ : Type*} (T : Finset κ) {c : κ → X → ℂ}
    (hc : ∀ i ∈ T, HasRootHyperplanePoles L R (c i) D) (a : κ → ℂ) :
    HasRootHyperplanePoles L R (fun x => ∑ i ∈ T, c i x * a i) D := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hW, hs, hT⟩ := exists_common_hasRootPoleDataAt T hc n e s₀
  exact ⟨S, m, W, hSR, HasRootPoleDataAt.sum_mul T hW hs hT a⟩

theorem HasRootHyperplanePoles.finset_sum {κ : Type*} (T : Finset κ) {c : κ → X → ℂ}
    (hc : ∀ i ∈ T, HasRootHyperplanePoles L R (c i) D) :
    HasRootHyperplanePoles L R (fun x => ∑ i ∈ T, c i x) D :=
  (HasRootHyperplanePoles.sum_mul T hc fun _ => 1).congr fun x _ => by simp

theorem HasRootHyperplanePoles.finset_prod {κ : Type*} (T : Finset κ) {c : κ → X → ℂ}
    (hc : ∀ i ∈ T, HasRootHyperplanePoles L R (c i) D) :
    HasRootHyperplanePoles L R (fun x => ∏ i ∈ T, c i x) D := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hasRootHyperplanePoles_const (L := L) (R := R) (D := D) 1
  | insert j T hj ih =>
    refine ((hc j (Finset.mem_insert_self j T)).mul
      (ih fun i hi => hc i (Finset.mem_insert_of_mem hi))).congr fun x _ => ?_
    simp [Finset.prod_insert hj]

/-- Transfer from a dense subdomain: if `f₁` has poles along the hyperplanes of `L β`,
`β ∈ R`, on `D' ⊆ D`, the function `f₂` agrees with `f₁` on `D'` and is continuous on `D` in
every linear coordinate system, and `D'` is dense in `D` in every linear coordinate system,
then `f₂` has poles along the same hyperplanes on `D`. -/
theorem HasRootHyperplanePoles.of_eqOn_dense {D' : Set X}
    (hf : HasRootHyperplanePoles L R f₁ D') (hD : D' ⊆ D)
    (hdense : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), e ⁻¹' D ⊆ closure (e ⁻¹' D'))
    (hcont : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), ContinuousOn (f₂ ∘ e) (e ⁻¹' D))
    (heq : ∀ x ∈ D', f₁ x = f₂ x) : HasRootHyperplanePoles L R f₂ D := fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hW, hs, h, hh, hEq⟩ := hf n e s₀
  refine ⟨S, m, W, hSR, hW, hs, h, hh, fun s hs' hsD => ?_⟩
  have hEqOn : EqOn h (fun s => (∏ β ∈ S, L β (e s - e s₀)) ^ m * f₂ (e s))
      (W ∩ e ⁻¹' D') := fun s hs => by
    rw [hEq s hs.1 hs.2, heq _ hs.2]
  have hc₁ : ContinuousOn h (W ∩ e ⁻¹' D) := hh.continuousOn.mono inter_subset_left
  have hc₂ : ContinuousOn (fun s => (∏ β ∈ S, L β (e s - e s₀)) ^ m * f₂ (e s))
      (W ∩ e ⁻¹' D) :=
    ((differentiable_prod_linearForm_sub S L e s₀).pow m).continuous.continuousOn.mul
      ((hcont n e).mono inter_subset_right)
  exact hEqOn.of_subset_closure hc₁ hc₂ (fun t ht => ⟨ht.1, hD ht.2⟩)
    (fun t ht => hW.inter_closure ⟨ht.1, hdense n e ht.2⟩) ⟨hs', hsD⟩

/-- Transfer from a dense subdomain for a function meromorphic in linear coordinates on `D`:
it suffices that `D' ⊆ D` is dense in every linear coordinate system. -/
theorem HasRootHyperplanePoles.of_eqOn_of_isMeromorphicInCoordinatesOn {D' : Set X}
    (hf : HasRootHyperplanePoles L R f₁ D') (hD : D' ⊆ D)
    (hdense : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), Dense (e ⁻¹' D'))
    (hf₂ : IsMeromorphicInCoordinatesOn f₂ D) (heq : ∀ x ∈ D', f₁ x = f₂ x) :
    HasRootHyperplanePoles L R f₂ D := by
  refine hf.of_eqOn_dense hD (fun n e => by rw [(hdense n e).closure_eq]; exact subset_univ _)
    (fun n e => ?_) heq
  obtain ⟨-, -, hhol, -⟩ := hf₂.2 n e
  have h1 := mdifferentiableOn_iff_differentiableOn.1 (hhol (ContinuousLinearMap.id ℂ ℂ))
  exact h1.continuousOn

/-- The local form of Bernstein–Lapid, Theorem 2.3 (6), for a finite expansion
`∑ i, c i λ * ψ i g` whose scalar coefficients have poles along the hyperplanes of `L β`,
`β ∈ R`: the index set, exponent and neighborhood are chosen before the point `g`. -/
theorem exists_rootPoleData_sum_mul {k : ℕ} {G : Type*} {c : Fin k → X → ℂ}
    (hc : ∀ i, HasRootHyperplanePoles L R (c i) D) (ψ : Fin k → G → ℂ) (n : ℕ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ) :
    ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin n → ℂ)),
      (S : Set ι) ⊆ R ∧ IsOpen W ∧ s₀ ∈ W ∧
      ∀ g : G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
        ∀ s ∈ W, e s ∈ D →
          h s = (∏ β ∈ S, L β (e s - e s₀)) ^ m * ∑ i, c i (e s) * ψ i g := by
  obtain ⟨S, m, W, hSR, hW, hs, hT⟩ :=
    exists_common_hasRootPoleDataAt Finset.univ (fun i _ => hc i) n e s₀
  refine ⟨S, m, W, hSR, hW, hs, fun g => ?_⟩
  obtain ⟨-, -, h, hh, hEq⟩ :=
    HasRootPoleDataAt.sum_mul Finset.univ hW hs (fun i _ => hT i (Finset.mem_univ i))
      (fun i => ψ i g)
  exact ⟨h, hh, hEq⟩

/-- A finite expansion `∑ i, c i * ψ i g` can be rewritten through the values of the `ψ i` at
finitely many points `q j`: the new coefficients are the expansions evaluated at the points. -/
theorem exists_points_sum_mul_eq {k : ℕ} {G : Type*} (ψ : Fin k → G → ℂ) :
    ∃ (r : ℕ) (q : Fin r → G) (a : Fin r → G → ℂ), ∀ (c : Fin k → ℂ) (g : G),
      ∑ i, c i * ψ i g = ∑ j, (∑ i, c i * ψ i (q j)) * a j g := by
  classical
  let Ψ : G → Fin k → ℂ := fun g i => ψ i g
  obtain ⟨v, hv, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range Ψ)
  choose q hq using hv
  have hmem : ∀ g, ∃ a : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range Ψ))) → ℂ,
      ∑ j, a j • v j = Ψ g := fun g => by
    have : Ψ g ∈ Submodule.span ℂ (Set.range v) := by
      rw [hspan]
      exact Submodule.subset_span ⟨g, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose a ha using hmem
  refine ⟨_, q, fun j g => a g j, fun c g => ?_⟩
  have h1 : ∀ i, ψ i g = ∑ j, a g j * ψ i (q j) := fun i => by
    have h := congrFun (ha g) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [show ψ i g = Ψ g i from rfl, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hq j]
  simp_rw [h1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- If every expansion `λ ↦ ∑ i, c i λ * ψ i g` has poles along the hyperplanes of `L β`,
`β ∈ R`, then one index set, exponent and neighborhood serve for all points `g`. -/
theorem exists_rootPoleData_sum_mul_of_forall {k : ℕ} {G : Type*} {c : Fin k → X → ℂ}
    (ψ : Fin k → G → ℂ)
    (hc : ∀ g, HasRootHyperplanePoles L R (fun x => ∑ i, c i x * ψ i g) D) (n : ℕ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (s₀ : Fin n → ℂ) :
    ∃ (S : Finset ι) (m : ℕ) (W : Set (Fin n → ℂ)),
      (S : Set ι) ⊆ R ∧ IsOpen W ∧ s₀ ∈ W ∧
      ∀ g : G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
        ∀ s ∈ W, e s ∈ D →
          h s = (∏ β ∈ S, L β (e s - e s₀)) ^ m * ∑ i, c i (e s) * ψ i g := by
  obtain ⟨r, q, a, hqa⟩ := exists_points_sum_mul_eq ψ
  obtain ⟨S, m, W, hSR, hW, hs, hg⟩ :=
    exists_rootPoleData_sum_mul (c := fun j x => ∑ i, c i x * ψ i (q j)) (fun j => hc (q j))
      a n e s₀
  refine ⟨S, m, W, hSR, hW, hs, fun g => ?_⟩
  obtain ⟨h, hh, hEq⟩ := hg g
  exact ⟨h, hh, fun s hs' hsD => by rw [hEq s hs' hsD, hqa (fun i => c i (e s)) g]⟩

/-- The coefficients of linearly independent functions `ψ i` are detected by finitely many
points: each coefficient `c i` is a fixed linear combination of the values at points `q j` of
the expansion `∑ i', c i' * ψ i'`. -/
theorem exists_points_coeff_eq {k : ℕ} {G : Type*} {ψ : Fin k → G → ℂ}
    (hψ : LinearIndependent ℂ ψ) (i : Fin k) :
    ∃ (r : ℕ) (q : Fin r → G) (b : Fin r → ℂ), ∀ c : Fin k → ℂ,
      c i = ∑ j, (∑ i', c i' * ψ i' (q j)) * b j := by
  classical
  let Ψ : G → Fin k → ℂ := fun g i => ψ i g
  have htop : Submodule.span ℂ (Set.range Ψ) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    let a : Fin k → ℂ := fun i' => φ (fun j => if i' = j then 1 else 0)
    have hsum : ∑ i', a i' • ψ i' = 0 := by
      funext g
      have h0 : φ (Ψ g) = 0 := hφ (Submodule.subset_span ⟨g, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ (Ψ g)] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h0]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [a, Ψ, smul_eq_mul]
      ring
    have ha := Fintype.linearIndependent_iff.mp hψ a hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    have : φ (fun j => if i' = j then 1 else 0) = 0 := ha i'
    rw [this, smul_zero]
  obtain ⟨v, hv, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range Ψ)
  choose q hq using hv
  have hmem : (Pi.single i 1 : Fin k → ℂ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [hspan, htop]
    exact Submodule.mem_top
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨_, q, b, fun c => ?_⟩
  have h1 : ∀ i', (Pi.single i 1 : Fin k → ℂ) i' = ∑ j, b j * ψ i' (q j) := fun i' => by
    rw [← hb]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hq j]
  calc c i = ∑ i', c i' * (Pi.single i 1 : Fin k → ℂ) i' := by
        simp [Pi.single_apply]
    _ = ∑ j, (∑ i', c i' * ψ i' (q j)) * b j := by
        simp_rw [h1, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => ?_
        ring

/-- If the functions `ψ i` are linearly independent and every expansion
`λ ↦ ∑ i, c i λ * ψ i g` has poles along the hyperplanes of `L β`, `β ∈ R`, then so does every
coefficient `c i`. -/
theorem HasRootHyperplanePoles.coeff_of_linearIndependent {k : ℕ} {G : Type*}
    {c : Fin k → X → ℂ} {ψ : Fin k → G → ℂ} (hψ : LinearIndependent ℂ ψ)
    (hc : ∀ g, HasRootHyperplanePoles L R (fun x => ∑ i, c i x * ψ i g) D) (i : Fin k) :
    HasRootHyperplanePoles L R (c i) D := by
  obtain ⟨r, q, b, hqb⟩ := exists_points_coeff_eq hψ i
  exact (HasRootHyperplanePoles.sum_mul Finset.univ (fun j _ => hc (q j)) b).congr
    fun x _ => (hqb fun i' => c i' x).symm

end Global

section Change

variable {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {f : X → ℂ} {D : Set X}

/-- Poles along root hyperplanes are preserved by complex linear changes of variables; the
forms are pulled back. -/
theorem HasRootHyperplanePoles.comp_linearEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {L : ι → Y →ₗ[ℂ] ℂ} {f : Y → ℂ} {D : Set Y} (hf : HasRootHyperplanePoles L R f D)
    (T : X ≃ₗ[ℂ] Y) :
    HasRootHyperplanePoles (fun β => L β ∘ₗ T.toLinearMap) R (f ∘ T) (T ⁻¹' D) :=
  fun n e s₀ => by
  obtain ⟨S, m, W, hSR, hW, hs, h, hh, hEq⟩ := hf n (e.trans T) s₀
  refine ⟨S, m, W, hSR, hW, hs, h, hh, fun s hs' hsD => ?_⟩
  have := hEq s hs' hsD
  simpa [map_sub] using this

/-- A complex differentiable product of finitely many functions on a normed space. -/
theorem differentiable_finsetProd_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} (T : Finset κ) {F : κ → E → ℂ} (hF : ∀ i ∈ T, Differentiable ℂ (F i)) :
    Differentiable ℂ (fun s => ∏ i ∈ T, F i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hF j (Finset.mem_insert_self j T)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- Poles along the hyperplanes of forms `L' β`, `β ∈ R'`, are poles along the hyperplanes of
forms `L γ`, `γ ∈ R`, when every `L' β` is a nonzero multiple `a β • L (σ β)` with
`σ β ∈ R`. -/
theorem HasRootHyperplanePoles.of_proportional {κ : Type*} {L' : κ → X →ₗ[ℂ] ℂ}
    {R' : Set κ} (hf : HasRootHyperplanePoles L' R' f D) (σ : κ → ι) (a : κ → ℂ)
    (hσ : ∀ β ∈ R', σ β ∈ R) (ha : ∀ β ∈ R', a β ≠ 0)
    (hL : ∀ β ∈ R', L' β = a β • L (σ β)) : HasRootHyperplanePoles L R f D := fun n e s₀ => by
  classical
  obtain ⟨S', m, W, hS'R, hW, hs, h, hh, hEq⟩ := hf n e s₀
  set N := S'.card
  let c : ι → ℕ := fun γ => (S'.filter fun β => σ β = γ).card
  have hc : ∀ γ, c γ ≤ N := fun γ => Finset.card_filter_le _ _
  let A : ℂ := ∏ β ∈ S', a β
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β hβ => ha β (hS'R hβ)
  let Q : (Fin n → ℂ) → ℂ := fun s =>
    ∏ γ ∈ S'.image σ, L γ (e s - e s₀) ^ (N - c γ)
  have hQ : Differentiable ℂ Q :=
    differentiable_finsetProd_apply _ fun γ _ => (differentiable_linearForm_sub (L γ) e s₀).pow _
  refine ⟨S'.image σ, N * m, W, ?_, hW, hs, fun s => A⁻¹ ^ m * Q s ^ m * h s,
    ((differentiable_const _).mul (hQ.pow m)).differentiableOn.mul hh, fun s hs' hsD => ?_⟩
  · intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hγ
    exact hσ β (hS'R hβ)
  · have hP' : ∏ β ∈ S', L' β (e s - e s₀) =
        A * ∏ γ ∈ S'.image σ, L γ (e s - e s₀) ^ c γ := by
      rw [Finset.prod_congr rfl fun β hβ => by rw [hL β (hS'R hβ)], ]
      simp only [LinearMap.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
      rw [Finset.prod_comp (fun γ => L γ (e s - e s₀)) σ]
    have hPS : (∏ γ ∈ S'.image σ, L γ (e s - e s₀)) ^ N =
        (∏ γ ∈ S'.image σ, L γ (e s - e s₀) ^ c γ) * Q s := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun γ _ => ?_
      rw [← pow_add, Nat.add_sub_cancel' (hc γ)]
    dsimp only
    rw [hEq s hs' hsD, hP', pow_mul, hPS]
    calc A⁻¹ ^ m * Q s ^ m * ((A * ∏ γ ∈ S'.image σ, L γ (e s - e s₀) ^ c γ) ^ m * f (e s))
        = (A⁻¹ * A) ^ m * ((∏ γ ∈ S'.image σ, L γ (e s - e s₀) ^ c γ) * Q s) ^ m *
            f (e s) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_pow, one_mul]

/-- Poles along root hyperplanes are preserved by composition with a complex linear map `τ`
into a finite-dimensional space; the forms are pulled back along `τ`. -/
theorem HasRootHyperplanePoles.comp_linearMap {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] {L : ι → Y →ₗ[ℂ] ℂ} {f : Y → ℂ} {D : Set Y}
    (hf : HasRootHyperplanePoles L R f D) (τ : X →ₗ[ℂ] Y) :
    HasRootHyperplanePoles (fun β => L β ∘ₗ τ) R (f ∘ τ) (τ ⁻¹' D) := fun n e s₀ => by
  let e' : (Fin (Module.finrank ℂ Y) → ℂ) ≃ₗ[ℂ] Y := (Module.finBasis ℂ Y).equivFun.symm
  let A : (Fin n → ℂ) →L[ℂ] (Fin (Module.finrank ℂ Y) → ℂ) :=
    LinearMap.toContinuousLinearMap (e'.symm.toLinearMap ∘ₗ τ ∘ₗ e.toLinearMap)
  have hA : ∀ s, e' (A s) = τ (e s) := fun s => by simp [A]
  obtain ⟨S, m, W, hSR, hW, hs, h, hh, hEq⟩ := hf _ e' (A s₀)
  refine ⟨S, m, A ⁻¹' W, hSR, hW.preimage A.continuous, hs, h ∘ A,
    hh.comp A.differentiable.differentiableOn (mapsTo_preimage A W), fun s hs' hsD => ?_⟩
  have hsD' : e' (A s) ∈ D := by rw [hA]; exact hsD
  have := hEq (A s) hs' hsD'
  rw [hA, hA] at this
  simpa [map_sub] using this

/-- Pullback along a linear map with proportional forms: if `f` on `Y` has poles along the
hyperplanes of `L' β`, `β ∈ R'`, and each pulled-back form `L' β ∘ τ` is a nonzero multiple
`a β • L (σ β)` with `σ β ∈ R`, then `f ∘ τ` has poles along the hyperplanes of `L γ`,
`γ ∈ R`. -/
theorem HasRootHyperplanePoles.comp_linearMap_of_proportional {Y : Type*} [AddCommGroup Y]
    [Module ℂ Y] [FiniteDimensional ℂ Y] {κ : Type*} {L' : κ → Y →ₗ[ℂ] ℂ} {R' : Set κ}
    {f : Y → ℂ} {D : Set Y} (hf : HasRootHyperplanePoles L' R' f D) (τ : X →ₗ[ℂ] Y)
    (σ : κ → ι) (a : κ → ℂ) (hσ : ∀ β ∈ R', σ β ∈ R) (ha : ∀ β ∈ R', a β ≠ 0)
    (hL : ∀ β ∈ R', L' β ∘ₗ τ = a β • L (σ β)) :
    HasRootHyperplanePoles L R (f ∘ τ) (τ ⁻¹' D) :=
  (hf.comp_linearMap τ).of_proportional σ a hσ ha hL

/-- Pullback along a linear equivalence with proportional forms (no finite-dimensionality
needed). -/
theorem HasRootHyperplanePoles.comp_linearEquiv_of_proportional {Y : Type*} [AddCommGroup Y]
    [Module ℂ Y] {κ : Type*} {L' : κ → Y →ₗ[ℂ] ℂ} {R' : Set κ} {f : Y → ℂ} {D : Set Y}
    (hf : HasRootHyperplanePoles L' R' f D) (T : X ≃ₗ[ℂ] Y) (σ : κ → ι) (a : κ → ℂ)
    (hσ : ∀ β ∈ R', σ β ∈ R) (ha : ∀ β ∈ R', a β ≠ 0)
    (hL : ∀ β ∈ R', L' β ∘ₗ T.toLinearMap = a β • L (σ β)) :
    HasRootHyperplanePoles L R (f ∘ T) (T ⁻¹' D) :=
  (hf.comp_linearEquiv T).of_proportional σ a hσ ha hL

end Change

section Invariant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The parameters of a line `t ↦ x + t • y` lying in a convex set form a convex set. -/
theorem convex_preimage_line {B : Set E} (hB : Convex ℝ B) (x y : E) :
    Convex ℝ ((fun t : ℂ => x + t • y) ⁻¹' B) := by
  intro t₁ ht₁ t₂ ht₂ c₁ c₂ hc₁ hc₂ hc
  have h := hB ht₁ ht₂ hc₁ hc₂ hc
  have hcomb : c₁ • (x + t₁ • y) + c₂ • (x + t₂ • y) =
      (c₁ + c₂) • x + (c₁ • t₁ + c₂ • t₂) • y := by
    simp only [smul_add, add_smul, smul_assoc]
    abel
  rw [hc, one_smul] at hcomb
  show x + (c₁ • t₁ + c₂ • t₂) • y ∈ B
  rw [← hcomb]
  exact h

/-- The one-variable criterion in a normed space: let `F` satisfy `g * F = h` on `U ∩ W` for
complex differentiable `g`, `h` on the connected open set `W` with `g` not identically zero,
and let `F` be invariant on the open set `U` under translations by the kernel of a continuous
linear form `a`. Then near `s₀` a power of `s ↦ a (s - s₀)` times `F` agrees on `U` with a
complex differentiable function. -/
theorem exists_pow_mul_eq_of_kernel_invariant {F g h : E → ℂ} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hWc : IsPreconnected W) {s₀ : E} (hs₀ : s₀ ∈ W)
    (hg : DifferentiableOn ℂ g W) (hne : ∃ s ∈ W, g s ≠ 0) (hh : DifferentiableOn ℂ h W)
    (hgh : ∀ s ∈ U ∩ W, g s * F s = h s) (a : E →L[ℂ] ℂ)
    (hinv : ∀ s ∈ U, ∀ v, a v = 0 → s + v ∈ U → F (s + v) = F s) :
    ∃ (m : ℕ) (W' : Set E), IsOpen W' ∧ s₀ ∈ W' ∧ ∃ H : E → ℂ, DifferentiableOn ℂ H W' ∧
      ∀ s ∈ W', s ∈ U → H s = a (s - s₀) ^ m * F s := by
  by_cases ha : a = 0
  · exact ⟨1, univ, isOpen_univ, mem_univ _, fun _ => 0, differentiableOn_const 0,
      fun s _ _ => by simp [ha]⟩
  obtain ⟨u, hu⟩ : ∃ u : E, a u = 1 := by
    obtain ⟨w, hw⟩ : ∃ w, a w ≠ 0 := by
      by_contra! hcon
      exact ha (ContinuousLinearMap.ext hcon)
    exact ⟨(a w)⁻¹ • w, by simp [hw]⟩
  obtain ⟨R₀, hR₀, hBW⟩ := Metric.isOpen_iff.mp hW s₀ hs₀
  -- the lines `z ↦ p + (z - a p) • u` through points `p` near `s₀`
  let Λ : E × ℂ → E := fun q => q.1 + (q.2 - a q.1) • u
  have hΛc : Continuous Λ := by
    exact continuous_fst.add ((continuous_snd.sub (a.continuous.comp continuous_fst)).smul
      continuous_const)
  have hΛ0 : Λ (s₀, a s₀) = s₀ := by simp [Λ]
  have haΛ : ∀ p z, a (Λ (p, z)) = z := fun p z => by simp [Λ, hu]
  obtain ⟨ε, hε, hεB⟩ : ∃ ε > 0, ∀ q : E × ℂ, dist q (s₀, a s₀) < ε →
      Λ q ∈ Metric.ball s₀ R₀ := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hΛc.continuousAt R₀ hR₀
    refine ⟨δ, hδ, fun q hq => ?_⟩
    have := hδ' hq
    rw [hΛ0] at this
    exact this
  obtain ⟨δ', hδ', hδ'a⟩ := Metric.continuousAt_iff.mp a.continuous.continuousAt ε hε
  have hball : Metric.ball s₀ (min (min ε δ') R₀) ⊆ W := fun p hp =>
    hBW (Metric.ball_subset_ball (min_le_right _ _) hp)
  obtain ⟨p₁, hp₁, hgp₁⟩ := exists_ne_zero_of_differentiableOn hW hWc hg hne Metric.isOpen_ball
    hball (Metric.nonempty_ball.mpr (lt_min (lt_min hε hδ') hR₀))
  have hp₁ε : dist p₁ s₀ < ε :=
    lt_of_lt_of_le (Metric.mem_ball.mp hp₁) ((min_le_left _ _).trans (min_le_left _ _))
  have hp₁δ : dist p₁ s₀ < δ' :=
    lt_of_lt_of_le (Metric.mem_ball.mp hp₁) ((min_le_left _ _).trans (min_le_right _ _))
  have hap₁ : dist (a p₁) (a s₀) < ε := hδ'a hp₁δ
  let ℓ : ℂ → E := fun z => Λ (p₁, z)
  have hℓ : Differentiable ℂ ℓ := by
    show Differentiable ℂ (fun z : ℂ => p₁ + (z - a p₁) • u)
    exact (differentiable_const _).add
      ((differentiable_id.sub_const _).smul_const u)
  have hℓB : ∀ z ∈ Metric.ball (a s₀) ε, ℓ z ∈ Metric.ball s₀ R₀ := fun z hz => by
    refine hεB (p₁, z) ?_
    rw [Prod.dist_eq]
    exact max_lt hp₁ε (Metric.mem_ball.mp hz)
  -- the restriction of `g` to the line through `p₁` has finite order at `a s₀`
  let φ : ℂ → ℂ := fun z => g (ℓ z)
  have hφ : DifferentiableOn ℂ φ (Metric.ball (a s₀) ε) :=
    hg.comp hℓ.differentiableOn fun z hz => hBW (hℓB z hz)
  have hφne : ¬∀ᶠ z in 𝓝 (a s₀), φ z = 0 := by
    intro hev
    have h0 := eqOn_zero_of_differentiableOn_of_eventuallyEq_zero Metric.isOpen_ball
      (convex_ball (a s₀) ε).isPreconnected hφ (Metric.mem_ball_self hε) hev (a p₁)
      (Metric.mem_ball.mpr hap₁)
    apply hgp₁
    have hℓp₁ : ℓ (a p₁) = p₁ := by simp [ℓ, Λ]
    simpa [φ, hℓp₁] using h0
  obtain ⟨N, w, hwan, hw0, hφw⟩ :=
    ((hφ.analyticOnNhd Metric.isOpen_ball) (a s₀) (Metric.mem_ball_self hε)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      hφne
  have hev : ∀ᶠ z in 𝓝 (a s₀), (φ z = (z - a s₀) ^ N • w z ∧ w z ≠ 0 ∧
      AnalyticAt ℂ w z) ∧ z ∈ Metric.ball (a s₀) ε :=
    (hφw.and ((hwan.continuousAt.eventually_ne hw0).and hwan.eventually_analyticAt)).and
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨N, Metric.ball s₀ R₀ ∩ a ⁻¹' Metric.ball (a s₀) ρ,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage a.continuous),
    ⟨Metric.mem_ball_self hR₀, Metric.mem_ball_self hρ⟩,
    fun s => h (ℓ (a s)) / w (a s), ?_, ?_⟩
  · intro s hs
    have hz := hρev (Metric.mem_ball.mp hs.2)
    have h1 : DifferentiableWithinAt ℂ (fun s => h (ℓ (a s)))
        (Metric.ball s₀ R₀ ∩ a ⁻¹' Metric.ball (a s₀) ρ) s :=
      (hh.comp (hℓ.comp a.differentiable).differentiableOn
        (fun t ht => hBW (hℓB _ (hρev (Metric.mem_ball.mp ht.2)).2))) s hs
    have h2 : DifferentiableAt ℂ (fun s => w (a s)) s :=
      hz.1.2.2.differentiableAt.comp s a.differentiableAt
    have h3 : DifferentiableAt ℂ (fun s => (w (a s))⁻¹) s := by
      have hwz : DifferentiableAt ℂ w (a s) := hz.1.2.2.differentiableAt
      exact ((differentiableAt_inv hz.1.2.1).comp (a s) hwz).comp s a.differentiableAt
    have h4 := h1.mul h3.differentiableWithinAt
    simp only [div_eq_mul_inv]
    exact h4
  · intro s hs hsU
    have hz := hρev (Metric.mem_ball.mp hs.2)
    obtain ⟨⟨hφz, hwz, -⟩, hzε⟩ := hz
    -- `h (ℓ z) = F s * g (ℓ z)` by the identity theorem along the segment from `s` to `ℓ z`
    set z := a s with hzdef
    let y : E := ℓ z - s
    let T : Set ℂ := (fun t : ℂ => s + t • y) ⁻¹' Metric.ball s₀ R₀
    have hlin : Differentiable ℂ (fun t : ℂ => s + t • y) :=
      (differentiable_const _).add (differentiable_id.smul_const y)
    have hTo : IsOpen T := Metric.isOpen_ball.preimage hlin.continuous
    have hTc : IsPreconnected T :=
      (convex_preimage_line (convex_ball s₀ R₀) s y).isPreconnected
    have hT0 : (0 : ℂ) ∈ T := by simpa [T] using hs.1
    have hT1 : (1 : ℂ) ∈ T := by simpa [T, y] using hℓB z hzε
    let k : ℂ → ℂ := fun t => h (s + t • y) - F s * g (s + t • y)
    have hk : DifferentiableOn ℂ k T := by
      have hmaps : MapsTo (fun t : ℂ => s + t • y) T W := fun t ht => hBW ht
      exact (hh.comp hlin.differentiableOn hmaps).sub
        ((differentiableOn_const _).mul (hg.comp hlin.differentiableOn hmaps))
    have hk0 : k =ᶠ[𝓝 0] 0 := by
      have hmem : ∀ᶠ t in 𝓝 (0 : ℂ), s + t • y ∈ U ∩ Metric.ball s₀ R₀ := by
        have hcont : Tendsto (fun t : ℂ => s + t • y) (𝓝 0) (𝓝 s) := by
          simpa using hlin.continuous.tendsto 0
        exact hcont (IsOpen.mem_nhds (hU.inter Metric.isOpen_ball) ⟨hsU, hs.1⟩)
      filter_upwards [hmem] with t ht
      have hay : a (t • y) = 0 := by
        simp [y, map_sub, haΛ, ℓ, hzdef]
      have hF := hinv s hsU (t • y) hay ht.1
      have hgh' := hgh (s + t • y) ⟨ht.1, hBW ht.2⟩
      simp only [k, Pi.zero_apply]
      rw [← hgh', hF]
      ring
    have hk1 := eqOn_zero_of_differentiableOn_of_eventuallyEq_zero hTo hTc hk hT0 hk0 1 hT1
    have hseg : s + (1 : ℂ) • y = ℓ z := by simp [y]
    simp only [k, hseg] at hk1
    have hφz' : g (ℓ z) = (z - a s₀) ^ N * w z := by simpa [φ, smul_eq_mul] using hφz
    rw [map_sub, ← hzdef, div_eq_iff hwz]
    rw [sub_eq_zero] at hk1
    rw [hk1, hφz']
    ring

end Invariant

section Criterion

variable {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {f : X → ℂ} {D : Set X}

/-- A meromorphic function invariant under translation by the kernel of one form `L β`,
`β ∈ R`, has poles along the hyperplanes of `L β`: near every point, in every linear
coordinate system, a power of `λ ↦ L β (λ - λ₀)` times `f` agrees on `D` with a holomorphic
function. -/
theorem hasRootHyperplanePoles_of_kernel_invariant (hf : IsMeromorphicInCoordinatesOn f D)
    {β : ι} (hβ : β ∈ R) (hinv : ∀ x ∈ D, ∀ ν : X, L β ν = 0 → x + ν ∈ D → f (x + ν) = f x) :
    HasRootHyperplanePoles L R f D := fun n e s₀ => by
  obtain ⟨hUo, -, -, hloc⟩ := hf.2 n e
  obtain ⟨W, hW, hWc, hs₀, g, h, hg, hne, hh, hgh⟩ := hloc s₀
  let a : (Fin n → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (L β ∘ₗ e.toLinearMap)
  obtain ⟨m, W', hW', hs₀', H, hH, hHEq⟩ := exists_pow_mul_eq_of_kernel_invariant hUo hW
    hWc.isPreconnected hs₀ (mdifferentiableOn_iff_differentiableOn.1 hg) hne
    (differentiableOn_of_isHolomorphicOn hh)
    (fun s hs => by simpa [smul_eq_mul] using hgh s hs) a
    (fun s hs v hv hsv => by
      have h1 : e (s + v) = e s + e v := map_add e s v
      have := hinv (e s) hs (e v) hv (by simpa [h1] using hsv)
      simpa [Function.comp_apply, h1] using this)
  refine ⟨{β}, m, W', by simpa using hβ, hW', hs₀', H, hH, fun s hs hsD => ?_⟩
  rw [hHEq s hs hsD]
  simp [a, map_sub]

end Criterion

end Langlands.Analysis.Meromorphic
