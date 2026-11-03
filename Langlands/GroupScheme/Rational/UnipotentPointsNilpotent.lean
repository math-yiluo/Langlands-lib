import Langlands.GroupScheme.Rational.UnipotentProductBound
import Mathlib.Algebra.Algebra.Operations
import Mathlib.GroupTheory.Nilpotent

/-! # Uniform nilpotence of unipotent groups of points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open scoped CategoryTheory.MonObj Matrix Pointwise

namespace Langlands.GroupScheme.UnitDifference

variable {S A H : Type*} [CommRing S] [Ring A] [Algebra S A] [Group H]

/-- The span of ordered products of at least `r` represented differences. -/
def productSpan (S : Type*) [CommRing S] {A H : Type*} [Ring A] [Algebra S A]
    [Group H] (f : H →* Aˣ) (r : ℕ) : Submodule S A :=
  Submodule.span S {M | ∃ l : List H, r ≤ l.length ∧
    (l.map (fun x => (f x : A) - 1)).prod = M}

variable (S) (f : H →* Aˣ)

/-- Larger word length gives a smaller submodule. -/
theorem productSpan_antitone : Antitone (productSpan S f) := by
  intro r s hrs
  apply Submodule.span_mono
  rintro M ⟨l, hl, rfl⟩
  exact ⟨l, hrs.trans hl, rfl⟩

/-- Multiplication adds the lower word-length bounds. -/
theorem productSpan_mul_le (r s : ℕ) :
    productSpan S f r * productSpan S f s ≤ productSpan S f (r + s) := by
  rw [productSpan, productSpan, Submodule.span_mul_span]
  apply Submodule.span_le.2
  rintro _ ⟨a, ⟨l, hl, rfl⟩, b, ⟨t, ht, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨l ++ t, ?_, ?_⟩
  · simpa using Nat.add_le_add hl ht
  · simp

/-- Every single represented difference is in the first span. -/
theorem sub_one_mem (x : H) : (f x : A) - 1 ∈ productSpan S f 1 := by
  apply Submodule.subset_span
  exact ⟨[x], by simp, by simp⟩

/-- Multiplying by a represented point on the right preserves each span. -/
theorem mul_point_mem {r : ℕ} {M : A} (hM : M ∈ productSpan S f r) (x : H) :
    M * (f x : A) ∈ productSpan S f r := by
  have h := productSpan_mul_le S f r 1
    (Submodule.mul_mem_mul hM (sub_one_mem S f x))
  have h' := productSpan_antitone S f (Nat.le_add_right r 1) h
  have heq : M * (f x : A) = M * ((f x : A) - 1) + M := by noncomm_ring
  rw [heq]
  exact (productSpan S f r).add_mem h' hM

/-- Multiplying by a represented point on the left preserves each span. -/
theorem point_mul_mem {r : ℕ} {M : A} (hM : M ∈ productSpan S f r) (x : H) :
    (f x : A) * M ∈ productSpan S f r := by
  have h := productSpan_mul_le S f 1 r
    (Submodule.mul_mem_mul (sub_one_mem S f x) hM)
  have h' := productSpan_antitone S f (Nat.le_add_left r 1) h
  have heq : (f x : A) * M = ((f x : A) - 1) * M + M := by noncomm_ring
  rw [heq]
  exact (productSpan S f r).add_mem h' hM

/-- Points whose difference belongs to the given product span. -/
def congruenceSubgroup (r : ℕ) : Subgroup H where
  carrier := {x | (f x : A) - 1 ∈ productSpan S f r}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (f (x * y) : A) - 1 ∈ productSpan S f r
    rw [map_mul, Units.val_mul]
    have heq : (f x : A) * (f y : A) - 1 =
        ((f x : A) - 1) * (f y : A) + ((f y : A) - 1) := by noncomm_ring
    rw [heq]
    exact (productSpan S f r).add_mem (mul_point_mem S f hx y) hy
  inv_mem' := by
    intro x hx
    have h := (productSpan S f r).neg_mem (mul_point_mem S f hx x⁻¹)
    have heq : -(((f x : A) - 1) * (f x⁻¹ : A)) = (f x⁻¹ : A) - 1 := by
      rw [sub_mul, map_inv]
      simp
    rwa [heq] at h

/-- A commutator adds one represented difference. -/
theorem commutator_mem_succ {r : ℕ} {x : H}
    (hx : x ∈ congruenceSubgroup S f r) (y : H) :
    ⁅x, y⁆ ∈ congruenceSubgroup S f (r + 1) := by
  have hxy := productSpan_mul_le S f r 1
    (Submodule.mul_mem_mul hx (sub_one_mem S f y))
  have hyx : ((f y : A) - 1) * ((f x : A) - 1) ∈ productSpan S f (r + 1) := by
    simpa only [Nat.add_comm 1 r] using productSpan_mul_le S f 1 r
      (Submodule.mul_mem_mul (sub_one_mem S f y) hx)
  have h := mul_point_mem S f
    (mul_point_mem S f ((productSpan S f (r + 1)).sub_mem hxy hyx) x⁻¹) y⁻¹
  change (f ⁅x, y⁆ : A) - 1 ∈ productSpan S f (r + 1)
  have hd : ((f x : A) - 1) * ((f y : A) - 1) -
      ((f y : A) - 1) * ((f x : A) - 1) =
      (f x : A) * (f y : A) - (f y : A) * (f x : A) := by noncomm_ring
  have heq : (f ⁅x, y⁆ : A) - 1 =
      (((f x : A) - 1) * ((f y : A) - 1) -
        ((f y : A) - 1) * ((f x : A) - 1)) * (f x⁻¹ : A) * (f y⁻¹ : A) := by
    rw [hd]
    simp [commutatorElement_def, sub_mul, mul_assoc]
  rw [heq]
  exact h

/-- The abstract lower central series lies in the difference filtration. -/
theorem lowerCentralSeries_le_congruence (r : ℕ) :
    (⊤ : Subgroup H).lowerCentralSeries r ≤ congruenceSubgroup S f (r + 1) := by
  induction r with
  | zero =>
    intro x _hx
    exact sub_one_mem S f x
  | succ r ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro x hx y _hy
    exact commutator_mem_succ S f (ih hx) y

/-- A zero word bound forces the matching span to vanish. -/
theorem productSpan_eq_bot_of_bound (m : ℕ)
    (h : ∀ l : List H, m ≤ l.length → (l.map (fun x => (f x : A) - 1)).prod = 0) :
    productSpan S f m = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.2
  rintro M ⟨l, hl, rfl⟩
  exact (Submodule.mem_bot S).2 (h l hl)

include S in
/-- The bound gives a uniform term of the lower central series in the kernel. -/
theorem lowerCentralSeries_le_ker_of_bound (m : ℕ)
    (h : ∀ l : List H, m ≤ l.length → (l.map (fun x => (f x : A) - 1)).prod = 0) :
    (⊤ : Subgroup H).lowerCentralSeries m ≤ f.ker := by
  intro x hx
  have hmem := lowerCentralSeries_le_congruence S f m hx
  change (f x : A) - 1 ∈ productSpan S f (m + 1) at hmem
  have hz := productSpan_antitone S f (Nat.le_add_right m 1) hmem
  rw [productSpan_eq_bot_of_bound S f m h, Submodule.mem_bot] at hz
  rw [MonoidHom.mem_ker]
  exact Units.ext (sub_eq_zero.1 hz)

end Langlands.GroupScheme.UnitDifference

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A single lower-central-series bound works on every relative scheme test. -/
def HasUniformNilpotentPoints (G : GroupScheme (Spec (CommRingCat.of k))) (d : ℕ) : Prop :=
  ∀ T : Over (Spec (CommRingCat.of k)),
    (⊤ : Subgroup (T ⟶ G.X)).lowerCentralSeries d = ⊥

namespace MatrixRepresentation

/-- The representation dimension bounds the lower central series in its kernel,
uniformly over all tests. -/
theorem lowerCentralSeries_le_ker_of_isUnipotent (hG : IsUnipotent G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) (T : Over (Spec (CommRingCat.of k))) :
    (⊤ : Subgroup (T ⟶ G.X)).lowerCentralSeries m ≤ (ρ.pointMatrix T).ker := by
  exact UnitDifference.lowerCentralSeries_le_ker_of_bound Γ(T.left, ⊤)
    (ρ.pointMatrix T) m (hasUnipotentProductBound_of_isUnipotent hG m ρ T)

/-- A faithful representation gives the same nilpotence bound on every test. -/
theorem hasUniformNilpotentPoints_of_mono (hG : IsUnipotent G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) [Mono ρ.hom.hom] :
    HasUniformNilpotentPoints G m := by
  intro T
  rw [eq_bot_iff]
  refine le_trans (lowerCentralSeries_le_ker_of_isUnipotent hG ρ T) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (pointMatrix_injective ρ T)]

end MatrixRepresentation

/-- Every affine unipotent group scheme of finite type has a uniform nilpotence
bound on all groups of points, including tests with nilpotents. -/
theorem exists_hasUniformNilpotentPoints_of_isUnipotent
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G) :
    ∃ d, HasUniformNilpotentPoints G d := by
  obtain ⟨m, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  exact ⟨m, MatrixRepresentation.hasUniformNilpotentPoints_of_mono hG ρ⟩

/-- Each all-test group of points is a nilpotent abstract group. -/
theorem isNilpotent_points_of_isUnipotent
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G)
    (T : Over (Spec (CommRingCat.of k))) : Group.IsNilpotent (T ⟶ G.X) := by
  obtain ⟨d, hd⟩ := exists_hasUniformNilpotentPoints_of_isUnipotent hG
  exact Subgroup.nilpotent_iff_lowerCentralSeries.2 ⟨d, hd T⟩

end Langlands.GroupScheme
