import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Central.Basic

/-! # Galois descent of algebras along a semilinear Galois action -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.CentralSimple

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (B : Type v) [Ring B] [Algebra L B] [Algebra K B] [IsScalarTower K L B]

/-- A semilinear action of the Galois group `Gal(L/K)` on an `L`-algebra `B` by ring
automorphisms: each `σ` acts by a ring endomorphism that is `σ`-semilinear on the scalars
from `L`, and the action is a group action. -/
structure SemilinearGaloisAction where
  /-- The action of a Galois automorphism, as a ring endomorphism. -/
  act : (L ≃ₐ[K] L) → B →+* B
  act_algebraMap : ∀ σ l, act σ (algebraMap L B l) = algebraMap L B (σ l)
  act_one : ∀ b, act 1 b = b
  act_mul : ∀ σ τ b, act (σ * τ) b = act σ (act τ b)

namespace SemilinearGaloisAction

variable {K L B} (ρ : SemilinearGaloisAction K L B)

theorem act_algebraMap_base (σ : L ≃ₐ[K] L) (k : K) :
    ρ.act σ (algebraMap K B k) = algebraMap K B k := by
  rw [IsScalarTower.algebraMap_apply K L B, ρ.act_algebraMap, AlgEquiv.commutes]

/-- The `K`-subalgebra of elements fixed by every Galois automorphism. -/
def fixed : Subalgebra K B where
  carrier := {b | ∀ σ, ρ.act σ b = b}
  mul_mem' ha hb σ := by rw [map_mul, ha σ, hb σ]
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  algebraMap_mem' k σ := ρ.act_algebraMap_base σ k

theorem mem_fixed {b : B} : b ∈ ρ.fixed ↔ ∀ σ, ρ.act σ b = b := Iff.rfl

theorem act_fixed (σ : L ≃ₐ[K] L) (a : ρ.fixed) : ρ.act σ (a : B) = a := a.2 σ

/-- The scalar copy of `L` in `B` commutes with every element. -/
theorem algebraMap_commute (l : L) (y : B) : algebraMap L B l * y = y * algebraMap L B l :=
  Algebra.commutes l y

/-- The multiplication map `L ⊗[K] B^G → B`. -/
def mulMap : L ⊗[K] ρ.fixed →ₐ[L] B :=
  Algebra.TensorProduct.lift (Algebra.ofId L B) ρ.fixed.val
    (fun l a => by exact Algebra.commute_algebraMap_left l (a : B))

@[simp]
theorem mulMap_tmul (l : L) (a : ρ.fixed) :
    ρ.mulMap (l ⊗ₜ[K] a) = algebraMap L B l * a :=
  Algebra.TensorProduct.lift_tmul _ _ _ l a

variable [FiniteDimensional K L]

/-- The Galois trace `b ↦ ∑ σ, σ • b`, with values in the fixed subalgebra. -/
def trace : B →ₗ[K] ρ.fixed where
  toFun b := ⟨∑ σ, ρ.act σ b, fun τ => by
    rw [map_sum]
    simp_rw [← ρ.act_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)⟩
  map_add' x y := by
    apply Subtype.ext
    simp [Finset.sum_add_distrib]
  map_smul' k x := by
    apply Subtype.ext
    simp [Algebra.smul_def, ρ.act_algebraMap_base, Finset.mul_sum]

theorem coe_trace (b : B) : (ρ.trace b : B) = ∑ σ, ρ.act σ b := rfl

theorem trace_fixed_mul (a : ρ.fixed) (y : B) : ρ.trace ((a : B) * y) = a * ρ.trace y := by
  apply Subtype.ext
  simp [coe_trace, ρ.act_fixed, Finset.mul_sum]

theorem trace_mul_fixed (y : B) (a : ρ.fixed) : ρ.trace (y * (a : B)) = ρ.trace y * a := by
  apply Subtype.ext
  simp [coe_trace, ρ.act_fixed, Finset.sum_mul]

/-- The bilinear pieces of the inverse of the multiplication map. -/
def descentAux : L →ₗ[K] L →ₗ[K] B →ₗ[K] L ⊗[K] ρ.fixed :=
  LinearMap.mk₂ K
    (fun a b => (TensorProduct.mk K L ρ.fixed a) ∘ₗ ρ.trace ∘ₗ
      LinearMap.mulLeft K (algebraMap L B b))
    (fun a a' b => by ext y; simp)
    (fun k a b => by ext y; simp [TensorProduct.smul_tmul'])
    (fun a b b' => by ext y; simp [add_mul, TensorProduct.tmul_add])
    (fun k a b => by
      ext y
      simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      rw [← Algebra.smul_def, map_smul, TensorProduct.tmul_smul])

/-- For `t ∈ L ⊗[K] L`, the `K`-linear map `B → L ⊗[K] B^G` sending `y` to
`∑ aᵢ ⊗ tr(bᵢ y)` when `t = ∑ aᵢ ⊗ bᵢ`. -/
def descentMap (t : L ⊗[K] L) : B →ₗ[K] L ⊗[K] ρ.fixed :=
  TensorProduct.lift ρ.descentAux t

theorem descentMap_tmul (a b : L) (y : B) :
    ρ.descentMap (a ⊗ₜ[K] b) y = a ⊗ₜ[K] ρ.trace (algebraMap L B b * y) := by
  simp [descentMap, descentAux]

theorem trace_algebraMap_mul [IsGalois K L] (x : L) (a : ρ.fixed) :
    ρ.trace (algebraMap L B x * a) = Algebra.trace K L x • a := by
  apply Subtype.ext
  rw [coe_trace]
  simp only [map_mul, ρ.act_algebraMap, ρ.act_fixed]
  rw [← Finset.sum_mul, ← map_sum, ← trace_eq_sum_automorphisms,
    ← IsScalarTower.algebraMap_apply, Subalgebra.coe_smul, Algebra.smul_def]

theorem mulMap_descentMap_eq_sum (t : L ⊗[K] L) (y : B) :
    ρ.mulMap (ρ.descentMap t y) =
      ∑ σ, GroupScheme.Descent.galoisTensorHom K L t σ • ρ.act σ y := by
  induction t with
  | tmul a b =>
    rw [descentMap_tmul, mulMap_tmul, coe_trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Algebra.smul_def, ρ.act_algebraMap, mul_assoc]
  | add t t' ht ht' =>
    simp only [descentMap, map_add, LinearMap.add_apply] at ht ht' ⊢
    rw [ht, ht', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [add_smul]

theorem descentMap_mulMap_eq [IsGalois K L] (t : L ⊗[K] L) (x : L) (a : ρ.fixed) :
    ρ.descentMap t (algebraMap L B x * a) =
      (∑ σ, GroupScheme.Descent.galoisTensorHom K L t σ * σ x) ⊗ₜ[K] a := by
  induction t with
  | tmul a' b =>
    rw [descentMap_tmul, ← mul_assoc, ← map_mul, trace_algebraMap_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, trace_eq_sum_automorphisms, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [GroupScheme.Descent.galoisTensorHom_tmul, map_mul]
    ring
  | add t t' ht ht' =>
    simp only [descentMap, map_add, LinearMap.add_apply] at ht ht' ⊢
    rw [ht, ht', ← TensorProduct.add_tmul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [add_mul]

/-- An element of `L ⊗[K] L` whose Galois evaluation tuple is the indicator of the identity. -/
theorem exists_galoisTensorHom_eq_indicator :
    ∃ t : L ⊗[K] L, GroupScheme.Descent.galoisTensorHom K L t 1 = 1 ∧
      ∀ σ : L ≃ₐ[K] L, σ ≠ 1 → GroupScheme.Descent.galoisTensorHom K L t σ = 0 := by
  classical
  obtain ⟨t, ht⟩ := GroupScheme.Descent.galoisTensorHom_surjective K L
    (Pi.single (1 : L ≃ₐ[K] L) (1 : L))
  exact ⟨t, by rw [ht]; simp, fun σ hσ => by rw [ht]; simp [hσ]⟩

theorem sum_indicator_smul {M : Type*} [AddCommMonoid M] [Module L M]
    (g : (L ≃ₐ[K] L) → L) (h1 : g 1 = 1) (h0 : ∀ σ, σ ≠ 1 → g σ = 0)
    (f : (L ≃ₐ[K] L) → M) :
    ∑ σ, g σ • f σ = f 1 := by
  rw [Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · rw [h1, one_smul]
  · intro σ _ hσ
    rw [h0 σ hσ, zero_smul]
  · simp

variable [IsGalois K L]

/-- The multiplication map `L ⊗[K] B^G → B` is bijective. -/
theorem mulMap_bijective : Function.Bijective ρ.mulMap := by
  obtain ⟨t, ht1, ht0⟩ := exists_galoisTensorHom_eq_indicator (K := K) (L := L)
  have hright : Function.RightInverse (ρ.descentMap t) ρ.mulMap := by
    intro y
    rw [mulMap_descentMap_eq_sum, sum_indicator_smul _ ht1 ht0, ρ.act_one]
  have hleft : Function.LeftInverse (ρ.descentMap t) ρ.mulMap := by
    intro z
    induction z with
    | tmul x a =>
      rw [mulMap_tmul, descentMap_mulMap_eq]
      congr 1
      simpa [smul_eq_mul] using sum_indicator_smul _ ht1 ht0 (fun σ => σ x)
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  exact ⟨hleft.injective, hright.surjective⟩

/-- Galois descent: the fixed subalgebra is a `K`-form of `B`. -/
def descentEquiv : L ⊗[K] ρ.fixed ≃ₐ[L] B :=
  AlgEquiv.ofBijective ρ.mulMap ρ.mulMap_bijective

@[simp]
theorem descentEquiv_tmul (l : L) (a : ρ.fixed) :
    ρ.descentEquiv (l ⊗ₜ[K] a) = algebraMap L B l * a :=
  ρ.mulMap_tmul l a

theorem descentEquiv_one_tmul (a : ρ.fixed) : ρ.descentEquiv (1 ⊗ₜ[K] a) = a := by
  simp

/-- Every element of `B` is an `L`-combination of fixed elements; an induction principle. -/
theorem induction_on {P : B → Prop} (y : B)
    (add : ∀ y y', P y → P y' → P (y + y'))
    (tmul : ∀ (l : L) (a : ρ.fixed), P (algebraMap L B l * a)) : P y := by
  obtain ⟨z, rfl⟩ := ρ.mulMap_bijective.2 y
  induction z with
  | tmul x a => simpa using tmul x a
  | add z z' hz hz' => simpa [map_add] using add _ _ hz hz'

omit [IsGalois K L] in
/-- The fixed subalgebra of a finite-dimensional algebra is finite-dimensional. -/
theorem finiteDimensional_fixed [FiniteDimensional L B] : FiniteDimensional K ρ.fixed := by
  have : FiniteDimensional K B := Module.Finite.trans L B
  infer_instance

/-- The fixed subalgebra of a central algebra is central. -/
theorem isCentral_fixed [Algebra.IsCentral L B] [Nontrivial B] :
    Algebra.IsCentral K ρ.fixed where
  out z hz := by
    rw [Subalgebra.mem_center_iff] at hz
    have hcomm : ∀ y : B, y * (z : B) = (z : B) * y := by
      intro y
      refine ρ.induction_on (P := fun y => y * (z : B) = (z : B) * y) y
        (fun y y' h h' => by rw [add_mul, mul_add, h, h'])
        (fun l a => ?_)
      have ha : (a : B) * z = z * a := congrArg Subtype.val (hz a)
      rw [mul_assoc, ha, ← mul_assoc, algebraMap_commute, mul_assoc]
    have hzc : (z : B) ∈ Subalgebra.center L B := Subalgebra.mem_center_iff.mpr hcomm
    obtain ⟨l, hl⟩ := (Algebra.IsCentral.mem_center_iff L).mp hzc
    have hfix : ∀ σ : L ≃ₐ[K] L, σ l = l := by
      intro σ
      apply (algebraMap L B).injective
      rw [← ρ.act_algebraMap, ← hl, ρ.act_fixed]
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed l).mpr hfix)
    refine Algebra.mem_bot.mpr ⟨k, Subtype.ext ?_⟩
    rw [hl, ← hk, ← IsScalarTower.algebraMap_apply]
    rfl

/-- The fixed subalgebra of a simple algebra is simple. -/
theorem isSimpleRing_fixed [IsSimpleRing B] : IsSimpleRing ρ.fixed := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  rw [or_iff_not_imp_left, ← I.one_mem_iff]
  intro hI
  obtain ⟨a, haI, ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  rw [TwoSidedIdeal.mem_bot] at ha0
  have zero_mem : ∀ l : L, ρ.trace (algebraMap L B l * 0) ∈ I := by simp
  let J : TwoSidedIdeal B := TwoSidedIdeal.mk' {y | ∀ l : L, ρ.trace (algebraMap L B l * y) ∈ I}
    zero_mem
    (fun {x y} hx hy l => by rw [mul_add, map_add]; exact I.add_mem (hx l) (hy l))
    (fun {x} hx l => by rw [mul_neg, map_neg]; exact I.neg_mem (hx l))
    (fun {x y} hy => by
      refine ρ.induction_on (P := fun x => ∀ l : L, ρ.trace (algebraMap L B l * (x * y)) ∈ I)
        x (fun x x' h h' l => by
          rw [add_mul, mul_add, map_add]; exact I.add_mem (h l) (h' l)) (fun l' p l => ?_)
      have : algebraMap L B l * (algebraMap L B l' * p * y) =
          p * (algebraMap L B (l * l') * y) := by
        calc algebraMap L B l * (algebraMap L B l' * p * y)
            = algebraMap L B l * algebraMap L B l' * p * y := by simp only [mul_assoc]
          _ = p * (algebraMap L B l * algebraMap L B l') * y := by
            rw [← map_mul, algebraMap_commute]
          _ = p * (algebraMap L B (l * l') * y) := by rw [map_mul, mul_assoc]
      rw [this, trace_fixed_mul]
      exact I.mul_mem_left _ _ (hy _))
    (fun {x y} hx => by
      refine ρ.induction_on (P := fun y => ∀ l : L, ρ.trace (algebraMap L B l * (x * y)) ∈ I)
        y (fun y y' h h' l => by
          rw [mul_add, mul_add, map_add]; exact I.add_mem (h l) (h' l)) (fun l' p l => ?_)
      have : algebraMap L B l * (x * (algebraMap L B l' * p)) =
          algebraMap L B (l * l') * x * p := by
        rw [← mul_assoc x, ← algebraMap_commute l' x, map_mul]
        simp only [mul_assoc]
      rw [this, trace_mul_fixed]
      exact I.mul_mem_right _ _ (hx _))
  have haJ : (a : B) ∈ J := by
    rw [TwoSidedIdeal.mem_mk']
    intro l
    rw [trace_algebraMap_mul, Algebra.smul_def]
    exact I.mul_mem_left _ _ haI
  have ha0' : (a : B) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have h1J : (1 : B) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J ha0' haJ
  rw [TwoSidedIdeal.mem_mk'] at h1J
  obtain ⟨l, hl⟩ := Algebra.trace_surjective K L 1
  have h := h1J l
  rw [show (1 : B) = ((1 : ρ.fixed) : B) from rfl, trace_algebraMap_mul, hl, one_smul] at h
  exact h

/-- The reduced degree of the fixed subalgebra is read off from a matrix chart of `B`. -/
theorem reducedDegree_fixed {m : ℕ} (e : B ≃ₐ[L] Matrix (Fin m) (Fin m) L) :
    reducedDegree K ρ.fixed = m :=
  (matrix_size_eq_reducedDegree K ρ.fixed L m (ρ.descentEquiv.trans e)).symm

end SemilinearGaloisAction

end Langlands.CentralSimple
