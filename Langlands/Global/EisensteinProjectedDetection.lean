import Langlands.Global.EisensteinHolomorphicDetection
import Langlands.Global.EisensteinJetSubquotient

/-! # Detecting simple specializations on a compact projection -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

variable {R J Z Q : Type*} [Ring R]
  [AddCommGroup J] [Module R J] [AddCommGroup Z] [Module R Z]
  [AddCommGroup Q] [Module R Q] [IsSimpleModule R Q]

/-- The simultaneous vanishing submodule of a finite set of coefficients. -/
def jointCoefficientKernel {ι : Type*} (s : Finset ι) (c : ι → J →ₗ[R] Z) : Submodule R J :=
  ⨅ i ∈ s, (c i).ker

theorem mem_jointCoefficientKernel {ι : Type*} (s : Finset ι) (c : ι → J →ₗ[R] Z) (x : J) :
    x ∈ jointCoefficientKernel s c ↔ ∀ i ∈ s, c i x = 0 := by
  simp only [jointCoefficientKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- A finite coefficient test on the image of a projection suffices for
the entire simple specialization. The projection may be defined outside
the operator ring if it preserves each cyclic submodule. -/
theorem exists_subquotient_of_projected_coefficients {ι : Type*}
    (s : Finset ι) (c : ι → J →ₗ[R] Z) (q : J →ₗ[R] Q) (hq : Function.Surjective q)
    (P : J → J) (Pq : Q → Q) (hP : ∀ x, P (P x) = P x)
    (hspan : ∀ x : J, P x ∈ Submodule.span R {x})
    (hcomm : ∀ x, q (P x) = Pq (q x)) (hnonzero : ∃ y, Pq y ≠ 0)
    (hdetect : ∀ x, P x = x → (∀ i ∈ s, c i x = 0) → q x = 0) :
    ∃ U : Submodule R Z, ∃ f : U →ₗ[R] Q, Function.Surjective f := by
  have hqtop : Function.Surjective (q.comp (⊤ : Submodule R J).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  refine exists_subquotient_of_coefficients s c q ⊤ hqtop (fun x _ hx => ?_)
  by_contra hqx
  obtain ⟨y, hy⟩ := hnonzero
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective R hqx y
  have hat : q (a • x) = y := (q.map_smul a x).trans ha
  let K := jointCoefficientKernel s c
  have hxK : x ∈ K := (mem_jointCoefficientKernel s c x).mpr hx
  have hle : Submodule.span R {a • x} ≤ K :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (K.smul_mem a hxK))
  have h := hdetect (P (a • x)) (hP _)
    ((mem_jointCoefficientKernel s c _).mp (hle (hspan (a • x))))
  rw [hcomm, hat] at h
  exact hy h

variable {V X : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Module ℂ Z]

/-- In a holomorphic family with an injective member, the coefficients on
a finite-dimensional projected space detect a simple specialization. -/
theorem exists_subquotient_of_holomorphic_specialization
    (U : Set ℂ) (hU : IsPreconnected U) (z t₁ : ℂ) (hz : z ∈ U) (ht₁ : t₁ ∈ U)
    (E : ℂ → V →ₗ[ℂ] (X → ℂ)) (hE : ∀ v p, AnalyticOnNhd ℂ (fun t => E t v p) U)
    (hinj : Function.Injective (E t₁)) (sectionFamily : J → ℂ → V)
    (q : J →ₗ[R] Q) (hq : Function.Surjective q) (c : ℕ → J →ₗ[R] Z)
    (observe : Z →ₗ[ℂ] (X → ℂ))
    (P : J → J) (Pq : Q → Q) (hP : ∀ x, P (P x) = P x)
    (hspan : ∀ x : J, P x ∈ Submodule.span R {x})
    (hcomm : ∀ x, q (P x) = Pq (q x)) (hnonzero : ∃ y, Pq y ≠ 0)
    (hsection : ∀ x, P x = x → ∀ ℓ : V →ₗ[ℂ] ℂ,
      AnalyticAt ℂ (fun t => ℓ (sectionFamily x t)) z)
    (hcoefficient : ∀ x, P x = x → ∀ n p, observe (c n x) p =
      iteratedDeriv n (fun t => E t (sectionFamily x t) p) z / (n.factorial : ℂ))
    (hspecialize : ∀ x, P x = x → sectionFamily x z = 0 → q x = 0) :
    ∃ W : Submodule R Z, ∃ f : W →ₗ[R] Q, Function.Surjective f := by
  obtain ⟨d, hd⟩ := exists_derivativeDetectionOrder U hU z t₁ hz ht₁ E hE hinj
  refine exists_subquotient_of_projected_coefficients (Finset.range d) c q hq P Pq
    hP hspan hcomm hnonzero (fun x hx hzero => ?_)
  apply hspecialize x hx
  apply hd (sectionFamily x) (hsection x hx)
  intro p k
  have hk := hcoefficient x hx k p
  rw [hzero k (Finset.mem_range.mpr k.isLt), map_zero, Pi.zero_apply] at hk
  exact (div_eq_zero_iff.mp hk.symm).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end Langlands.Global.EisensteinJet
