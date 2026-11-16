import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Inverse limits of compatible algebras over a complete local ring

For Step 2a of Murre's induction (Bourbaki exp. 294): over a complete local noetherian ring
`R`, the inverse limit of a tower of `R`-algebras `A (n+1) → A n` with kernels
`m^(n+1) A (n+1)` and `A 0` finite is a finite `R`-algebra whose quotients are the `A n`. -/

universe u

open IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

variable {R : Type u} [CommRing R] (A : ℕ → Type u) [∀ n, CommRing (A n)] [∀ n, Algebra R (A n)]
  (t : ∀ n, A (n + 1) →ₐ[R] A n)

/-- The inverse limit of the tower `t`: compatible sequences in the product. -/
def limitAlg : Subalgebra R (∀ n, A n) where
  carrier := {x | ∀ n, t n (x (n + 1)) = x n}
  mul_mem' {a b} ha hb n := by
    simp only [Set.mem_ofPred_eq, Pi.mul_apply, map_mul] at *
    rw [ha n, hb n]
  add_mem' {a b} ha hb n := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [ha n, hb n]
  algebraMap_mem' r n := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes]

/-- The projection of the inverse limit to `A n`. -/
def limitProj (n : ℕ) : limitAlg A t →ₐ[R] A n :=
  (Pi.evalAlgHom R A n).comp (limitAlg A t).val

@[simp]
lemma limitProj_apply (n : ℕ) (x : limitAlg A t) : limitProj A t n x = (x : ∀ n, A n) n := rfl

lemma limitProj_compat (n : ℕ) (x : limitAlg A t) :
    t n (limitProj A t (n + 1) x) = limitProj A t n x := x.2 n

lemma limit_ext {x y : limitAlg A t} (h : ∀ n, limitProj A t n x = limitProj A t n y) : x = y :=
  Subtype.ext (funext h)

/-- A compatible sequence defines an element of the inverse limit. -/
def limitMk (x : ∀ n, A n) (hx : ∀ n, t n (x (n + 1)) = x n) : limitAlg A t := ⟨x, hx⟩

@[simp]
lemma limitProj_limitMk (x : ∀ n, A n) (hx : ∀ n, t n (x (n + 1)) = x n) (n : ℕ) :
    limitProj A t n (limitMk A t x hx) = x n := rfl

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

/-- The inverse limit of a tower with surjective transition maps, kernels `m^(n+1) A (n+1)`
and `A 0` finite over `R` is finite over `R`, its projections are surjective, and their kernels
are `m^(n+1)` times the limit. -/
theorem limit_spec (ht : ∀ n, Function.Surjective (t n))
    (hker : ∀ n, LinearMap.ker (t n).toLinearMap = (maximalIdeal R) ^ (n + 1) • ⊤)
    (hfin : Module.Finite R (A 0)) :
    Module.Finite R (limitAlg A t) ∧ (∀ n, Function.Surjective (limitProj A t n)) ∧
      ∀ n, LinearMap.ker (limitProj A t n).toLinearMap =
        (maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R (limitAlg A t)) := by
  obtain ⟨L, _, _, _, _, hLfin, p, hp1, hp2, hp3, hp4, hp5⟩ :=
    AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective
      (maximalIdeal R) (IsNoetherian.noetherian _) (fun n ↦ A n) (fun n ↦ (t n).toLinearMap)
      ht hker hfin
  let Φ : L →ₗ[R] limitAlg A t :=
    { toFun := fun x ↦ limitMk A t (fun n ↦ p n x) (fun n ↦ hp1 n x)
      map_add' := fun x y ↦ limit_ext A t fun n ↦
        show p n (x + y) = p n x + p n y from map_add _ _ _
      map_smul' := fun r x ↦ limit_ext A t fun n ↦
        show p n (r • x) = r • p n x from map_smul _ _ _ }
  have hΦ : ∀ n x, limitProj A t n (Φ x) = p n x := fun _ _ ↦ rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    rw [← sub_eq_zero]
    apply hp2
    intro n
    rw [map_sub, ← hΦ, ← hΦ, hxy, sub_self]
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx⟩ := hp3 (fun n ↦ limitProj A t n z) (fun n ↦ limitProj_compat A t n z)
    exact ⟨x, limit_ext A t fun n ↦ by rw [hΦ, hx]⟩
  let e : L ≃ₗ[R] limitAlg A t := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hfinR : Module.Finite R (AdicCompletion (maximalIdeal R) R) :=
    Module.Finite.of_surjective (AdicCompletion.of (maximalIdeal R) R)
      (AdicCompletion.of_surjective _ _)
  have : Module.Finite R L := Module.Finite.trans (AdicCompletion (maximalIdeal R) R) L
  refine ⟨Module.Finite.equiv e, fun n z ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hp4 n z
    exact ⟨Φ x, by rw [hΦ, hx]⟩
  · have hcomp : (limitProj A t n).toLinearMap.comp e.toLinearMap = p n := by
      ext x; rfl
    have h1 : LinearMap.ker (p n) = (LinearMap.ker (limitProj A t n).toLinearMap).comap
        e.toLinearMap := by
      rw [← hcomp, LinearMap.ker_comp]
    rw [← Submodule.map_comap_eq_of_surjective e.surjective
      (LinearMap.ker (limitProj A t n).toLinearMap), ← h1, hp5, Submodule.map_smul'',
      Submodule.map_top, LinearEquiv.range]

section Ring

variable (ht : ∀ n, Function.Surjective (t n))
  (hker : ∀ n, LinearMap.ker (t n).toLinearMap = (maximalIdeal R) ^ (n + 1) • ⊤)
  (hfin : Module.Finite R (A 0))
include ht hker hfin

/-- The kernel of the `n`-th projection is the `(n+1)`-st power of `m` times the limit. -/
lemma limit_ker_eq (n : ℕ) :
    RingHom.ker (limitProj A t n) =
      ((maximalIdeal R).map (algebraMap R (limitAlg A t))) ^ (n + 1) := by
  have h := (limit_spec A t ht hker hfin).2.2 n
  ext x
  rw [RingHom.mem_ker, ← Ideal.map_pow]
  have : x ∈ ((maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R (limitAlg A t))) ↔
      x ∈ ((maximalIdeal R) ^ (n + 1)).map (algebraMap R (limitAlg A t)) := by
    rw [Ideal.smul_top_eq_map]; rfl
  rw [← this, ← h]
  rfl

/-- The limit is complete for the ideal generated by `m`. -/
theorem limit_isAdicComplete :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R (limitAlg A t))) (limitAlg A t) := by
  set J := (maximalIdeal R).map (algebraMap R (limitAlg A t))
  have hJ : ∀ n x, x ∈ J ^ (n + 1) ↔ limitProj A t n x = 0 := fun n x ↦ by
    rw [← limit_ker_eq A t ht hker hfin n, RingHom.mem_ker]
  have hsm : ∀ n, (J ^ n • ⊤ : Submodule (limitAlg A t) (limitAlg A t)) = J ^ n := fun n ↦ by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff J (limitAlg A t) := ⟨fun x hx ↦ limit_ext A t fun n ↦ by
    have := hx (n + 1)
    rw [SModEq.sub_mem, sub_zero, hsm] at this
    rw [(hJ n x).1 this, map_zero]⟩
  have hP : IsPrecomplete J (limitAlg A t) := ⟨fun f hf ↦ by
    have hc : ∀ k, limitProj A t k (f (k + 1)) = limitProj A t k (f (k + 2)) := fun k ↦ by
      have := hf (Nat.le_succ (k + 1))
      rw [SModEq.sub_mem, hsm, hJ, map_sub, sub_eq_zero] at this
      exact this
    refine ⟨limitMk A t (fun k ↦ limitProj A t k (f (k + 1))) (fun k ↦ ?_), fun n ↦ ?_⟩
    · rw [limitProj_compat, hc]
    · rw [SModEq.sub_mem, hsm]
      cases n with
      | zero => simp
      | succ k => rw [hJ, map_sub, limitProj_limitMk, sub_self]⟩
  exact {}

variable (h0 : IsField (A 0))
include h0

/-- If `A 0` is a field, the kernel of the projection to `A 0`, which is the ideal generated by
`m`, is maximal. -/
lemma limit_isMaximal :
    ((maximalIdeal R).map (algebraMap R (limitAlg A t))).IsMaximal := by
  have := limit_ker_eq A t ht hker hfin 0
  rw [pow_one] at this
  rw [← this]
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField h0
    (RingHom.quotientKerEquivOfSurjective ((limit_spec A t ht hker hfin).2.1 0)).toMulEquiv

/-- If `A 0` is a field, the limit is a local ring. -/
theorem limit_isLocalRing : IsLocalRing (limitAlg A t) := by
  have hmax := limit_isMaximal A t ht hker hfin h0
  have hc := limit_isAdicComplete A t ht hker hfin
  refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun I hI ↦ ?_⟩
  have hle : (maximalIdeal R).map (algebraMap R (limitAlg A t)) ≤ I :=
    (IsAdicComplete.le_jacobson_bot _).trans (sInf_le ⟨bot_le, hI⟩)
  exact (hmax.eq_of_le hI.ne_top hle).symm

/-- If `A 0` is a field, the maximal ideal of the limit is generated by `m`. -/
theorem limit_maximalIdeal :
    letI := limit_isLocalRing A t ht hker hfin h0
    maximalIdeal (limitAlg A t) = (maximalIdeal R).map (algebraMap R (limitAlg A t)) := by
  let := limit_isLocalRing A t ht hker hfin h0
  exact (IsLocalRing.eq_maximalIdeal (limit_isMaximal A t ht hker hfin h0)).symm

/-- If `A 0` is a field, formally unramified over `R`, the limit is formally unramified over
`R`: its maximal ideal is generated by `m` and its residue field embeds into `A 0`, hence is
separable over the residue field of `R`. -/
theorem limit_formallyUnramified [Algebra.FormallyUnramified R (A 0)] :
    letI := limit_isLocalRing A t ht hker hfin h0
    Algebra.FormallyUnramified R (limitAlg A t) := by
  let := limit_isLocalRing A t ht hker hfin h0
  let := h0.toField
  have hmax := limit_maximalIdeal A t ht hker hfin h0
  have hker0 := limit_ker_eq A t ht hker hfin 0
  rw [pow_one, ← hmax] at hker0
  have hloc : IsLocalHom (algebraMap R (limitAlg A t)) := ⟨fun r hr ↦ by
    by_contra h
    have : algebraMap R (limitAlg A t) r ∈ maximalIdeal (limitAlg A t) := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 h)
    exact (mem_maximalIdeal _).1 this hr⟩
  have hpr : IsLocalHom (limitProj A t 0 : limitAlg A t →+* A 0) := ⟨fun x hx ↦ by
    by_contra h
    have : limitProj A t 0 x = 0 := by
      rw [← RingHom.mem_ker, hker0]; exact (mem_maximalIdeal x).2 h
    change IsUnit (limitProj A t 0 x) at hx
    rw [this] at hx
    exact not_isUnit_zero hx⟩
  have hloc0 : IsLocalHom (algebraMap R (A 0)) := by
    have : algebraMap R (A 0) = (limitProj A t 0 : limitAlg A t →+* A 0).comp
        (algebraMap R (limitAlg A t)) := by
      ext r; exact ((limitProj A t 0).commutes r).symm
    rw [this]
    infer_instance
  have : Module.Finite R (A 0) := hfin
  have : Algebra.EssFiniteType R (A 0) := inferInstance
  have : Algebra.EssFiniteType R (limitAlg A t) := by
    have := (limit_spec A t ht hker hfin).1
    infer_instance
  let f : ResidueField (limitAlg A t) →ₐ[ResidueField R] ResidueField (A 0) :=
    { ResidueField.map (limitProj A t 0 : limitAlg A t →+* A 0) with
      commutes' := fun r ↦ by
        obtain ⟨r, rfl⟩ := residue_surjective r
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, ResidueField.algebraMap_residue, ResidueField.map_residue]
        exact congrArg (residue (A 0)) ((limitProj A t 0).commutes r) }
  have : Algebra.IsSeparable (ResidueField R) (ResidueField (limitAlg A t)) :=
    Algebra.IsSeparable.of_algHom _ _ f
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax.symm

omit h0 in
/-- The limit is noetherian. -/
theorem limit_isNoetherianRing : IsNoetherianRing (limitAlg A t) := by
  have := (limit_spec A t ht hker hfin).1
  exact isNoetherian_of_tower R (isNoetherian_of_isNoetherianRing_of_finite R (limitAlg A t))

end Ring

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
