/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Degreewise split free resolutions of a short exact sequence

Source: Stacks Project, Algebra, proof of Tag 065P
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u v₁ v₂ v₃

namespace Module

private structure ResolutionSES (R : Type u) [CommRing R] where
  A : Type v₁
  B : Type v₁
  C : Type v₁
  agA : AddCommGroup A
  agB : AddCommGroup B
  agC : AddCommGroup C
  modA : Module R A
  modB : Module R B
  modC : Module R C
  i : A →ₗ[R] B
  p : B →ₗ[R] C
  inj : Function.Injective i
  exact : Function.Exact i p
  surj : Function.Surjective p

private instance resolutionSESAddA {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : AddCommGroup E.A := E.agA

private instance resolutionSESAddB {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : AddCommGroup E.B := E.agB

private instance resolutionSESAddC {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : AddCommGroup E.C := E.agC

private instance resolutionSESModuleA {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Module R E.A := E.modA

private instance resolutionSESModuleB {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Module R E.B := E.modB

private instance resolutionSESModuleC {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Module R E.C := E.modC

private abbrev ResolutionSES.P {R : Type u} [CommRing R] (E : ResolutionSES.{u, v₁} R) :=
  E.A →₀ R

private abbrev ResolutionSES.T {R : Type u} [CommRing R] (E : ResolutionSES.{u, v₁} R) :=
  E.C →₀ R

private noncomputable def ResolutionSES.η {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : E.P →ₗ[R] E.A :=
  Finsupp.linearCombination R id

private noncomputable def ResolutionSES.θ {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : E.T →ₗ[R] E.C :=
  Finsupp.linearCombination R id

private noncomputable def ResolutionSES.lift {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : E.T →ₗ[R] E.B :=
  Finsupp.linearCombination R (fun c ↦ (E.surj c).choose)

private lemma ResolutionSES.p_lift {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) (z : E.T) : E.p (E.lift z) = E.θ z := by
  classical
  simp only [lift, θ, Finsupp.apply_linearCombination]
  have hfun : (⇑E.p ∘ fun c ↦ (E.surj c).choose) = id := by
    funext c
    exact (E.surj c).choose_spec
  rw [hfun]

private noncomputable def ResolutionSES.μ {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : E.P × E.T →ₗ[R] E.B :=
  (E.i.comp E.η).coprod E.lift

private lemma ResolutionSES.η_surj {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Surjective E.η :=
  Finsupp.linearCombination_id_surjective R E.A

private lemma ResolutionSES.θ_surj {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Surjective E.θ :=
  Finsupp.linearCombination_id_surjective R E.C

private lemma ResolutionSES.p_μ {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) (z : E.P × E.T) : E.p (E.μ z) = E.θ z.2 := by
  simp [μ, E.exact.apply_apply_eq_zero, E.p_lift]

private lemma ResolutionSES.μ_surj {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Surjective E.μ := by
  intro b
  obtain ⟨z, hz⟩ := E.θ_surj (E.p b)
  have h : E.p (b - E.lift z) = 0 := by simp [E.p_lift, hz]
  obtain ⟨a, ha⟩ := (E.exact (b - E.lift z)).mp h
  obtain ⟨x, hx⟩ := E.η_surj a
  refine ⟨(x, z), ?_⟩
  simp only [μ, LinearMap.coprod_apply, LinearMap.comp_apply, hx, ha]
  exact sub_add_cancel b (E.lift z)

private noncomputable def ResolutionSES.ki {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : LinearMap.ker E.η →ₗ[R] LinearMap.ker E.μ :=
  ((LinearMap.inl R E.P E.T).comp (LinearMap.ker E.η).subtype).codRestrict _ (by
    intro x
    simp [μ])

private noncomputable def ResolutionSES.kp {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : LinearMap.ker E.μ →ₗ[R] LinearMap.ker E.θ :=
  ((LinearMap.snd R E.P E.T).comp (LinearMap.ker E.μ).subtype).codRestrict _ (by
    intro x
    change E.θ x.val.2 = 0
    rw [← E.p_μ, x.property, map_zero])

private lemma ResolutionSES.ki_inj {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Injective E.ki := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z ↦ z.val.1) h

private lemma ResolutionSES.kernel_exact {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Exact E.ki E.kp := by
  intro y
  constructor
  · intro h
    have hy : y.val.2 = 0 := congrArg Subtype.val h
    have hx : E.η y.val.1 = 0 := by
      apply E.inj
      have hyμ : E.i (E.η y.val.1) + E.lift y.val.2 = 0 := y.property
      simpa only [hy, map_zero, add_zero] using hyμ
    refine ⟨⟨y.val.1, hx⟩, ?_⟩
    apply Subtype.ext
    change (y.val.1, 0) = y.val
    exact Prod.ext rfl hy.symm
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    rfl

private lemma ResolutionSES.kp_surj {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : Function.Surjective E.kp := by
  intro z
  have h : E.p (-E.lift z.val) = 0 := by simp [E.p_lift]
  obtain ⟨a, ha⟩ := (E.exact (-E.lift z.val)).mp h
  obtain ⟨x, hx⟩ := E.η_surj a
  have hμ : E.μ (x, z.val) = 0 := by simp [μ, hx, ha]
  refine ⟨⟨(x, z.val), hμ⟩, ?_⟩
  apply Subtype.ext
  rfl

private noncomputable def ResolutionSES.next {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, v₁} R) : ResolutionSES.{u, max u v₁} R where
  A := LinearMap.ker E.η
  B := LinearMap.ker E.μ
  C := LinearMap.ker E.θ
  agA := inferInstance
  agB := inferInstance
  agC := inferInstance
  modA := inferInstance
  modB := inferInstance
  modC := inferInstance
  i := E.ki
  p := E.kp
  inj := E.ki_inj
  exact := E.kernel_exact
  surj := E.kp_surj

private noncomputable def ResolutionSES.stage {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) : ℕ → ResolutionSES.{u, max u v₁} R
  | 0 => E
  | n + 1 => (E.stage n).next

private noncomputable def ResolutionSES.dA {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) (n : ℕ) :
    (E.stage (n + 1)).P →ₗ[R] (E.stage n).P :=
  (LinearMap.ker (E.stage n).η).subtype.comp (E.stage (n + 1)).η

private noncomputable def ResolutionSES.dB {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) (n : ℕ) :
    (E.stage (n + 1)).P × (E.stage (n + 1)).T →ₗ[R]
      (E.stage n).P × (E.stage n).T :=
  (LinearMap.ker (E.stage n).μ).subtype.comp (E.stage (n + 1)).μ

private noncomputable def ResolutionSES.dC {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) (n : ℕ) :
    (E.stage (n + 1)).T →ₗ[R] (E.stage n).T :=
  (LinearMap.ker (E.stage n).θ).subtype.comp (E.stage (n + 1)).θ

private lemma range_kernel_cover {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {N : Type v₂} [AddCommGroup N] [Module R N]
    {P : Type v₃} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : P →ₗ[R] LinearMap.ker f) (hg : Function.Surjective g) :
    LinearMap.range ((LinearMap.ker f).subtype.comp g) = LinearMap.ker f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (g y).property
  · intro hx
    obtain ⟨y, hy⟩ := hg ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

private lemma ker_kernel_cover {R : Type u} [CommRing R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    {N : Type v₂} [AddCommGroup N] [Module R N]
    {P : Type v₃} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : P →ₗ[R] LinearMap.ker f) :
    LinearMap.ker ((LinearMap.ker f).subtype.comp g) = LinearMap.ker g := by
  ext x
  change ((LinearMap.ker f).subtype (g x) = 0) ↔ g x = 0
  simp

private lemma ResolutionSES.exactA {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) :
    LinearMap.ker (E.stage 0).η = LinearMap.range (E.dA 0) ∧
      ∀ n, LinearMap.ker (E.dA n) = LinearMap.range (E.dA (n + 1)) := by
  constructor
  · exact (range_kernel_cover _ _ (E.stage 1).η_surj).symm
  · intro n
    rw [dA, ker_kernel_cover]
    exact (range_kernel_cover _ _ (E.stage (n + 1 + 1)).η_surj).symm

private lemma ResolutionSES.exactB {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) :
    LinearMap.ker (E.stage 0).μ = LinearMap.range (E.dB 0) ∧
      ∀ n, LinearMap.ker (E.dB n) = LinearMap.range (E.dB (n + 1)) := by
  constructor
  · exact (range_kernel_cover _ _ (E.stage 1).μ_surj).symm
  · intro n
    rw [dB, ker_kernel_cover]
    exact (range_kernel_cover _ _ (E.stage (n + 1 + 1)).μ_surj).symm

private lemma ResolutionSES.exactC {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) :
    LinearMap.ker (E.stage 0).θ = LinearMap.range (E.dC 0) ∧
      ∀ n, LinearMap.ker (E.dC n) = LinearMap.range (E.dC (n + 1)) := by
  constructor
  · exact (range_kernel_cover _ _ (E.stage 1).θ_surj).symm
  · intro n
    rw [dC, ker_kernel_cover]
    exact (range_kernel_cover _ _ (E.stage (n + 1 + 1)).θ_surj).symm

private lemma ResolutionSES.chainA {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) (n : ℕ) :
    (E.dB n).comp (LinearMap.inl R _ _) =
      (LinearMap.inl R _ _).comp (E.dA n) := by
  apply LinearMap.ext
  intro x
  change ((E.stage (n + 1)).μ (x, 0)).val =
    (((E.stage (n + 1)).η x).val, 0)
  simp only [μ, LinearMap.coprod_apply, LinearMap.comp_apply, map_zero, add_zero]
  rfl

private lemma ResolutionSES.chainC {R : Type u} [CommRing R]
    (E : ResolutionSES.{u, max u v₁} R) (n : ℕ) :
    (E.dC n).comp (LinearMap.snd R _ _) =
      (LinearMap.snd R _ _).comp (E.dB n) := by
  apply LinearMap.ext
  intro z
  change ((E.stage (n + 1)).θ z.2).val =
    ((E.stage (n + 1)).μ z).val.2
  exact congrArg Subtype.val ((E.stage (n + 1)).p_μ z).symm

/-- A short exact sequence of modules admits compatible free resolutions with split rows in
every degree. Source: Stacks Project, Algebra, proof of Tag 065P; Derived Categories,
Tag 064C (blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof plan:
1. For a short exact sequence A → A' → A'', choose generating families of A and A'' and
   lifts in A' of the latter. Take free modules P and P'' on these families and P' = P ⊕ P''.
   The generator maps give compatible surjections onto A, A', A''. Inclusion, projection,
   retraction and section satisfy the four splitting identities. Apply the snake lemma
   (lem-weil-pbc-snake-lemma-modules) to obtain a short exact sequence of kernels;
   surjectivity makes the cokernels zero (def-weil-pbc-exact-sequence).
2. Starting from the given sequence, repeat Step 1 on these kernels. At degree n take
   the resulting free modules (def-weil-pbc-free-module); define the next differential
   as the surjection onto the kernel followed by its inclusion. The initial surjections
   are the augmentations.
3. Each augmentation is surjective. Each differential has image equal to the preceding
   kernel, so the augmented complexes are exact. Compatibility of the kernel inclusions
   and surjections makes α and β chain maps and gives both augmentation squares. The four
   splitting identities hold by construction in every degree, hence all rows are split
   exact (def-weil-pbc-exact-sequence).

As in `Module.exists_finite_free_resolution`, the terms are a family `F : ℕ → Type _` and
`d i : F (i + 1) →ₗ[R] F i` is the node's `d_{i+1}`; exactness of the augmented complex is
surjectivity of `ε` and the kernel-image equalities (which imply `d ∘ d = 0`). Short
exactness of the given sequence is injectivity, `Function.Exact` and surjectivity, the
module form of def-weil-pbc-exact-sequence. The maps `π n` and `s n` are families of linear
maps, not chain maps. The free terms live in `Type (max u v₁ v₂ v₃)`, which holds free
modules on generating sets of all three modules. -/
theorem exists_free_resolution_ses_split
    (R : Type u) [CommRing R]
    {Q : Type v₁} [AddCommGroup Q] [Module R Q]
    {Q' : Type v₂} [AddCommGroup Q'] [Module R Q']
    {Q'' : Type v₃} [AddCommGroup Q''] [Module R Q'']
    (u : Q →ₗ[R] Q') (v : Q' →ₗ[R] Q'')
    (hu : Function.Injective u) (huv : Function.Exact u v) (hv : Function.Surjective v) :
    ∃ (F F' F'' : ℕ → Type (max u v₁ v₂ v₃))
      (_ : ∀ n, AddCommGroup (F n)) (_ : ∀ n, Module R (F n))
      (_ : ∀ n, AddCommGroup (F' n)) (_ : ∀ n, Module R (F' n))
      (_ : ∀ n, AddCommGroup (F'' n)) (_ : ∀ n, Module R (F'' n))
      (d : ∀ i : ℕ, F (i + 1) →ₗ[R] F i) (d' : ∀ i : ℕ, F' (i + 1) →ₗ[R] F' i)
      (d'' : ∀ i : ℕ, F'' (i + 1) →ₗ[R] F'' i)
      (ε : F 0 →ₗ[R] Q) (ε' : F' 0 →ₗ[R] Q') (ε'' : F'' 0 →ₗ[R] Q'')
      (α : ∀ n : ℕ, F n →ₗ[R] F' n) (β : ∀ n : ℕ, F' n →ₗ[R] F'' n)
      (π : ∀ n : ℕ, F' n →ₗ[R] F n) (s : ∀ n : ℕ, F'' n →ₗ[R] F' n),
      (∀ n : ℕ, Module.Free R (F n) ∧ Module.Free R (F' n) ∧ Module.Free R (F'' n)) ∧
      (Function.Surjective ε ∧ LinearMap.ker ε = LinearMap.range (d 0) ∧
        ∀ i : ℕ, LinearMap.ker (d i) = LinearMap.range (d (i + 1))) ∧
      (Function.Surjective ε' ∧ LinearMap.ker ε' = LinearMap.range (d' 0) ∧
        ∀ i : ℕ, LinearMap.ker (d' i) = LinearMap.range (d' (i + 1))) ∧
      (Function.Surjective ε'' ∧ LinearMap.ker ε'' = LinearMap.range (d'' 0) ∧
        ∀ i : ℕ, LinearMap.ker (d'' i) = LinearMap.range (d'' (i + 1))) ∧
      (∀ i : ℕ, d' i ∘ₗ α (i + 1) = α i ∘ₗ d i) ∧
      (∀ i : ℕ, d'' i ∘ₗ β (i + 1) = β i ∘ₗ d' i) ∧
      ε' ∘ₗ α 0 = u ∘ₗ ε ∧ ε'' ∘ₗ β 0 = v ∘ₗ ε' ∧
      ∀ n : ℕ, β n ∘ₗ α n = 0 ∧ π n ∘ₗ α n = LinearMap.id ∧
        β n ∘ₗ s n = LinearMap.id ∧ α n ∘ₗ π n + s n ∘ₗ β n = LinearMap.id := by
  classical
  let eA : ULift.{max u v₁ v₂ v₃} Q ≃ₗ[R] Q := ULift.moduleEquiv
  let eB : ULift.{max u v₁ v₂ v₃} Q' ≃ₗ[R] Q' := ULift.moduleEquiv
  let eC : ULift.{max u v₁ v₂ v₃} Q'' ≃ₗ[R] Q'' := ULift.moduleEquiv
  let E : ResolutionSES.{u, max u v₁ v₂ v₃} R := {
    A := ULift.{max u v₁ v₂ v₃} Q
    B := ULift.{max u v₁ v₂ v₃} Q'
    C := ULift.{max u v₁ v₂ v₃} Q''
    agA := inferInstance
    agB := inferInstance
    agC := inferInstance
    modA := inferInstance
    modB := inferInstance
    modC := inferInstance
    i := eB.symm.toLinearMap.comp (u.comp eA.toLinearMap)
    p := eC.symm.toLinearMap.comp (v.comp eB.toLinearMap)
    inj := by
      intro x y h
      apply eA.injective
      apply hu
      exact eB.symm.injective h
    exact := by
      intro y
      constructor
      · intro h
        have hy : v (eB y) = 0 := by
          have := congrArg eC h
          simpa using this
        obtain ⟨x, hx⟩ := (huv (eB y)).mp hy
        refine ⟨eA.symm x, ?_⟩
        apply eB.injective
        simpa using hx
      · rintro ⟨x, rfl⟩
        simp [huv.apply_apply_eq_zero]
    surj := by
      intro z
      obtain ⟨y, hy⟩ := hv (eC z)
      refine ⟨eB.symm y, ?_⟩
      apply eC.injective
      simpa using hy }
  -- Fix the residual universe parameter explicitly before building the dependent witnesses.
  let S := ResolutionSES.stage.{u, max v₁ v₂ v₃} E
  refine ⟨(fun n ↦ (S n).P), (fun n ↦ (S n).P × (S n).T), (fun n ↦ (S n).T),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance),
    ResolutionSES.dA.{u, max v₁ v₂ v₃} E, ResolutionSES.dB.{u, max v₁ v₂ v₃} E,
    ResolutionSES.dC.{u, max v₁ v₂ v₃} E,
    eA.toLinearMap.comp E.η, eB.toLinearMap.comp E.μ, eC.toLinearMap.comp E.θ,
    (fun _ ↦ LinearMap.inl R _ _), (fun _ ↦ LinearMap.snd R _ _),
    (fun _ ↦ LinearMap.fst R _ _), (fun _ ↦ LinearMap.inr R _ _), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ResolutionSES.chainA.{u, max v₁ v₂ v₃} E,
    ResolutionSES.chainC.{u, max v₁ v₂ v₃} E, ?_, ?_, ?_⟩
  · intro n
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · refine ⟨eA.surjective.comp E.η_surj, ?_, (ResolutionSES.exactA.{u, max v₁ v₂ v₃} E).2⟩
    rw [LinearMap.ker_comp_of_ker_eq_bot _ eA.ker]
    exact (ResolutionSES.exactA.{u, max v₁ v₂ v₃} E).1
  · refine ⟨eB.surjective.comp E.μ_surj, ?_, (ResolutionSES.exactB.{u, max v₁ v₂ v₃} E).2⟩
    rw [LinearMap.ker_comp_of_ker_eq_bot _ eB.ker]
    exact (ResolutionSES.exactB.{u, max v₁ v₂ v₃} E).1
  · refine ⟨eC.surjective.comp E.θ_surj, ?_, (ResolutionSES.exactC.{u, max v₁ v₂ v₃} E).2⟩
    rw [LinearMap.ker_comp_of_ker_eq_bot _ eC.ker]
    exact (ResolutionSES.exactC.{u, max v₁ v₂ v₃} E).1
  · apply LinearMap.ext
    intro x
    change eB (E.μ (x, 0)) = u (eA (E.η x))
    simp only [ResolutionSES.μ, LinearMap.coprod_apply, LinearMap.comp_apply,
      map_zero, add_zero]
    simp [E]
  · apply LinearMap.ext
    intro z
    change eC (E.θ z.2) = v (eB (E.μ z))
    rw [← E.p_μ]
    simp [E]
  · intro n
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;> simp

end Module
