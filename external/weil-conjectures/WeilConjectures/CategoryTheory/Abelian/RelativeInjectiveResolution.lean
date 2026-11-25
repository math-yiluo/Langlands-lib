/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Resolutions over a complex

Let `C` be an abelian category with enough injectives, `K` a cochain complex in `C` (indexed by
`ℕ`) and `κ : M ⟶ K⁰` a morphism with `κ ≫ d = 0`. We construct a resolution
`M ⟶ A⁰ ⟶ A¹ ⟶ ⋯` of `M` together with a cochain map `c : A ⟶ K` extending `κ`, where
`Aⁿ = Eⁿ ⊞ Kⁿ` with `Eⁿ` injective (`CochainComplex.OverResolution`). It has the following
universal property (`CochainComplex.OverResolution.exists_lift`): for every resolution
`ε : M ⟶ P` and every cochain map `u : P ⟶ K` extending `κ`, there is a cochain map
`a : P ⟶ A` over `M` with `a ≫ c = u`.

Since `K` need not consist of injective objects, a cochain map from a resolution of `M` to `K`
extending `κ` need not exist, and two of them need not be homotopic; the complex `A` replaces
an injective resolution of `M` in this situation. If the terms of `K` are acyclic for a left
exact functor `F`, then so are the terms of `A`, and the maps `H^q(F u)` all factor through
`H^q(F c)` (`CochainComplex.OverResolution.rightDerivedObjIsoOfResolution_comp`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Injective HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A short complex `X ⟶ Y ⟶ Z` is exact as soon as `g` followed by some morphism `q` is the
cokernel of `f` followed by a monomorphism. -/
lemma exact_of_comp_eq_cokernel_π_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (q : Z ⟶ W) (m : cokernel f ⟶ W) [Mono m] (h : g ≫ q = cokernel.π f ≫ m) :
    (ShortComplex.mk f g w).Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  dsimp
  rw [← cancel_mono m, Category.assoc, ← h, kernel.condition_assoc, zero_comp, zero_comp]

variable [EnoughInjectives C] (K : CochainComplex C ℕ) {M : C} (κ : M ⟶ K.X 0)
  (hκ : κ ≫ K.d 0 1 = 0)

namespace OverResolution

/-- One step of the construction of `CochainComplex.OverResolution`: a morphism
`d : X₀ ⟶ X₁` and the projection `p : X₁ ⟶ Kⁿ`. -/
structure Step (n : ℕ) where
  /-- The source of the differential. -/
  X₀ : C
  /-- The target of the differential. -/
  X₁ : C
  /-- The differential. -/
  d : X₀ ⟶ X₁
  /-- The projection to `Kⁿ`. -/
  p : X₁ ⟶ K.X n

/-- The steps of the construction of `CochainComplex.OverResolution`. -/
def step : (n : ℕ) → Step K n
  | 0 => ⟨M, under M ⊞ K.X 0, biprod.lift (Injective.ι M) κ, biprod.snd⟩
  | n + 1 =>
    ⟨(step n).X₁, under (cokernel (step n).d) ⊞ K.X (n + 1),
      biprod.lift (cokernel.π (step n).d ≫ Injective.ι _) ((step n).p ≫ K.d n (n + 1)),
      biprod.snd⟩

lemma step_zero_d : (step K κ 0).d = biprod.lift (Injective.ι M) κ := rfl

lemma step_succ_d (n : ℕ) : (step K κ (n + 1)).d =
    biprod.lift (cokernel.π (step K κ n).d ≫ Injective.ι _) ((step K κ n).p ≫ K.d n (n + 1)) :=
  rfl

@[reassoc (attr := simp)]
lemma step_d_fst (n : ℕ) : (step K κ (n + 1)).d ≫ biprod.fst =
    cokernel.π (step K κ n).d ≫ Injective.ι _ :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma step_d_p (n : ℕ) : (step K κ (n + 1)).d ≫ (step K κ (n + 1)).p =
    (step K κ n).p ≫ K.d n (n + 1) :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma step_zero_d_p : (step K κ 0).d ≫ (step K κ 0).p = κ :=
  biprod.lift_snd _ _

include hκ in
@[reassoc (attr := simp)]
lemma step_d_d (n : ℕ) : (step K κ n).d ≫ (step K κ (n + 1)).d = 0 := by
  rw [step_succ_d]
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst, cokernel.condition_assoc, zero_comp, zero_comp]
  · rw [Category.assoc, biprod.lift_snd, zero_comp]
    cases n with
    | zero => rw [step_zero_d_p_assoc, hκ]
    | succ n => rw [step_d_p_assoc, K.d_comp_d, comp_zero]

instance mono_step_zero_d : Mono (step K κ 0).d := by
  have := Injective.ι_mono M
  rw [step_zero_d]
  exact mono_of_mono_fac (biprod.lift_fst (Injective.ι M) κ)

include hκ in
lemma exact_step (n : ℕ) :
    (ShortComplex.mk _ _ (step_d_d K κ hκ n)).Exact :=
  exact_of_comp_eq_cokernel_π_comp _ _ _ biprod.fst (Injective.ι _) (step_d_fst K κ n)

end OverResolution

open OverResolution

/-- The **resolution of `M` over `K`**: the complex `Aⁿ = Eⁿ ⊞ Kⁿ`, with `Eⁿ` injective, with
the differential `(e, k) ↦ (π(e, k), d k)` where `π` is the cokernel of the previous
differential followed by an embedding into an injective object. -/
def OverResolution : CochainComplex C ℕ :=
  CochainComplex.of (fun n ↦ (step K κ n).X₁) (fun n ↦ (step K κ (n + 1)).d)
    (fun n ↦ step_d_d K κ hκ (n + 1))

namespace OverResolution

@[simp]
lemma d_succ (n : ℕ) : (OverResolution K κ hκ).d n (n + 1) = (step K κ (n + 1)).d := by
  simp [OverResolution]

/-- The augmentation `M ⟶ A⁰`. -/
def ι : (single₀ C).obj M ⟶ OverResolution K κ hκ :=
  (fromSingle₀Equiv _ _).symm ⟨(step K κ 0).d, by
    rw [d_succ]
    exact step_d_d K κ hκ 0⟩

@[simp]
lemma ι_f_zero : (ι K κ hκ).f 0 = (step K κ 0).d := by
  simp [ι, fromSingle₀Equiv]

/-- The cochain map `c : A ⟶ K`, the projection on the second factor. -/
def c : OverResolution K κ hκ ⟶ K where
  f n := (step K κ n).p
  comm' := by
    rintro n _ rfl
    rw [d_succ]
    exact (step_d_p K κ n).symm

@[simp]
lemma c_f (n : ℕ) : (c K κ hκ).f n = (step K κ n).p := rfl

@[reassoc (attr := simp)]
lemma ι_f_zero_c_f_zero : (ι K κ hκ).f 0 ≫ (c K κ hκ).f 0 = κ := by
  rw [ι_f_zero, c_f, step_zero_d_p]

instance quasiIso_ι : QuasiIso (ι K κ hκ) := ⟨fun n ↦ by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨exact_step K κ hκ 0, mono_step_zero_d K κ⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
        (by simp only [CochainComplex.next]; rfl)]
      refine (ShortComplex.exact_iff_of_iso ?_).2 (exact_step K κ hκ (n + 1))
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

/-- The terms of the resolution over `K` are `Eⁿ ⊞ Kⁿ` with `Eⁿ` injective. -/
lemma exists_iso_biprod (n : ℕ) : ∃ (E : C) (_ : Injective E),
    Nonempty ((OverResolution K κ hκ).X n ≅ E ⊞ K.X n) := by
  cases n with
  | zero => exact ⟨under M, inferInstance, ⟨Iso.refl _⟩⟩
  | succ n => exact ⟨under (cokernel (step K κ n).d), inferInstance, ⟨Iso.refl _⟩⟩

/-! ### The universal property -/

variable {K κ hκ} {P : CochainComplex C ℕ} (ε : (single₀ C).obj M ⟶ P) [QuasiIso ε]
  (u : P ⟶ K) (hu : ε.f 0 ≫ u.f 0 = κ)

/-- The first component of the lift `P ⟶ A` in degree `0`. -/
def liftZero : P.X 0 ⟶ under M :=
  factorThru (Injective.ι M) (ε.f 0)

@[reassoc (attr := simp)]
lemma comp_liftZero : ε.f 0 ≫ liftZero ε = Injective.ι M :=
  comp_factorThru _ _

include hu in
lemma ε_comp_lift_zero :
    ε.f 0 ≫ (biprod.lift (liftZero ε) (u.f 0) : P.X 0 ⟶ under M ⊞ K.X 0) = (step K κ 0).d := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [step_zero_d, hu]

/-- The data of the lift `P ⟶ A` in degrees `n` and `n + 1`. -/
structure LiftData (n : ℕ) where
  /-- The lift in degree `n`. -/
  a : P.X n ⟶ (step K κ n).X₁
  /-- The lift in degree `n + 1`. -/
  a' : P.X (n + 1) ⟶ (step K κ (n + 1)).X₁
  ha : a ≫ (step K κ n).p = u.f n
  ha' : a' ≫ (step K κ (n + 1)).p = u.f (n + 1)
  comm : a ≫ (step K κ (n + 1)).d = P.d n (n + 1) ≫ a'

include hu in
lemma lift_comm_zero_aux :
    ε.f 0 ≫ (biprod.lift (liftZero ε) (u.f 0) : P.X 0 ⟶ under M ⊞ K.X 0) ≫
      cokernel.π (step K κ 0).d ≫ Injective.ι _ = 0 := by
  rw [← Category.assoc, ε_comp_lift_zero ε u hu, cokernel.condition_assoc, zero_comp]

/-- The lift in degrees `0` and `1`. -/
def liftDataZero : LiftData (κ := κ) u 0 where
  a := biprod.lift (liftZero ε) (u.f 0)
  a' := biprod.lift ((exact₀_of_quasiIso_single₀ ε).descToInjective
      ((biprod.lift (liftZero ε) (u.f 0) : P.X 0 ⟶ under M ⊞ K.X 0) ≫
        cokernel.π (step K κ 0).d ≫ Injective.ι _) (lift_comm_zero_aux ε u hu))
    (u.f 1)
  ha := biprod.lift_snd _ _
  ha' := biprod.lift_snd _ _
  comm := by
    rw [step_succ_d]
    refine biprod.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, biprod.lift_fst]
      exact ((exact₀_of_quasiIso_single₀ ε).comp_descToInjective _ _).symm
    · simp only [Category.assoc, biprod.lift_snd]
      erw [biprod.lift_snd_assoc]
      exact u.comm 0 1

/-- The lift in degrees `n + 1` and `n + 2`, from the lift in degrees `n` and `n + 1`. -/
def liftDataSucc {n : ℕ} (D : LiftData (κ := κ) u n) : LiftData (κ := κ) u (n + 1) where
  a := D.a'
  a' := biprod.lift ((exact_succ_of_quasiIso_single₀ ε n).descToInjective
      (D.a' ≫ cokernel.π (step K κ (n + 1)).d ≫ Injective.ι _) (by
        dsimp
        rw [← Category.assoc, ← D.comm, Category.assoc, cokernel.condition_assoc, zero_comp,
          comp_zero]))
    (u.f (n + 2))
  ha := D.ha'
  ha' := biprod.lift_snd _ _
  comm := by
    rw [step_succ_d]
    refine biprod.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, biprod.lift_fst]
      exact ((exact_succ_of_quasiIso_single₀ ε n).comp_descToInjective _ _).symm
    · simp only [Category.assoc, biprod.lift_snd]
      rw [← Category.assoc, D.ha']
      exact u.comm _ _

/-- The lifts in all degrees. -/
def liftData : (n : ℕ) → LiftData (κ := κ) u n
  | 0 => liftDataZero ε u hu
  | n + 1 => liftDataSucc ε u (liftData n)

lemma liftData_succ_a (n : ℕ) : (liftData ε u hu (n + 1)).a = (liftData ε u hu n).a' := rfl

/-- The lift `P ⟶ A` of a cochain map `u : P ⟶ K` extending `κ`. -/
def lift : P ⟶ OverResolution K κ hκ where
  f n := (liftData ε u hu n).a
  comm' := by
    rintro n _ rfl
    rw [d_succ, (liftData ε u hu n).comm, liftData_succ_a]

@[reassoc (attr := simp)]
lemma lift_c : lift ε u hu ≫ c K κ hκ = u := by
  ext n
  exact (liftData ε u hu n).ha

@[reassoc (attr := simp)]
lemma comp_lift : ε ≫ lift ε u hu = ι K κ hκ := by
  ext
  simp only [HomologicalComplex.comp_f, ι_f_zero]
  exact ε_comp_lift_zero ε u hu

include hu in
/-- **The universal property of the resolution over `K`.** Every resolution `ε : M ⟶ P` with a
cochain map `u : P ⟶ K` extending `κ` maps to `A` over `M`, compatibly with `u`. -/
theorem exists_lift : ∃ a : P ⟶ OverResolution K κ hκ, ε ≫ a = ι K κ hκ ∧ a ≫ c K κ hκ = u :=
  ⟨lift ε u hu, comp_lift ε u hu, lift_c ε u hu⟩

end OverResolution

end CochainComplex
