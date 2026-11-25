/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionMap

/-!
# Additivity of the cup product with the class of a `ℤ/m`-torsor

Let `T` be a `ℤ/m × ℤ/m`-torsor over `Y`, with total space `π : Q ⟶ Y`, and let `D₁`, `D₂` be the
differences `τ - 𝟙` of the translations by the two generators on `π_* μ_m`. With `N` the
invariants (`D₁ = D₂ = 0`) and `V` the sections with `D₁ v, D₂ v ∈ N`, there is a short exact
sequence `0 ⟶ N ⟶ V ⟶ N ⊞ N ⟶ 0` (`AlgebraicGeometry.Scheme.EtaleTorsor.pairSeq_shortExact`),
and `N ≅ μ_m` (`AlgebraicGeometry.Scheme.EtaleTorsor.isIso_pairUnit`). Locally `V` consists of
the functions `(a, b) ↦ x + a c₁ + b c₂`.

If `t` is a `ℤ/m`-torsor with a morphism `h : Q ⟶ P` over `Y` under which the generators act as
`c₁` and `c₂`, pulling back functions along `h` maps the extension
`0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0` of `t` to this sequence, by `(c₁, c₂)` on the quotient. Applied to the
three torsors `t₁`, `t₂`, `t₃` obtained from `T` along the projections and the sum, this gives
`t₃.cupMu = t₁.cupMu + t₂.cupMu` (`AlgebraicGeometry.Scheme.EtaleTorsor.cupMu_eq_add`): the
cup product is additive in the class of the torsor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section Algebra

variable {m : ℕ} [NeZero m] {A : Type*} [AddCommGroup A]

omit [AddCommGroup A] in
/-- A function on `ℤ/m × ℤ/m` invariant under the shifts by `-e₁` and `-e₂` is constant. -/
lemma apply_eq_apply_zero_of_forall_sub_pair
    {F : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m) → A}
    (h₁ : ∀ a, F (a - (1, 0)) = F a) (h₂ : ∀ a, F (a - (0, 1)) = F a)
    (a : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) : F a = F 0 := by
  have e₁ (x y : ULift.{u + 1} (ZMod m)) : F (x, y) = F (0, y) :=
    apply_eq_apply_zero_of_forall_sub_one (F := fun x ↦ F (x, y)) (fun x ↦ by
      simpa using h₁ (x, y)) x
  have e₂ (y : ULift.{u + 1} (ZMod m)) : F (0, y) = F (0, 0) :=
    apply_eq_apply_zero_of_forall_sub_one (F := fun y ↦ F (0, y)) (fun y ↦ by
      simpa using h₂ (0, y)) y
  obtain ⟨x, y⟩ := a
  exact (e₁ x y).trans (e₂ y)

omit [NeZero m] in
/-- The character `zmodChar c` increases by `c` from `-x` to `-(x - 1)`. -/
lemma zmodChar_neg_sub_one (c : A) (hc : m • c = 0) (x : ZMod m) :
    zmodChar c hc (-(x - 1)) - zmodChar c hc (-x) = c := by
  rw [← map_sub]
  convert zmodChar_one c hc using 2
  ring
end Algebra

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m]
  (T : EtaleTorsor (ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) Y)

/-! ### The sequence `0 ⟶ N ⟶ V ⟶ N ⊞ N ⟶ 0` -/

/-- `τ_b - 𝟙` on `π_* 𝔾ₘ`. -/
noncomputable def pairDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pushforwardGm ⟶ T.pushforwardGm :=
  T.pushforwardGmTranslate b - 𝟙 _

/-- The sheaf `π_* μ_m`. -/
noncomputable abbrev pairMu : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (m • 𝟙 T.pushforwardGm)

/-- `τ_b - 𝟙` on `π_* μ_m`. -/
noncomputable def pairMuDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pairMu ⟶ T.pairMu :=
  kernel.lift _ (kernel.ι _ ≫ T.pairDiff b) (by
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma pairMuDiff_ι (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pairMuDiff b ≫ kernel.ι _ = kernel.ι _ ≫ T.pairDiff b :=
  kernel.lift_ι _ _ _

/-- `(D₁, D₂) : π_* μ_m ⟶ π_* μ_m ⊞ π_* μ_m`. -/
noncomputable def pairPhi : T.pairMu ⟶ T.pairMu ⊞ T.pairMu :=
  biprod.lift (T.pairMuDiff (1, 0)) (T.pairMuDiff (0, 1))

/-- The invariants `N = ker (D₁, D₂)`. -/
noncomputable abbrev pairN : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel T.pairPhi

/-- The sections `v` with `D₁ v, D₂ v ∈ N`. -/
noncomputable abbrev pairV : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi)

lemma ιV_pairMuDiff_pairPhi (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) :
    kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ T.pairMuDiff b ≫ T.pairPhi = 0 := by
  rcases hb with rfl | rfl
  · calc _ = kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫
          (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ biprod.fst := by
          rw [Category.assoc, biprod.map_fst, pairPhi, biprod.lift_fst_assoc]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  · calc _ = kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫
          (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) ≫ biprod.snd := by
          rw [Category.assoc, biprod.map_snd, pairPhi, biprod.lift_snd_assoc]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

lemma ιN_pairMuDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) : kernel.ι T.pairPhi ≫ T.pairMuDiff b = 0 := by
  rcases hb with rfl | rfl
  · calc _ = kernel.ι T.pairPhi ≫ T.pairPhi ≫ biprod.fst := by rw [pairPhi, biprod.lift_fst]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  · calc _ = kernel.ι T.pairPhi ≫ T.pairPhi ≫ biprod.snd := by rw [pairPhi, biprod.lift_snd]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]

/-- The map `V ⟶ N`, `v ↦ D_b v`. -/
noncomputable def pairQ (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) : T.pairV ⟶ T.pairN :=
  kernel.lift _ (kernel.ι _ ≫ T.pairMuDiff b) (by
    rw [Category.assoc, T.ιV_pairMuDiff_pairPhi b hb])

@[reassoc (attr := simp)]
lemma pairQ_ι (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) :
    T.pairQ b hb ≫ kernel.ι _ = kernel.ι _ ≫ T.pairMuDiff b :=
  kernel.lift_ι _ _ _

/-- The inclusion `N ⟶ V`. -/
noncomputable def pairI : T.pairN ⟶ T.pairV :=
  kernel.lift _ (kernel.ι _) (by rw [← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma pairI_ι : T.pairI ≫ kernel.ι _ = kernel.ι T.pairPhi :=
  kernel.lift_ι _ _ _

/-- The short complex `N ⟶ V ⟶ N ⊞ N`. -/
noncomputable def pairSeq : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk T.pairI (biprod.lift (T.pairQ (1, 0) (.inl rfl)) (T.pairQ (0, 1) (.inr rfl)))
    (by
      apply biprod.hom_ext
      · rw [← cancel_mono (kernel.ι T.pairPhi)]
        simp only [Category.assoc, biprod.lift_fst_assoc, pairQ_ι, pairI_ι_assoc, zero_comp]
        exact T.ιN_pairMuDiff _ (.inl rfl)
      · rw [← cancel_mono (kernel.ι T.pairPhi)]
        simp only [Category.assoc, biprod.lift_snd_assoc, pairQ_ι, pairI_ι_assoc, zero_comp]
        exact T.ιN_pairMuDiff _ (.inr rfl))

lemma pairSeq_g_comp :
    T.pairSeq.g ≫ biprod.map (kernel.ι T.pairPhi) (kernel.ι T.pairPhi) =
      kernel.ι _ ≫ T.pairPhi := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, pairPhi, biprod.lift_fst, pairSeq]
    exact (biprod.lift_fst_assoc _ _ _).trans (T.pairQ_ι (1, 0) (.inl rfl))
  · simp only [Category.assoc, biprod.map_snd, pairPhi, biprod.lift_snd, pairSeq]
    exact (biprod.lift_snd_assoc _ _ _).trans (T.pairQ_ι (0, 1) (.inr rfl))

instance : Mono T.pairSeq.f :=
  mono_of_mono_fac (T.pairI_ι)

lemma pairSeq_exact : T.pairSeq.Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun w hw ↦ kernel.lift T.pairPhi (w ≫ kernel.ι _) (by
      rw [Category.assoc, ← T.pairSeq_g_comp, ← Category.assoc, hw, zero_comp]))
    (fun w hw ↦ ?_) (fun w hw g hg ↦ ?_))
  · rw [← cancel_mono (kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi))]
    simp [pairSeq]
  · rw [← cancel_mono (kernel.ι T.pairPhi)]
    simp only [kernel.lift_ι, ← hg]
    simp [pairSeq]

/-! ### Local computations -/

lemma pairDiff_app (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (U : Y.Etaleᵒᵖ)
    (x : T.pushforwardGm.obj.obj U) :
    (T.pairDiff b).hom.app U x = (T.pushforwardGmTranslate b).hom.app U x - x :=
  map_sub (homAppAddHom U x) _ _

/-- Sections of a biproduct of abelian sheaves are determined by their components. -/
lemma biprod_app_ext {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {U : X.Etaleᵒᵖ} (x y : (F ⊞ G).obj.obj U)
    (h₁ : (biprod.fst : F ⊞ G ⟶ F).hom.app U x = (biprod.fst : F ⊞ G ⟶ F).hom.app U y)
    (h₂ : (biprod.snd : F ⊞ G ⟶ G).hom.app U x = (biprod.snd : F ⊞ G ⟶ G).hom.app U y) :
    x = y := by
  have e (z : (F ⊞ G).obj.obj U) : z = (biprod.inl : F ⟶ F ⊞ G).hom.app U
      ((biprod.fst : F ⊞ G ⟶ F).hom.app U z) +
        (biprod.inr : G ⟶ F ⊞ G).hom.app U ((biprod.snd : F ⊞ G ⟶ G).hom.app U z) := by
    have := congrArg (fun φ : F ⊞ G ⟶ F ⊞ G ↦ homAppAddHom U z φ) (biprod.total (X := F) (Y := G))
    exact (this.symm.trans (map_add (homAppAddHom U z) _ _))
  rw [e x, e y, h₁, h₂]

section LocalTrivialization

variable {U : Y.Etale} (σ : U.left ⟶ T.P) (hσ : σ ≫ T.π = U.hom)

lemma localUnits_pairDiff (a b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (x : T.pushforwardGm.obj.obj (op U)) :
    T.localUnits σ hσ a ((T.pairDiff b).hom.app (op U) x) =
      T.localUnits σ hσ (a - b) x - T.localUnits σ hσ a x := by
  rw [pairDiff_app, map_sub, localUnits_translate]

include σ hσ in
/-- Over an étale `U` with a section of the torsor, an invariant section of `π_* 𝔾ₘ` comes from
the base. -/
lemma exists_of_pairDiff_eq_zero (x : T.pushforwardGm.obj.obj (op U)) (hx : m • x = 0)
    (h₁ : (T.pairDiff (1, 0)).hom.app (op U) x = 0)
    (h₂ : (T.pairDiff (0, 1)).hom.app (op U) x = 0) :
    ∃ c : Y.gmSheaf.obj.obj (op U), m • c = 0 ∧ T.pushforwardGmUnit.hom.app (op U) c = x := by
  set F := fun a ↦ T.localUnits σ hσ a x
  have hF (a) : F a = F 0 := by
    refine apply_eq_apply_zero_of_forall_sub_pair (fun a ↦ ?_) (fun a ↦ ?_) a
    · have := T.localUnits_pairDiff σ hσ a (1, 0) x
      rw [h₁, map_zero] at this
      exact sub_eq_zero.1 this.symm
    · have := T.localUnits_pairDiff σ hσ a (0, 1) x
      rw [h₂, map_zero] at this
      exact sub_eq_zero.1 this.symm
  refine ⟨ULift.up (F 0), ULift.ext ?_, T.localUnits_injective σ hσ fun a ↦ ?_⟩
  · change m • T.localUnits σ hσ 0 x = 0
    rw [← map_nsmul, hx, map_zero]
  · rw [localUnits_unit]
    exact (hF a).symm

include σ hσ in
/-- Over an étale `U` with a section of the torsor, every pair of `m`-torsion units of the base is
`(D₁ y, D₂ y)` for an `m`-torsion section `y` of `π_* 𝔾ₘ`. -/
lemma exists_pairDiff_eq (c₁ c₂ : Y.gmSheaf.obj.obj (op U)) (hc₁ : m • c₁.down = 0)
    (hc₂ : m • c₂.down = 0) :
    ∃ y : T.pushforwardGm.obj.obj (op U), m • y = 0 ∧
      (T.pairDiff (1, 0)).hom.app (op U) y = T.pushforwardGmUnit.hom.app (op U) c₁ ∧
      (T.pairDiff (0, 1)).hom.app (op U) y = T.pushforwardGmUnit.hom.app (op U) c₂ := by
  obtain ⟨y, hy⟩ := T.exists_localUnits σ hσ
    (fun a ↦ zmodChar c₁.down hc₁ (-a.1.down) + zmodChar c₂.down hc₂ (-a.2.down))
  refine ⟨y, T.localUnits_injective σ hσ fun a ↦ ?_, T.localUnits_injective σ hσ fun a ↦ ?_,
    T.localUnits_injective σ hσ fun a ↦ ?_⟩
  · rw [map_nsmul, hy, map_zero, smul_add]
    exact (congrArg₂ (· + ·) (nsmul_zmodChar _ _ _) (nsmul_zmodChar _ _ _)).trans (add_zero 0)
  · rw [localUnits_pairDiff, hy, hy, localUnits_unit]
    have h1 : (a - (1, 0)).1.down = a.1.down - 1 := rfl
    have h2 : (a - (1, 0)).2 = a.2 := by simp
    rw [h1, h2, add_sub_add_right_eq_sub]
    exact zmodChar_neg_sub_one _ _ _
  · rw [localUnits_pairDiff, hy, hy, localUnits_unit]
    have h1 : (a - (0, 1)).2.down = a.2.down - 1 := rfl
    have h2 : (a - (0, 1)).1 = a.1 := by simp
    rw [h1, h2, add_sub_add_left_eq_sub]
    exact zmodChar_neg_sub_one _ _ _
end LocalTrivialization

/-! ### Exactness and the identification `N ≅ μ_m` -/

lemma ιN_ι_pairDiff_app (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) (U : Y.Etaleᵒᵖ) (n : T.pairN.obj.obj U) :
    (T.pairDiff b).hom.app U ((kernel.ι (m • 𝟙 T.pushforwardGm)).hom.app U
      ((kernel.ι T.pairPhi).hom.app U n)) = 0 := by
  have h : kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm) ≫ T.pairDiff b = 0 := by
    rw [← pairMuDiff_ι, ← Category.assoc, T.ιN_pairMuDiff b hb, zero_comp]
  change (kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm) ≫ T.pairDiff b).hom.app U n = 0
  rw [h]
  rfl

lemma epi_pairSeq_g : Epi T.pairSeq.g := by
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology T.pairSeq.g.hom := ⟨fun {U} s ↦ by
    apply T.mem_smallEtaleTopology_of_coverArrow
    set U' := T.coverObj U
    set s' := (T.pairN ⊞ T.pairN).obj.map (T.coverArrow U).op s
    set n₁ := (biprod.fst : T.pairN ⊞ T.pairN ⟶ _).hom.app (op U') s'
    set n₂ := (biprod.snd : T.pairN ⊞ T.pairN ⟶ _).hom.app (op U') s'
    set w₁ := (kernel.ι (m • 𝟙 T.pushforwardGm)).hom.app (op U')
      ((kernel.ι T.pairPhi).hom.app (op U') n₁)
    set w₂ := (kernel.ι (m • 𝟙 T.pushforwardGm)).hom.app (op U')
      ((kernel.ι T.pairPhi).hom.app (op U') n₂)
    have hw₁ : m • w₁ = 0 := by
      rw [← nsmul_id_app]
      exact kernel_ι_app_apply_eq_zero _ _ _
    have hw₂ : m • w₂ = 0 := by
      rw [← nsmul_id_app]
      exact kernel_ι_app_apply_eq_zero _ _ _
    have hσ := T.coverObj_section U
    obtain ⟨c₁, hc₁, hcw₁⟩ := T.exists_of_pairDiff_eq_zero (pullback.snd U.hom T.π) hσ w₁ hw₁
      (T.ιN_ι_pairDiff_app _ (.inl rfl) _ _) (T.ιN_ι_pairDiff_app _ (.inr rfl) _ _)
    obtain ⟨c₂, hc₂, hcw₂⟩ := T.exists_of_pairDiff_eq_zero (pullback.snd U.hom T.π) hσ w₂ hw₂
      (T.ιN_ι_pairDiff_app _ (.inl rfl) _ _) (T.ιN_ι_pairDiff_app _ (.inr rfl) _ _)
    obtain ⟨y, hy, hy₁, hy₂⟩ := T.exists_pairDiff_eq (pullback.snd U.hom T.π) hσ c₁ c₂
      (congrArg ULift.down hc₁) (congrArg ULift.down hc₂)
    obtain ⟨v, hv⟩ := exists_kernel_ι_app_eq (m • 𝟙 T.pushforwardGm) y
      (by rw [nsmul_id_app, hy])
    have hDv₁ : (T.pairMuDiff (1, 0)).hom.app (op U') v = (kernel.ι T.pairPhi).hom.app _ n₁ := by
      apply injective_kernel_ι_app
      rw [← app_apply_comp, pairMuDiff_ι, app_apply_comp, hv, hy₁, hcw₁]
    have hDv₂ : (T.pairMuDiff (0, 1)).hom.app (op U') v = (kernel.ι T.pairPhi).hom.app _ n₂ := by
      apply injective_kernel_ι_app
      rw [← app_apply_comp, pairMuDiff_ι, app_apply_comp, hv, hy₂, hcw₂]
    obtain ⟨k, hk⟩ := exists_kernel_ι_app_eq (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi) v (by
      apply biprod_app_ext
      · rw [map_zero, ← app_apply_comp, Category.assoc, biprod.map_fst, ← Category.assoc,
          show T.pairPhi ≫ biprod.fst = T.pairMuDiff (1, 0) from biprod.lift_fst _ _,
          app_apply_comp, hDv₁]
        exact kernel_ι_app_apply_eq_zero _ _ _
      · rw [map_zero, ← app_apply_comp, Category.assoc, biprod.map_snd, ← Category.assoc,
          show T.pairPhi ≫ biprod.snd = T.pairMuDiff (0, 1) from biprod.lift_snd _ _,
          app_apply_comp, hDv₂]
        exact kernel_ι_app_apply_eq_zero _ _ _)
    refine ⟨k, biprod_app_ext _ _ ?_ ?_⟩
    · apply injective_kernel_ι_app
      change ((T.pairSeq.g ≫ biprod.fst) ≫ kernel.ι T.pairPhi).hom.app _ k = _
      rw [show T.pairSeq.g ≫ biprod.fst = T.pairQ (1, 0) (.inl rfl) from biprod.lift_fst _ _,
        pairQ_ι, app_apply_comp]
      exact (congrArg _ hk).trans hDv₁
    · apply injective_kernel_ι_app
      change ((T.pairSeq.g ≫ biprod.snd) ≫ kernel.ι T.pairPhi).hom.app _ k = _
      rw [show T.pairSeq.g ≫ biprod.snd = T.pairQ (0, 1) (.inr rfl) from biprod.lift_snd _ _,
        pairQ_ι, app_apply_comp]
      exact (congrArg _ hk).trans hDv₂⟩
  exact Sheaf.epi_of_isLocallySurjective T.pairSeq.g

lemma pairSeq_shortExact : T.pairSeq.ShortExact :=
  haveI := T.epi_pairSeq_g
  { exact := T.pairSeq_exact }

/-- The map `μ_m ⟶ π_* μ_m` pulling back roots of unity from the base. -/
noncomputable def pairUnitMu : Y.rootsOfUnitySheaf m ⟶ T.pairMu :=
  kernel.map _ _ T.pushforwardGmUnit T.pushforwardGmUnit (by
    rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma pairUnitMu_ι : T.pairUnitMu ≫ kernel.ι _ = kernel.ι _ ≫ T.pushforwardGmUnit :=
  kernel.lift_ι _ _ _

lemma pairUnitMu_pairMuDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) :
    T.pairUnitMu ≫ T.pairMuDiff b = 0 := by
  rw [← cancel_mono (kernel.ι (m • 𝟙 T.pushforwardGm)), Category.assoc, pairMuDiff_ι,
    pairUnitMu_ι_assoc, pairDiff, Preadditive.comp_sub, pushforwardGmUnit_comp_translate,
    Category.comp_id, sub_self, comp_zero, zero_comp]

/-- The map `μ_m ⟶ N`: roots of unity pulled back from the base are invariant. -/
noncomputable def pairUnit : Y.rootsOfUnitySheaf m ⟶ T.pairN :=
  kernel.lift _ T.pairUnitMu (by
    apply biprod.hom_ext <;> simp [pairPhi, pairUnitMu_pairMuDiff])

@[reassoc (attr := simp)]
lemma pairUnit_ι : T.pairUnit ≫ kernel.ι _ = T.pairUnitMu :=
  kernel.lift_ι _ _ _

lemma isIso_pairUnit : IsIso T.pairUnit := by
  have hι : T.pairUnit ≫ kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm) =
      kernel.ι (m • 𝟙 Y.gmSheaf) ≫ T.pushforwardGmUnit := by
    simp
  have : Mono T.pushforwardGmUnit := by
    have : Presheaf.IsLocallyInjective Y.smallEtaleTopology T.pushforwardGmUnit.hom :=
      ⟨fun {U} x y hxy ↦ by
        apply T.mem_smallEtaleTopology_of_coverArrow
        change Y.gmSheaf.obj.map (T.coverArrow U.unop).op x =
          Y.gmSheaf.obj.map (T.coverArrow U.unop).op y
        have h := congrArg (T.pushforwardGm.obj.map (T.coverArrow U.unop).op) hxy
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at h
        have h' := congrArg (T.localUnits (pullback.snd U.unop.hom T.π)
          (T.coverObj_section U.unop) 0) h
        rw [localUnits_unit, localUnits_unit] at h'
        exact ULift.ext h'⟩
    exact Sheaf.mono_of_isLocallyInjective _
  have : Mono T.pairUnit := by
    have : Mono (T.pairUnit ≫ kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm)) := by
      rw [hι]
      infer_instance
    exact mono_of_mono T.pairUnit (kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm))
  have : Epi T.pairUnit := by
    have : Presheaf.IsLocallySurjective Y.smallEtaleTopology T.pairUnit.hom := ⟨fun {U} s ↦ by
      apply T.mem_smallEtaleTopology_of_coverArrow
      set U' := T.coverObj U
      set s' := T.pairN.obj.map (T.coverArrow U).op s
      set w := (kernel.ι (m • 𝟙 T.pushforwardGm)).hom.app (op U')
        ((kernel.ι T.pairPhi).hom.app (op U') s')
      have hw : m • w = 0 := by
        rw [← nsmul_id_app]
        exact kernel_ι_app_apply_eq_zero _ _ _
      obtain ⟨c, hc, hcw⟩ := T.exists_of_pairDiff_eq_zero (pullback.snd U.hom T.π)
        (T.coverObj_section U) w hw (T.ιN_ι_pairDiff_app _ (.inl rfl) _ _)
        (T.ιN_ι_pairDiff_app _ (.inr rfl) _ _)
      obtain ⟨r, hr⟩ := exists_kernel_ι_app_eq (m • 𝟙 Y.gmSheaf) c (by rw [nsmul_id_app, hc])
      refine ⟨r, injective_kernel_ι_app _ _ (injective_kernel_ι_app _ _ ?_)⟩
      change (T.pairUnit ≫ kernel.ι T.pairPhi ≫ kernel.ι (m • 𝟙 T.pushforwardGm)).hom.app _ r = w
      rw [hι, app_apply_comp]
      exact (congrArg _ hr).trans hcw⟩
    exact Sheaf.epi_of_isLocallySurjective T.pairUnit
  exact isIso_of_mono_of_epi _

/-! ### Mapping the extension of a `ℤ/m`-torsor to the pair sequence -/

lemma comp_pairPhi_eq_zero {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : Z ⟶ T.pairMu) (h₁ : f ≫ T.pairMuDiff (1, 0) = 0) (h₂ : f ≫ T.pairMuDiff (0, 1) = 0) :
    f ≫ T.pairPhi = 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, pairPhi, biprod.lift_fst, h₁, zero_comp]
  · rw [Category.assoc, pairPhi, biprod.lift_snd, h₂, zero_comp]

variable {T} (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y) (h : T.P ⟶ t.P) (hπ : h ≫ t.π = T.π)

/-- Pullback of units along `h : Q ⟶ P`. -/
noncomputable abbrev pairW : t.pushforwardGm ⟶ T.pushforwardGm :=
  lowerStarGmSheafMap t.π h T.π hπ

lemma pairW_pairDiff (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (c : ℕ)
    (hv : T.vadd b ≫ h = h ≫ t.vadd (c • 1)) :
    pairW t h hπ ≫ T.pairDiff b = (t.transl c - 𝟙 _) ≫ pairW t h hπ := by
  have e : pairW t h hπ ≫ T.pushforwardGmTranslate b = t.transl c ≫ pairW t h hπ := by
    rw [pairW, pushforwardGmTranslate, transl, pushforwardGmTranslate, lowerStarGmSheafMap_comp,
      lowerStarGmSheafMap_comp]
    congr 1
  rw [pairDiff, Preadditive.comp_sub, e, Preadditive.sub_comp, Category.comp_id,
    Category.id_comp]

/-- Pullback of units along `h` on `π_* μ_m`. -/
noncomputable def pairV' : t.pushforwardMu ⟶ T.pairMu :=
  kernel.lift _ (kernel.ι _ ≫ pairW t h hπ) (by
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, Preadditive.comp_nsmul,
      Category.comp_id, t.nsmul_kernel_ι_pushforwardMu, zero_comp])

@[reassoc (attr := simp)]
lemma pairV'_ι : pairV' t h hπ ≫ kernel.ι _ = kernel.ι _ ≫ pairW t h hπ :=
  kernel.lift_ι _ _ _

lemma comp_pairV'_pairMuDiff {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (X : Z ⟶ t.pushforwardMu) (hX : X ≫ t.muDiff ≫ t.muDiff = 0)
    (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (c : ℕ)
    (hv : T.vadd b ≫ h = h ≫ t.vadd (c • 1)) :
    X ≫ pairV' t h hπ ≫ T.pairMuDiff b = c • (X ≫ t.muDiff ≫ pairV' t h hπ) := by
  rw [← cancel_mono (kernel.ι (m • 𝟙 T.pushforwardGm))]
  have hX' : (X ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ t.gmDiff ≫ t.gmDiff = 0 := by
    have : X ≫ t.muDiff ≫ t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm) = 0 := by
      rw [reassoc_of% hX, zero_comp]
    simpa only [Category.assoc, muDiff_ι, muDiff_ι_assoc] using this
  have key := t.comp_transl_sub _ hX' c
  calc (X ≫ pairV' t h hπ ≫ T.pairMuDiff b) ≫ kernel.ι (m • 𝟙 T.pushforwardGm) =
      (X ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ pairW t h hπ ≫ T.pairDiff b := by
        simp only [Category.assoc, pairMuDiff_ι, pairV'_ι_assoc]
    _ = ((X ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) ≫ (t.transl c - 𝟙 _)) ≫ pairW t h hπ := by
        rw [pairW_pairDiff t h hπ b c hv]
        simp only [Category.assoc]
    _ = (c • (X ≫ t.muDiff ≫ pairV' t h hπ)) ≫ kernel.ι (m • 𝟙 T.pushforwardGm) := by
        rw [key]
        simp only [Preadditive.nsmul_comp, Category.assoc, pairV'_ι, muDiff_ι_assoc]

lemma comp_pairV'_pairMuDiff_eq_zero (c₁ c₂ : ℕ)
    (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1))
    {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (X : Z ⟶ t.pushforwardMu) (hX : X ≫ t.muDiff = 0)
    (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (hb : b = (1, 0) ∨ b = (0, 1)) :
    X ≫ pairV' t h hπ ≫ T.pairMuDiff b = 0 := by
  have hX₂ : X ≫ t.muDiff ≫ t.muDiff = 0 := by rw [← Category.assoc, hX, zero_comp]
  rcases hb with rfl | rfl
  · rw [comp_pairV'_pairMuDiff t h hπ X hX₂ _ c₁ hv₁, ← Category.assoc, hX, zero_comp,
      smul_zero]
  · rw [comp_pairV'_pairMuDiff t h hπ X hX₂ _ c₂ hv₂, ← Category.assoc, hX, zero_comp,
      smul_zero]

/-- The map `K₁ ⟶ N`. -/
noncomputable def pairK₁ (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1)) : kernel t.muDiff ⟶ T.pairN :=
  kernel.lift _ (kernel.ι _ ≫ pairV' t h hπ) (by
    refine T.comp_pairPhi_eq_zero _ ?_ ?_ <;> rw [Category.assoc]
    · exact comp_pairV'_pairMuDiff_eq_zero t h hπ c₁ c₂ hv₁ hv₂ _ (kernel.condition _) _
        (Or.inl rfl)
    · exact comp_pairV'_pairMuDiff_eq_zero t h hπ c₁ c₂ hv₁ hv₂ _ (kernel.condition _) _
        (Or.inr rfl))

@[reassoc (attr := simp)]
lemma pairK₁_ι (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1)) :
    pairK₁ t h hπ c₁ c₂ hv₁ hv₂ ≫ kernel.ι _ = kernel.ι _ ≫ pairV' t h hπ :=
  kernel.lift_ι _ _ _

lemma comp_pairV'_pairMuDiff_pairPhi (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1))
    {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (X : Z ⟶ t.pushforwardMu) (hX : X ≫ t.muDiff ≫ t.muDiff = 0)
    (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) (c : ℕ)
    (hv : T.vadd b ≫ h = h ≫ t.vadd (c • 1)) :
    X ≫ pairV' t h hπ ≫ T.pairMuDiff b ≫ T.pairPhi = 0 := by
  have hX' : (X ≫ t.muDiff) ≫ t.muDiff = 0 := by rw [Category.assoc, hX]
  have e₁ := comp_pairV'_pairMuDiff_eq_zero t h hπ c₁ c₂ hv₁ hv₂ _ hX' _ (Or.inl rfl)
  have e₂ := comp_pairV'_pairMuDiff_eq_zero t h hπ c₁ c₂ hv₁ hv₂ _ hX' _ (Or.inr rfl)
  have e₃ : ((X ≫ t.muDiff) ≫ pairV' t h hπ) ≫ T.pairPhi = 0 :=
    T.comp_pairPhi_eq_zero _ (by rw [Category.assoc, e₁]) (by rw [Category.assoc, e₂])
  calc X ≫ pairV' t h hπ ≫ T.pairMuDiff b ≫ T.pairPhi =
      (X ≫ pairV' t h hπ ≫ T.pairMuDiff b) ≫ T.pairPhi := by simp only [Category.assoc]
    _ = c • (((X ≫ t.muDiff) ≫ pairV' t h hπ) ≫ T.pairPhi) := by
        rw [comp_pairV'_pairMuDiff t h hπ X hX b c hv, Preadditive.nsmul_comp]
        simp only [Category.assoc]
    _ = 0 := by rw [e₃, smul_zero]

lemma comp_pairV'_pairPhi_map (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1))
    {Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (X : Z ⟶ t.pushforwardMu) (hX : X ≫ t.muDiff ≫ t.muDiff = 0) :
    (X ≫ pairV' t h hπ) ≫ T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi = 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, biprod.map_fst, ← Category.assoc T.pairPhi,
      show T.pairPhi ≫ biprod.fst = T.pairMuDiff (1, 0) from biprod.lift_fst _ _, zero_comp]
    exact comp_pairV'_pairMuDiff_pairPhi t h hπ c₁ c₂ hv₁ hv₂ X hX _ c₁ hv₁
  · rw [Category.assoc, Category.assoc, Category.assoc, biprod.map_snd, ← Category.assoc T.pairPhi,
      show T.pairPhi ≫ biprod.snd = T.pairMuDiff (0, 1) from biprod.lift_snd _ _, zero_comp]
    exact comp_pairV'_pairMuDiff_pairPhi t h hπ c₁ c₂ hv₁ hv₂ X hX _ c₂ hv₂

/-- The map `K₂ ⟶ V`. -/
noncomputable def pairK₂ (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1)) :
    kernel (t.muDiff ≫ t.muDiff) ⟶ T.pairV :=
  kernel.lift _ (kernel.ι _ ≫ pairV' t h hπ)
    (comp_pairV'_pairPhi_map t h hπ c₁ c₂ hv₁ hv₂ _ (kernel.condition _))

@[reassoc (attr := simp)]
lemma pairK₂_ι (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
    (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1)) :
    pairK₂ t h hπ c₁ c₂ hv₁ hv₂ ≫ kernel.ι _ = kernel.ι _ ≫ pairV' t h hπ :=
  kernel.lift_ι _ _ _

variable (c₁ c₂ : ℕ) (hv₁ : T.vadd (1, 0) ≫ h = h ≫ t.vadd (c₁ • 1))
  (hv₂ : T.vadd (0, 1) ≫ h = h ≫ t.vadd (c₂ • 1))

lemma pairK₁_pairI : pairK₁ t h hπ c₁ c₂ hv₁ hv₂ ≫ T.pairI =
    kernelToKernelComp t.muDiff ≫ pairK₂ t h hπ c₁ c₂ hv₁ hv₂ := by
  rw [← cancel_mono (kernel.ι (T.pairPhi ≫ biprod.map T.pairPhi T.pairPhi)), Category.assoc,
    pairI_ι, pairK₁_ι, Category.assoc, pairK₂_ι, kernelToKernelComp_ι_assoc]

lemma pairK₂_pairQ (b : ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m))
    (hb : b = (1, 0) ∨ b = (0, 1)) (c : ℕ) (hv : T.vadd b ≫ h = h ≫ t.vadd (c • 1)) :
    pairK₂ t h hπ c₁ c₂ hv₁ hv₂ ≫ T.pairQ b hb =
      kernelCompToKernel t.muDiff ≫ (c • pairK₁ t h hπ c₁ c₂ hv₁ hv₂) := by
  rw [← cancel_mono (kernel.ι T.pairPhi), Category.assoc, pairQ_ι, pairK₂_ι_assoc,
    comp_pairV'_pairMuDiff t h hπ _ (kernel.condition _) b c hv]
  simp only [Category.assoc, Preadditive.comp_nsmul, Preadditive.nsmul_comp, pairK₁_ι,
    kernelCompToKernel_ι_assoc]

/-- Pulling back along `h` is a morphism from the extension of `t` to the pair sequence, by
`(c₁, c₂)` on the quotient. -/
noncomputable def pairExtSeqMap : t.extSeq ⟶ T.pairSeq where
  τ₁ := pairK₁ t h hπ c₁ c₂ hv₁ hv₂
  τ₂ := pairK₂ t h hπ c₁ c₂ hv₁ hv₂
  τ₃ := biprod.lift (c₁ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂) (c₂ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂)
  comm₁₂ := pairK₁_pairI t h hπ c₁ c₂ hv₁ hv₂
  comm₂₃ := by
    apply biprod.hom_ext
    · change (pairK₂ t h hπ c₁ c₂ hv₁ hv₂ ≫ biprod.lift _ _) ≫ biprod.fst =
        (kernelCompToKernel t.muDiff ≫ biprod.lift _ _) ≫ biprod.fst
      rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.lift_fst,
        pairK₂_pairQ t h hπ c₁ c₂ hv₁ hv₂ _ _ c₁ hv₁]
    · change (pairK₂ t h hπ c₁ c₂ hv₁ hv₂ ≫ biprod.lift _ _) ≫ biprod.snd =
        (kernelCompToKernel t.muDiff ≫ biprod.lift _ _) ≫ biprod.snd
      rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.lift_snd,
        pairK₂_pairQ t h hπ c₁ c₂ hv₁ hv₂ _ _ c₂ hv₂]

lemma muUnit_pairK₁ : t.muUnit ≫ pairK₁ t h hπ c₁ c₂ hv₁ hv₂ = T.pairUnit := by
  rw [← cancel_mono (kernel.ι T.pairPhi), ← cancel_mono (kernel.ι (m • 𝟙 T.pushforwardGm))]
  simp [muUnit, muUnitV, pairW, pushforwardGmUnit]

include h hπ hv₁ hv₂ in
/-- The cup product with the class of `t`, read in the pair sequence. -/
lemma map_pairUnit_cupMu (x : Sheaf.H (Y.rootsOfUnitySheaf m) 1) :
    Sheaf.H.map T.pairUnit 2 (t.cupMu x) = Sheaf.H.δSucc T.pairSeq_shortExact 1
      (Sheaf.H.map (biprod.lift (c₁ • T.pairUnit) (c₂ • T.pairUnit)) 1 x) := by
  have := t.isIso_muUnit
  have e₁ : inv t.muUnit ≫ T.pairUnit = pairK₁ t h hπ c₁ c₂ hv₁ hv₂ := by
    rw [IsIso.inv_comp_eq, muUnit_pairK₁]
  have e₂ : t.muUnit ≫ biprod.lift (c₁ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂)
      (c₂ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂) = biprod.lift (c₁ • T.pairUnit) (c₂ • T.pairUnit) := by
    apply biprod.hom_ext <;>
      simp [muUnit_pairK₁ t h hπ c₁ c₂ hv₁ hv₂]
  simp only [cupMu, AddMonoidHom.comp_apply]
  rw [← Sheaf.H.map_comp_apply, e₁]
  refine (Sheaf.H.map_δSucc _ T.pairSeq_shortExact (pairExtSeqMap t h hπ c₁ c₂ hv₁ hv₂) 1
    _).trans ?_
  congr 1
  change Sheaf.H.map (biprod.lift (c₁ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂)
    (c₂ • pairK₁ t h hπ c₁ c₂ hv₁ hv₂)) 1 _ = _
  exact (Sheaf.H.map_comp_apply _ _ _).symm.trans (congrArg (fun φ ↦ Sheaf.H.map φ 1 x) e₂)

end AlgebraicGeometry.Scheme.EtaleTorsor
