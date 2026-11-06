/-
Parts of this file are adapted from
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists what was adapted and what was changed.
-/
import Langlands.AlgebraicGeometry.Modules.FormalModuleSystem
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.FinitePresentation
import Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Module presheaves of a formal module system

A formal module system `F` over the adic thickenings `X_n` of `X ⟶ Spec R` gives quasi-coherent
coherent `OModulePresheaf`s `U ↦ Γ(F_n, ι_n⁻¹ U)` on `X`, with transition maps that are
surjective on affine opens with kernel `I^(n+1)` times the sections.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.FormalModuleSystemPresheaves

section ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
  (N : Type u) [AddCommGroup N] [Module A N]

/-- The submodule `ker σ • N`. -/
abbrev kerSMul : Submodule A N := RingHom.ker σ • (⊤ : Submodule A N)

variable {σ} (hσ : Function.Surjective σ)

include hσ in
/-- Along a surjective ring map, every element of the scalar extension is of the form `1 ⊗ n`. -/
lemma exists_one_tmul (z : (ModuleCat.extendScalars σ).obj (ModuleCat.of A N)) :
    ∃ n : N, (1 : B) ⊗ₜ[A, σ] n = z := by
  let _ : Module A B := Module.compHom B σ
  refine TensorProduct.inductionOn (R := A) (M := B) (N := N)
    (motive := fun z : B ⊗[A] N => ∃ n : N, (1 : B) ⊗ₜ[A] n = z) z
    (fun b n => ?_) (fun z z' hz hz' => ?_)
  · obtain ⟨a, rfl⟩ := hσ b
    refine ⟨a • n, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    show σ a * (1 : B) = σ a
    rw [mul_one]
  · obtain ⟨n, rfl⟩ := hz
    obtain ⟨n', rfl⟩ := hz'
    exact ⟨n + n', TensorProduct.tmul_add _ _ _⟩

variable {N}

lemma mk_smul_eq_of_eq {a a' : A} (h : σ a = σ a') (n : N) :
    (Submodule.Quotient.mk (a • n) : N ⧸ kerSMul σ N) = Submodule.Quotient.mk (a' • n) := by
  rw [Submodule.Quotient.eq, ← sub_smul]
  exact Submodule.smul_mem_smul (by rw [RingHom.mem_ker, map_sub, h, sub_self])
    Submodule.mem_top

/-- The map `b ⊗ n ↦ [a • n]` for any `a` with `σ a = b`. -/
def descend : @TensorProduct A _ B N _ _ (Module.compHom B σ) _ →+ N ⧸ kerSMul σ N :=
  letI : Module A B := Module.compHom B σ
  TensorProduct.liftAddHom
    { toFun := fun b =>
        { toFun := fun n => Submodule.Quotient.mk (Function.surjInv hσ b • n)
          map_zero' := by rw [smul_zero, Submodule.Quotient.mk_zero]
          map_add' := fun n n' => by rw [smul_add, Submodule.Quotient.mk_add] }
      map_zero' := by
        ext n
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        rw [mk_smul_eq_of_eq (a' := 0) (by rw [Function.surjInv_eq hσ, map_zero]) n, zero_smul,
          Submodule.Quotient.mk_zero]
      map_add' := fun b b' => by
        ext n
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
        rw [← Submodule.Quotient.mk_add, ← add_smul]
        exact mk_smul_eq_of_eq (by rw [map_add, Function.surjInv_eq hσ, Function.surjInv_eq hσ,
          Function.surjInv_eq hσ]) n }
    (fun a b n => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [smul_smul]
      refine mk_smul_eq_of_eq ?_ n
      show σ (Function.surjInv hσ (σ a * b)) = σ (Function.surjInv hσ b * a)
      rw [map_mul, Function.surjInv_eq hσ, Function.surjInv_eq hσ, mul_comm])

lemma descend_one_tmul (n : N) :
    descend hσ ((1 : B) ⊗ₜ[A, σ] n) = Submodule.Quotient.mk n := by
  show Submodule.Quotient.mk (Function.surjInv hσ 1 • n) = Submodule.Quotient.mk n
  conv_rhs => rw [← one_smul A n]
  exact mk_smul_eq_of_eq (by rw [Function.surjInv_eq hσ, map_one]) n

include hσ in
/-- Along a surjective ring map, `1 ⊗ n` vanishes exactly when `n ∈ ker σ • N`. -/
lemma one_tmul_eq_zero_iff (n : N) :
    (1 : B) ⊗ₜ[A, σ] n = 0 ↔ n ∈ kerSMul σ N := by
  let _ : Module A B := Module.compHom B σ
  constructor
  · intro h
    have := congrArg (descend hσ) h
    rwa [descend_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
  · intro h
    refine Submodule.smul_induction_on h (fun a ha m _ => ?_) (fun x y hx hy => ?_)
    · rw [← TensorProduct.smul_tmul]
      have : a • (1 : B) = 0 := by
        show σ a * 1 = 0
        rw [RingHom.mem_ker.mp ha, zero_mul]
      rw [this, TensorProduct.zero_tmul]
    · rw [TensorProduct.tmul_add, hx, hy, add_zero]

include hσ in
/-- A map out of the scalar extension along a surjective ring map is bijective when its
restriction `n ↦ g (1 ⊗ n)` is surjective with kernel `ker σ • N`. -/
lemma bijective_of_one_tmul {T : Type u} [AddCommGroup T]
    (g : (ModuleCat.extendScalars σ).obj (ModuleCat.of A N) →+ T)
    (hs : Function.Surjective fun n : N => g ((1 : B) ⊗ₜ[A, σ] n))
    (hk : ∀ n : N, g ((1 : B) ⊗ₜ[A, σ] n) = 0 → n ∈ kerSMul σ N) :
    Function.Bijective g := by
  refine ⟨(injective_iff_map_eq_zero g).mpr fun z hz => ?_, fun t => ?_⟩
  · obtain ⟨n, rfl⟩ := exists_one_tmul N hσ z
    exact (one_tmul_eq_zero_iff hσ n).mpr (hk n hz)
  · obtain ⟨n, hn⟩ := hs t
    exact ⟨_, hn⟩

include hσ in
/-- Conversely, for a bijective map out of the scalar extension along a surjective ring map,
`n ↦ g (1 ⊗ n)` is surjective with kernel `ker σ • N`. -/
lemma surjective_and_ker_of_bijective {T : Type u} [AddCommGroup T]
    (g : (ModuleCat.extendScalars σ).obj (ModuleCat.of A N) →+ T) (hg : Function.Bijective g) :
    Function.Surjective (fun n : N => g ((1 : B) ⊗ₜ[A, σ] n)) ∧
      ∀ n : N, g ((1 : B) ⊗ₜ[A, σ] n) = 0 ↔ n ∈ kerSMul σ N := by
  refine ⟨fun t => ?_, fun n => ?_⟩
  · obtain ⟨z, rfl⟩ := hg.2 t
    obtain ⟨n, rfl⟩ := exists_one_tmul N hσ z
    exact ⟨n, rfl⟩
  · rw [← one_tmul_eq_zero_iff hσ n]
    exact ⟨fun h => hg.1 (h.trans (map_zero g).symm), fun h => by rw [h, map_zero]⟩

end ExtendScalars

section PushoutSurj

variable {A B C P : CommRingCat.{u}} {f : A ⟶ C} {q : A ⟶ B} {inl : C ⟶ P} {inr : B ⟶ P}

/-- In a pushout square of commutative rings, the base change of a surjection is surjective with
kernel generated by the image of the original kernel. -/
theorem surjective_and_ker_eq_of_isPushout (h : IsPushout f q inl inr)
    (hq : Function.Surjective q.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = Ideal.map f.hom (RingHom.ker q.hom) := by
  classical
  set J : Ideal C := Ideal.map f.hom (RingHom.ker q.hom) with hJ
  have hJle : J ≤ RingHom.ker inl.hom := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw, RingHom.mem_ker.mp ha, map_zero]
  let toQ : C ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hker : RingHom.ker q.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp f.hom) := by
    intro a ha
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let k₀ : B →+* C ⧸ J :=
    RingHom.liftOfSurjective q.hom hq ⟨(Ideal.Quotient.mk J).comp f.hom, hker⟩
  have hk₀ : ∀ a, k₀ (q.hom a) = Ideal.Quotient.mk J (f.hom a) := fun a =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  let k : B ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom k₀
  have w : f ≫ toQ = q ≫ k := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, k,
      CommRingCat.hom_ofHom]
    exact (hk₀ a).symm
  let d : P ⟶ CommRingCat.of (C ⧸ J) := h.desc toQ k w
  have hd : inl ≫ d = toQ := h.inl_desc toQ k w
  let u₀ : C ⧸ J →+* P := Ideal.Quotient.lift J inl.hom fun c hc => hJle hc
  have hu₀ : ∀ c, u₀ (Ideal.Quotient.mk J c) = inl.hom c := fun c => Ideal.Quotient.lift_mk J _ _
  let u : CommRingCat.of (C ⧸ J) ⟶ P := CommRingCat.ofHom u₀
  have hu : toQ ≫ u = inl := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, u,
      CommRingCat.hom_ofHom]
    exact hu₀ c
  have hdu : d ≫ u = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, hd, hu, Category.comp_id]
    · rw [Category.comp_id, ← Category.assoc, h.inr_desc toQ k w]
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨a, rfl⟩ := hq b
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, k, u,
        CommRingCat.hom_ofHom]
      rw [hk₀ a, hu₀]
      have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
      exact hw
  have hud : u ≫ d = 𝟙 _ := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply, u, CommRingCat.hom_ofHom]
    rw [hu₀]
    have := congrArg (fun φ : C ⟶ _ => φ.hom c) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ,
      CommRingCat.hom_ofHom] at this
    exact this
  have hu_surj : Function.Surjective u.hom := by
    intro p
    refine ⟨d.hom p, ?_⟩
    have := congrArg (fun φ : P ⟶ P => φ.hom p) hdu
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at this
    exact this
  have hu_inj : Function.Injective u.hom := by
    intro x y hxy
    have hx := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom x) hud
    have hy := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom y) hud
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hinl : ∀ c, inl.hom c = u.hom (Ideal.Quotient.mk J c) := fun c => (hu₀ c).symm
  refine ⟨?_, ?_⟩
  · intro p
    obtain ⟨x, hx⟩ := hu_surj p
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨c, (hinl c).trans hx⟩
  · ext c
    rw [RingHom.mem_ker, hinl, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hc
      exact hu_inj (hc.trans (map_zero u.hom).symm)
    · intro hc
      rw [hc, map_zero]

end PushoutSurj

section RingCat

variable {X Y Z : CommRingCat.{u}}

theorem surj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Surjective a.hom := fun y =>
  ⟨(inv a).hom y, by rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩

theorem inj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Injective a.hom := fun x x' h => by
  have := congrArg (inv a).hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id] at this

theorem ker_comp_of_injective (b : X ⟶ Y) (c : Y ⟶ Z) (hc : Function.Injective c.hom) :
    RingHom.ker (b ≫ c).hom = RingHom.ker b.hom := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  constructor
  · intro h
    exact hc (h.trans (map_zero c.hom).symm)
  · intro h
    rw [h, map_zero]

theorem ker_comp_eq_comap (a : X ⟶ Y) (b : Y ⟶ Z) :
    RingHom.ker (a ≫ b).hom = (RingHom.ker b.hom).comap a.hom := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

theorem surjective_comp_iff_of_isIso_right (b : X ⟶ Y) (c : Y ⟶ Z) [IsIso c] :
    Function.Surjective (b ≫ c).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (c.hom y)
    exact ⟨x, inj_hom_of_isIso c hx⟩
  · intro h
    exact (surj_hom_of_isIso c).comp h

theorem surjective_comp_iff_of_isIso_left (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso a] :
    Function.Surjective (a ≫ b).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h
    exact Function.Surjective.of_comp h
  · intro h
    exact h.comp (surj_hom_of_isIso a)

theorem comap_hom_eq_map_inv (e : X ≅ Y) (K : Ideal Y) :
    K.comap e.hom.hom = K.map e.inv.hom := by
  apply le_antisymm
  · intro x hx
    have hx' : x = e.inv.hom (e.hom.hom x) := by
      rw [← CommRingCat.comp_apply, e.hom_inv_id]; rfl
    rw [hx']
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, Ideal.mem_comap, ← CommRingCat.comp_apply, e.inv_hom_id]
    exact hz

theorem map_hom_comap_hom (e : X ≅ Y) (K : Ideal Y) : (K.comap e.hom.hom).map e.hom.hom = K :=
  Ideal.map_comap_of_surjective _ (surj_hom_of_isIso e.hom) K

theorem map_hom_map_inv (e : X ≅ Y) (K : Ideal Y) : (K.map e.inv.hom).map e.hom.hom = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

end RingCat

section Kernel

variable {R : Type u} [CommRing R] {V Z₀ Z₁ : Scheme.{u}} (π : V ⟶ Spec (.of R)) (j₁ : Z₁ ⟶ V)
  (y : Z₀ ⟶ Z₁)
  {A' A : Type u} [CommRing A'] [CommRing A] [Algebra R A'] (φ : A' →+* A)
  (hφ : Function.Surjective φ)
  (p₁ : Z₁ ⟶ Spec (.of A')) (p₀ : Z₀ ⟶ Spec (.of A))
  (H : IsPullback y p₀ p₁ (Spec.map (CommRingCat.ofHom φ)))
  (hp₁ : j₁ ≫ π = p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A')))

theorem appLE_congr_hom {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (U : Y.Opens)
    (W : X.Opens) (h : W ≤ k ⁻¹ᵁ U) (h' : W ≤ k' ⁻¹ᵁ U) : k.appLE U W h = k'.appLE U W h' := by
  subst e; rfl

include hp₁ in
theorem algebraMap_eq_of_fac (W : Z₁.Opens) (r : R) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (j₁ ≫ π) W).algebraMap r =
      (p₁.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of A')).inv.hom (algebraMap R A' r)) := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  rw [appLE_congr_hom hp₁ ⊤ W le_top le_top]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ ⊤ le_top ≫
      p₁.appLE ⊤ W le_top =
        (p₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ W le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← h1, CommRingCat.comp_apply]
  congr 1
  have h2 : CommRingCat.ofHom (algebraMap R A') ≫ (Scheme.ΓSpecIso (.of A')).inv =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have h3 : (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap R A'))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h3, ← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
  rfl

theorem appTop_SpecMap :
    (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (.of A')).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of A)).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem appLE_top_top {S T : Scheme.{u}} (t : T ⟶ S) : t.appLE ⊤ ⊤ le_top = t.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

include hφ H in
theorem surjective_and_ker_appLE_core (W₁ : Z₁.Opens) (hW₁ : IsAffineOpen W₁) :
    Function.Surjective (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)) ∧
      RingHom.ker (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)).hom =
        ((RingHom.ker φ).map (Scheme.ΓSpecIso (.of A')).inv.hom).map
          (p₁.appLE ⊤ W₁ le_top).hom := by
  set UY : Z₀.Opens := y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ with hUY
  have Hres := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := ⊤) (UX := W₁) le_top le_top
    (UY := UY) hUY
  have : IsAffine W₁ := hW₁
  have : IsAffine (⊤ : (Spec (CommRingCat.of A')).Opens) := isAffineOpen_top _
  have : IsAffine (⊤ : (Spec (CommRingCat.of A)).Opens) := isAffineOpen_top _
  have hpo := isPushout_appTop_of_isPullback Hres
  have hg' : Function.Surjective
      ((Spec.map (CommRingCat.ofHom φ)).resLE ⊤ ⊤ le_top).appTop.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_top_top, appTop_SpecMap,
      surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right,
      surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right]
    exact hφ
  obtain ⟨hsurj, hker⟩ := surjective_and_ker_eq_of_isPushout hpo hg'
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at hsurj hker
  rw [surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right] at hsurj
  refine ⟨hsurj, ?_⟩
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _)] at hker
  have hker' := congrArg (Ideal.map (W₁.topIso.hom.hom)) hker
  rw [map_hom_comap_hom] at hker'
  rw [hker']
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    appLE_top_top, appTop_SpecMap]
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _), ker_comp_eq_comap,
    ker_comp_of_injective _ _ (inj_hom_of_isIso _), CommRingCat.hom_ofHom]
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map]
  rw [map_hom_comap_hom, comap_hom_eq_map_inv, map_hom_map_inv]

theorem preimage_eq_inf' (W₁ : Z₁.Opens) : y ⁻¹ᵁ W₁ = y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ := by
  ext1
  simp

theorem app_eq_comp (W₁ : Z₁.Opens) :
    y.app W₁ = y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf' y p₀ W₁)).op := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map' y _ _).symm

include hφ H hp₁ in
/-- For a pullback square over a surjection `A' → A` of rings with kernel generated by `J`, the
map on sections over the inverse image of an affine open is surjective with kernel generated
by `J`. -/
theorem surjective_and_ker_app [IsAffineHom j₁] (J : Ideal R)
    (hJ : RingHom.ker φ = J.map (algebraMap R A')) (U : V.affineOpens) :
    Function.Surjective (y.app (j₁ ⁻¹ᵁ U.1)).hom ∧
      RingHom.ker (y.app (j₁ ⁻¹ᵁ U.1)).hom =
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (j₁ ≫ π) (j₁ ⁻¹ᵁ U.1)
        J.map (algebraMap R Γ(Z₁, j₁ ⁻¹ᵁ U.1)) := by
  have hW₁ : IsAffineOpen (j₁ ⁻¹ᵁ U.1) := U.2.preimage j₁
  obtain ⟨hs, hk⟩ := surjective_and_ker_appLE_core y φ hφ p₁ p₀ H (j₁ ⁻¹ᵁ U.1) hW₁
  rw [app_eq_comp y p₀ (j₁ ⁻¹ᵁ U.1)]
  refine ⟨?_, ?_⟩
  · exact (surjective_comp_iff_of_isIso_right _ _).mpr hs
  · let _ := Scheme.TwoAffineOpenCover.algebraOfHom (j₁ ≫ π) (j₁ ⁻¹ᵁ U.1)
    have halg : algebraMap R Γ(Z₁, j₁ ⁻¹ᵁ U.1) =
        ((p₁.appLE ⊤ (j₁ ⁻¹ᵁ U.1) le_top).hom.comp (Scheme.ΓSpecIso (.of A')).inv.hom).comp
          (algebraMap R A') :=
      RingHom.ext fun r => algebraMap_eq_of_fac π j₁ p₁ hp₁ (j₁ ⁻¹ᵁ U.1) r
    rw [ker_comp_of_injective _ _ (inj_hom_of_isIso _), hk, hJ, Ideal.map_map, Ideal.map_map,
      halg]

end Kernel

section Adic

open Picard.FormalLineBundle

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

instance isClosedImmersion_adicBaseProjection (n : ℕ) :
    IsClosedImmersion (adicBaseProjection I n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance isClosedImmersion_adicProjection (n : ℕ) :
    IsClosedImmersion (adicProjection f I n) := by
  unfold adicProjection
  infer_instance

lemma adicTransition_preimage (n : ℕ) (U : X.Opens) :
    adicTransition f I n ⁻¹ᵁ (adicProjection f I (n + 1) ⁻¹ᵁ U) =
      adicProjection f I n ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, adicTransition_projection]

lemma le_adicTransition_preimage (n : ℕ) (U : X.Opens) :
    adicProjection f I n ⁻¹ᵁ U ≤
      adicTransition f I n ⁻¹ᵁ (adicProjection f I (n + 1) ⁻¹ᵁ U) :=
  (adicTransition_preimage f I n U).ge

/-- The quotient map `R / I^(n+2) → R / I^(n+1)`. -/
abbrev qR (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + 1 + 1))

theorem ker_qR (n : ℕ) :
    RingHom.ker (qR I n) = (I ^ (n + 1)).map (algebraMap R (R ⧸ I ^ (n + 1 + 1))) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.Quotient.algebraMap_eq, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.le_succ _))]

theorem isPullback_adicTransition (n : ℕ) :
    IsPullback (adicTransition f I n) (pullback.snd f (adicBaseProjection I n))
      (pullback.snd f (adicBaseProjection I (n + 1)))
      (Spec.map (CommRingCat.ofHom (qR I n))) := by
  have t : IsPullback (adicProjection f I (n + 1))
      (pullback.snd f (adicBaseProjection I (n + 1))) f (adicBaseProjection I (n + 1)) :=
    IsPullback.of_hasPullback _ _
  have hb : Spec.map (CommRingCat.ofHom (qR I n)) ≫ adicBaseProjection I (n + 1) =
      adicBaseProjection I n := adicBaseTransition_projection I n
  have outer : IsPullback (adicTransition f I n ≫ adicProjection f I (n + 1))
      (pullback.snd f (adicBaseProjection I n)) f
      (Spec.map (CommRingCat.ofHom (qR I n)) ≫ adicBaseProjection I (n + 1)) := by
    rw [adicTransition_projection, hb]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right outer (pullback.lift_snd _ _ _) t

theorem adicProjection_comp_eq (n : ℕ) :
    adicProjection f I n ≫ f = pullback.snd f (adicBaseProjection I n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact pullback.condition

/-- On the inverse image of an affine open, the transition between consecutive thickenings is
surjective on sections with kernel generated by `I^(n+1)`. -/
theorem adicTransition_app_surjective_and_ker (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((adicTransition f I n).app (adicProjection f I (n + 1) ⁻¹ᵁ U.1)).hom ∧
      RingHom.ker ((adicTransition f I n).app (adicProjection f I (n + 1) ⁻¹ᵁ U.1)).hom =
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I (n + 1) ≫ f)
          (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
        (I ^ (n + 1)).map
          (algebraMap R Γ(adicSpace f I (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U.1)) :=
  surjective_and_ker_app f (adicProjection f I (n + 1)) (adicTransition f I n) (qR I n)
    (Ideal.Quotient.factor_surjective _) (pullback.snd _ _) (pullback.snd _ _)
    (isPullback_adicTransition f I n) (adicProjection_comp_eq f I (n + 1)) (I ^ (n + 1))
    (ker_qR I n) U

/-- The same facts for the map `Γ(X_(n+1), p⁻¹ U) → Γ(X_n, p⁻¹ U)` used by section pullback. -/
theorem adicTransition_appLE_surjective_and_ker (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((adicTransition f I n).appLE (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
        (adicProjection f I n ⁻¹ᵁ U.1) (le_adicTransition_preimage f I n U.1)).hom ∧
      RingHom.ker ((adicTransition f I n).appLE (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
          (adicProjection f I n ⁻¹ᵁ U.1) (le_adicTransition_preimage f I n U.1)).hom =
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I (n + 1) ≫ f)
          (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
        (I ^ (n + 1)).map
          (algebraMap R Γ(adicSpace f I (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U.1)) := by
  have key : ∀ (W : (adicSpace f I n).Opens)
      (hW : adicTransition f I n ⁻¹ᵁ (adicProjection f I (n + 1) ⁻¹ᵁ U.1) = W)
      (h : W ≤ adicTransition f I n ⁻¹ᵁ (adicProjection f I (n + 1) ⁻¹ᵁ U.1)),
      Function.Surjective ((adicTransition f I n).appLE
          (adicProjection f I (n + 1) ⁻¹ᵁ U.1) W h).hom ∧
        RingHom.ker ((adicTransition f I n).appLE
            (adicProjection f I (n + 1) ⁻¹ᵁ U.1) W h).hom =
          letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I (n + 1) ≫ f)
            (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
          (I ^ (n + 1)).map
            (algebraMap R Γ(adicSpace f I (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U.1)) := by
    rintro W rfl h
    rw [Scheme.Hom.appLE_eq_app]
    exact adicTransition_app_surjective_and_ker f I n U
  exact key _ (adicTransition_preimage f I n U.1) _

/-- Restriction along a morphism is compatible with the induced structure maps from `R`. -/
lemma appLE_algebraMap_comp {Z : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (g : Z ⟶ X)
    (U : X.Opens) (W : Z.Opens) (h : W ≤ g ⁻¹ᵁ U) (r : R) :
    g.appLE U W h ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (g ≫ π) W).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]

lemma algebraMap_algebraOfHom_congr {Z : Scheme.{u}} {c c' : Z ⟶ Spec (CommRingCat.of R)}
    (hc : c = c') (W : Z.Opens) (r : R) :
    (Scheme.TwoAffineOpenCover.algebraOfHom c W).algebraMap r =
      (Scheme.TwoAffineOpenCover.algebraOfHom c' W).algebraMap r := by
  subst hc; rfl

/-- On the `n`-th thickening, the structure map kills `I^(n+1)`. -/
lemma algebraMap_adicProjection_eq_zero (n : ℕ) (W : (adicSpace f I n).Opens) {r : R}
    (hr : r ∈ I ^ (n + 1)) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I n ≫ f) W).algebraMap r = 0 := by
  rw [algebraMap_eq_of_fac f (adicProjection f I n) (pullback.snd _ _)
    (adicProjection_comp_eq f I n) W r, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]

end Adic

section Sections

open Langlands.Scheme.Modules

/-- The components of an isomorphism of module sheaves are bijective on sections. -/
lemma app_bijective_of_iso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (U : Z.Opens) :
    Function.Bijective (e.hom.app U) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app U, fun x => ?_, fun y => ?_⟩
  · change (e.hom ≫ e.inv).app U x = x
    rw [e.hom_inv_id]
    rfl
  · change (e.inv ≫ e.hom).app U y = y
    rw [e.inv_hom_id]
    rfl

/-- For a quasi-coherent `M`, affine opens `W' ≤ τ⁻¹ W` with surjective restriction of functions
`σ`, and an isomorphism `e : τ^* M ≅ N`, the map `s ↦ e (τ^* s)|_{W'}` is surjective with
kernel `ker σ • Γ(M, W)`. -/
lemma surjective_and_ker_sectionPullbackLE {Y Z : Scheme.{u}} (τ : Z ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] {N : Z.Modules} (e : (Scheme.Modules.pullback τ).obj M ≅ N)
    {W' : Z.Opens} {W : Y.Opens} (h : W' ≤ τ ⁻¹ᵁ W) (hW' : IsAffineOpen W')
    (hW : IsAffineOpen W) (hσ : Function.Surjective (τ.appLE W W' h).hom) :
    Function.Surjective (fun s : Γ(M, W) => e.hom.app W' (sectionPullbackLE τ M h s)) ∧
      ∀ s : Γ(M, W), e.hom.app W' (sectionPullbackLE τ M h s) = 0 ↔
        s ∈ kerSMul (τ.appLE W W' h).hom Γ(M, W) := by
  let g := (e.hom.app W').hom.comp (pullbackTensorMap τ M h).hom.toAddMonoidHom
  have hg : Function.Bijective g :=
    (app_bijective_of_iso e W').comp (pullbackTensorMap_bijective τ M h hW' hW)
  have hgs : ∀ s : Γ(M, W), g ((1 : Γ(Z, W')) ⊗ₜ[Γ(Y, W), (τ.appLE W W' h).hom] s) =
      e.hom.app W' (sectionPullbackLE τ M h s) := fun s => by
    change e.hom.app W' (pullbackTensorMap τ M h
      ((1 : Γ(Z, W')) ⊗ₜ[Γ(Y, W), (τ.appLE W W' h).hom] s)) = _
    rw [pullbackTensorMap_one_tmul]
  obtain ⟨hs, hk⟩ := surjective_and_ker_of_bijective hσ g hg
  refine ⟨fun t => ?_, fun s => ?_⟩
  · obtain ⟨s, hs'⟩ := hs t
    exact ⟨s, (hgs s).symm.trans hs'⟩
  · rw [← hgs]
    exact hk s

end Sections

section LocMod

variable {Z : Scheme.{u}} (M : Z.Modules) [M.IsQuasicoherent]

/-- On an affine open `W` of a quasi-coherent module, sections over a basic open `D(g)` lift up
to a power of `g`, and sections vanishing on `D(g)` are killed by a power of `g`. -/
theorem loc_core_mod (W : Z.affineOpens) (g : Γ(Z, W.1)) (W' : Z.Opens) (hle : W' ≤ W.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(M, W'), ∃ (n : ℕ) (z : Γ(M, W.1)),
        M.presheaf.map (homOfLE hle).op z = (Z.presheaf.map (homOfLE hle).op).hom (g ^ n) • x) ∧
      (∀ z : Γ(M, W.1), M.presheaf.map (homOfLE hle).op z = 0 → ∃ n : ℕ, (g ^ n) • z = 0) := by
  subst hW'
  refine ⟨fun x => ?_, fun z hz => AffineVanishing.exists_pow_smul_eq_zero_aux W.2 M g z hz⟩
  obtain ⟨n, t, ht⟩ := AffineVanishing.exists_pow_smul_eq_res_aux W.2 M g x
  refine ⟨n, t, ?_⟩
  rw [map_pow]
  exact ht

end LocMod

section System

open Picard.FormalLineBundle Langlands.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {I : Ideal R} (F : FormalModuleSystem f I)

/-- The module presheaf `U ↦ Γ(F_n, p_n⁻¹ U)` on `X`, where `p_n : X_n ⟶ X` is the `n`-th adic
thickening. -/
abbrev presheaf (n : ℕ) : OModulePresheaf f :=
  OModulePresheaf.pushforward f (adicProjection f I n)
    (OModulePresheaf.ofModules (adicProjection f I n ≫ f) (F.obj n))

/-- The transition on sections: pull back along `X_n ⟶ X_(n+1)`, then apply the transition
isomorphism of the system. -/
def transitionSections (n : ℕ) (U : X.Opens)
    (s : Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U)) :
    Γ(F.obj n, adicProjection f I n ⁻¹ᵁ U) :=
  (F.transition n).hom.app _
    (sectionPullbackLE (adicTransition f I n) (F.obj (n + 1)) (le_adicTransition_preimage f I n U)
      s)

lemma transitionSections_add (n : ℕ) (U : X.Opens)
    (s s' : Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U)) :
    transitionSections F n U (s + s') =
      transitionSections F n U s + transitionSections F n U s' := by
  simp only [transitionSections, sectionPullbackLE_add, map_add]

lemma transitionSections_smul (n : ℕ) (U : X.Opens)
    (a : Γ(adicSpace f I (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U))
    (s : Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U)) :
    transitionSections F n U (a • s) =
      (adicTransition f I n).appLE (adicProjection f I (n + 1) ⁻¹ᵁ U)
        (adicProjection f I n ⁻¹ᵁ U) (le_adicTransition_preimage f I n U) a •
        transitionSections F n U s := by
  rw [transitionSections, sectionPullbackLE_smul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  rfl

lemma transitionSections_map (n : ℕ) {U U' : X.Opens} (h : U ≤ U')
    (s : Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U')) :
    transitionSections F n U ((F.obj (n + 1)).presheaf.map
        (homOfLE ((Opens.map (adicProjection f I (n + 1)).base).monotone h)).op s) =
      (F.obj n).presheaf.map (homOfLE ((Opens.map (adicProjection f I n).base).monotone h)).op
        (transitionSections F n U' s) := by
  rw [transitionSections, transitionSections, sectionPullbackLE_restrict,
    OpenCoverHomGluing.hom_map_app, map_sectionPullbackLE]

/-- The transition on sections as an `R`-linear map. -/
def phiLin (n : ℕ) (U : X.Opens) : (presheaf F (n + 1)).obj U →ₗ[R] (presheaf F n).obj U where
  toFun s := transitionSections F n U s
  map_add' := transitionSections_add F n U
  map_smul' r s := by
    change transitionSections F n U
        ((Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I (n + 1) ≫ f)
          (adicProjection f I (n + 1) ⁻¹ᵁ U)).algebraMap r •
            (show Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U) from s)) =
      (Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I n ≫ f)
          (adicProjection f I n ⁻¹ᵁ U)).algebraMap r • transitionSections F n U s
    rw [transitionSections_smul, appLE_algebraMap_comp]
    congr 1
    exact algebraMap_algebraOfHom_congr (adicTransition_projection_assoc f I n f) _ r

lemma phiLin_apply (n : ℕ) (U : X.Opens) (s : (presheaf F (n + 1)).obj U) :
    phiLin F n U s = transitionSections F n U s := rfl

/-- The transition maps of the module presheaves on affine opens. -/
def phi (n : ℕ) : OModulePresheaf.AffHom (presheaf F (n + 1)) (presheaf F n) where
  app U := phiLin F n U.1
  app_smul U a s := by
    change transitionSections F n U.1
        ((adicProjection f I (n + 1)).appLE U.1 (adicProjection f I (n + 1) ⁻¹ᵁ U.1) le_rfl a •
          (show Γ(F.obj (n + 1), adicProjection f I (n + 1) ⁻¹ᵁ U.1) from s)) =
      (adicProjection f I n).appLE U.1 (adicProjection f I n ⁻¹ᵁ U.1) le_rfl a •
        transitionSections F n U.1 s
    rw [transitionSections_smul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (adicTransition_projection f I n) _ _ _ le_rfl]
  naturality {U U'} h := LinearMap.ext fun s => transitionSections_map F n h s

lemma phi_app (n : ℕ) (U : X.affineOpens) (s : (presheaf F (n + 1)).obj U.1) :
    (phi F n).app U s = transitionSections F n U.1 s := rfl

theorem preimage_basicOpen_eq {V Z : Scheme.{u}} (ι : Z ⟶ V) (U : V.affineOpens)
    (r : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen r = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl r) := by
  rw [Scheme.Hom.appLE_eq_app]
  exact Scheme.preimage_basicOpen ι r

theorem preimage_basicOpen_le {V Z : Scheme.{u}} (ι : Z ⟶ V) (U : V.affineOpens)
    (r : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen r ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le r hx

/-- The module presheaves are coherent: finitely generated sections over affine opens. -/
theorem isCoherent_presheaf (hF : ∀ n, (F.obj n).IsFinitePresentation) (n : ℕ) :
    (presheaf F n).IsCoherent := by
  intro U
  set p := adicProjection f I n with hp
  have hW : IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  have := hF n
  have hfinL : Module.Finite Γ(adicSpace f I n, p ⁻¹ᵁ U.1) Γ(F.obj n, p ⁻¹ᵁ U.1) :=
    hasFiniteAffineSections_of_isFinitePresentation (F.obj n) ⟨p ⁻¹ᵁ U.1, hW⟩
  have hfin : (p.app U.1).hom.Finite := IsFinite.finite_app p U.1 U.2
  let alg : Algebra Γ(X, U.1) Γ(adicSpace f I n, p ⁻¹ᵁ U.1) :=
    (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(X, U.1) Γ(adicSpace f I n, p ⁻¹ᵁ U.1) := by
    change (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom.Finite
    rw [Scheme.Hom.appLE_eq_app]
    exact hfin
  let modXU : Module Γ(X, U.1) Γ(F.obj n, p ⁻¹ᵁ U.1) :=
    Module.compHom _ (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom
  have : IsScalarTower Γ(X, U.1) Γ(adicSpace f I n, p ⁻¹ᵁ U.1) Γ(F.obj n, p ⁻¹ᵁ U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans Γ(adicSpace f I n, p ⁻¹ᵁ U.1) Γ(F.obj n, p ⁻¹ᵁ U.1)

/-- The module presheaves are quasi-coherent in the sense of `OModulePresheaf.IsQuasicoherent`. -/
theorem isQuasicoherent_presheaf (hF : ∀ n, (F.obj n).IsFinitePresentation) (n : ℕ) :
    (presheaf F n).IsQuasicoherent := by
  intro U r
  set p := adicProjection f I n with hp
  have := hF n
  have hW : IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  obtain ⟨h1, h2⟩ := loc_core_mod (F.obj n) ⟨p ⁻¹ᵁ U.1, hW⟩
    (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl r) (p ⁻¹ᵁ X.basicOpen r) (preimage_basicOpen_le p U r)
    (preimage_basicOpen_eq p U r)
  have hres : ∀ z : (presheaf F n).obj U.1, (presheaf F n).res (X.basicOpen_le r) z =
      (show (presheaf F n).obj (X.basicOpen r) from
        (F.obj n).presheaf.map (homOfLE (preimage_basicOpen_le p U r)).op z) := fun _ => rfl
  have hsm : ∀ (a : Γ(X, U.1)) (x : (presheaf F n).obj (X.basicOpen r)),
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a • x) =
        (show (presheaf F n).obj (X.basicOpen r) from
          ((adicSpace f I n).presheaf.map (homOfLE (preimage_basicOpen_le p U r)).op).hom
            (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl a) •
            (show Γ(F.obj n, p ⁻¹ᵁ X.basicOpen r) from x)) := by
    intro a x
    change p.appLE (X.basicOpen r) (p ⁻¹ᵁ X.basicOpen r) le_rfl
        ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op) a) •
        (show Γ(F.obj n, p ⁻¹ᵁ X.basicOpen r) from x) = _
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  constructor
  · intro x
    obtain ⟨m, z, hz⟩ := h1 x
    refine ⟨m, z, ?_⟩
    rw [hres, hsm, map_pow (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom]
    exact hz
  · intro z hz
    rw [hres] at hz
    obtain ⟨m, hm⟩ := h2 z hz
    refine ⟨m, ?_⟩
    change p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl (r ^ m) • (show Γ(F.obj n, p ⁻¹ᵁ U.1) from z) = 0
    rw [map_pow (p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl).hom]
    exact hm

/-- On affine opens, the transition maps are surjective with kernel `I^(n+1)` times the
sections. -/
theorem surjective_and_ker_phi (hF : ∀ n, (F.obj n).IsFinitePresentation) (n : ℕ)
    (U : X.affineOpens) :
    Function.Surjective ((phi F n).app U) ∧
      LinearMap.ker ((phi F n).app U) =
        I ^ (n + 1) • (⊤ : Submodule R ((presheaf F (n + 1)).obj U.1)) := by
  have := hF (n + 1)
  obtain ⟨hσs, hσk⟩ := adicTransition_appLE_surjective_and_ker f I n U
  obtain ⟨hs, hk⟩ := surjective_and_ker_sectionPullbackLE (adicTransition f I n) (F.obj (n + 1))
    (F.transition n) (le_adicTransition_preimage f I n U.1) (U.2.preimage _) (U.2.preimage _) hσs
  refine ⟨hs, Submodule.ext fun s => ?_⟩
  let := Scheme.TwoAffineOpenCover.algebraOfHom (adicProjection f I (n + 1) ≫ f)
    (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
  let := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (adicProjection f I (n + 1) ≫ f)
    (F.obj (n + 1)) (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
  have := Scheme.TwoAffineOpenCover.isScalarTower_sections (adicProjection f I (n + 1) ≫ f)
    (F.obj (n + 1)) (adicProjection f I (n + 1) ⁻¹ᵁ U.1)
  rw [LinearMap.mem_ker, phi_app, transitionSections, hk s, kerSMul, hσk,
    ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

end System

end Langlands.AlgebraicGeometry.Modules.FormalModuleSystemPresheaves
