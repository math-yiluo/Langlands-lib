import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Representation.Archimedean.GKModuleDensity
import Langlands.Representation.IsotypicRestriction
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Irreducibility inside an isotypic `(𝔤, K)`-module -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

local notation "𝒜" => FreeAlgebra ℂ (K ⊕ L)

/-- The original carrier with the free algebra acting through the compact and Lie actions. -/
private def ActionModule (_ρ : Representation ℂ K V)
    (_π : L →ₗ⁅ℂ⁆ Module.End ℂ V) := V

variable (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (σ : Representation ℂ K W) (δ : L →ₗ⁅ℂ⁆ Module.End ℂ W)

private instance : AddCommGroup (ActionModule ρ π) :=
  inferInstanceAs (AddCommGroup V)

private instance : Module ℂ (ActionModule ρ π) :=
  inferInstanceAs (Module ℂ V)

private def actionHom : 𝒜 →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ (GKModuleDensity.gens ρ π)

private instance : Module 𝒜 (ActionModule ρ π) :=
  Module.compHom V (actionHom ρ π).toRingHom

private theorem generator_smul (g : K ⊕ L) (x : ActionModule ρ π) :
    FreeAlgebra.ι ℂ g • x = GKModuleDensity.gens ρ π g x :=
  congrArg (fun f : Module.End ℂ V => f x) (FreeAlgebra.lift_ι_apply _ _)

private instance : IsScalarTower ℂ 𝒜 (ActionModule ρ π) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change actionHom ρ π (algebraMap ℂ 𝒜 c) (x : V) = c • (x : V)
    rw [AlgHom.commutes, Module.algebraMap_end_apply]

private def actionSubmodule (P : Submodule ℂ V)
    (hK : ∀ k x, x ∈ P → ρ k x ∈ P) (hL : ∀ X x, x ∈ P → π X x ∈ P) :
    Submodule 𝒜 (ActionModule ρ π) where
  carrier := (P : Set V)
  zero_mem' := P.zero_mem
  add_mem' := P.add_mem
  smul_mem' a := by
    change ∀ x, x ∈ P → actionHom ρ π a x ∈ P
    induction a using FreeAlgebra.induction with
    | grade0 c =>
        intro x hx
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
        exact P.smul_mem c hx
    | grade1 g =>
        intro x hx
        rw [actionHom, FreeAlgebra.lift_ι_apply]
        cases g with
        | inl k => exact hK k x hx
        | inr X => exact hL X x hx
    | mul a b ha hb =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb _ hx)
    | add a b ha hb =>
        intro x hx
        rw [map_add, LinearMap.add_apply]
        exact P.add_mem (ha x hx) (hb x hx)

private theorem isSimpleModule_actionModule_iff :
    IsSimpleModule 𝒜 (ActionModule ρ π) ↔ IsIrreducibleGKModule ρ π := by
  constructor
  · intro h
    refine ⟨IsSimpleModule.nontrivial 𝒜 (ActionModule ρ π), fun P hK hL => ?_⟩
    change (show Submodule ℂ (ActionModule ρ π) from P) = ⊥ ∨
      (show Submodule ℂ (ActionModule ρ π) from P) = ⊤
    have he := eq_bot_or_eq_top (actionSubmodule ρ π P hK hL)
    have hr : (actionSubmodule ρ π P hK hL).restrictScalars ℂ =
        (show Submodule ℂ (ActionModule ρ π) from P) := rfl
    simpa only [hr, Submodule.restrictScalars_bot, Submodule.restrictScalars_top] using
      he.imp (congrArg (Submodule.restrictScalars ℂ)) (congrArg (Submodule.restrictScalars ℂ))
  · rintro ⟨hV, h⟩
    let : Nontrivial (ActionModule ρ π) := hV
    refine { eq_bot_or_eq_top := fun P => ?_ }
    have he := h (P.restrictScalars ℂ)
      (fun k x hx => by
        have hm := P.smul_mem (FreeAlgebra.ι ℂ (Sum.inl k))
          (show (x : ActionModule ρ π) ∈ P from hx)
        rw [generator_smul] at hm
        exact hm)
      (fun X x hx => by
        have hm := P.smul_mem (FreeAlgebra.ι ℂ (Sum.inr X))
          (show (x : ActionModule ρ π) ∈ P from hx)
        rw [generator_smul] at hm
        exact hm)
    have hinj := Submodule.restrictScalars_injective ℂ 𝒜 (ActionModule ρ π)
    rcases he with he | he
    · exact Or.inl (hinj (he.trans (Submodule.restrictScalars_bot ℂ 𝒜 (ActionModule ρ π)).symm))
    · exact Or.inr (hinj (he.trans (Submodule.restrictScalars_top ℂ 𝒜 (ActionModule ρ π)).symm))

private def actionLinearMap {f : V →ₗ[ℂ] W} (hf : f ∈ gkHoms ρ π σ δ) :
    ActionModule ρ π →ₗ[𝒜] ActionModule σ δ where
  toFun := f
  map_add' := f.map_add
  map_smul' a := by
    change ∀ x, f (actionHom ρ π a x) = actionHom σ δ a (f x)
    induction a using FreeAlgebra.induction with
    | grade0 c =>
        intro x
        simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    | grade1 g =>
        intro x
        simp only [actionHom, FreeAlgebra.lift_ι_apply]
        cases g with
        | inl k => exact hf.1 k x
        | inr X => exact hf.2 X x
    | mul a b ha hb =>
        intro x
        simp only [map_mul, Module.End.mul_apply, ha, hb]
    | add a b ha hb =>
        intro x
        simp only [map_add, LinearMap.add_apply, ha, hb]

private theorem action_isotypicComponent_eq_top
    [IsSimpleModule 𝒜 (ActionModule ρ π)] (h : IsGKIsotypic ρ π σ δ) :
    isotypicComponent 𝒜 (ActionModule σ δ) (ActionModule ρ π) = ⊤ := by
  apply Submodule.restrictScalars_injective ℂ 𝒜 (ActionModule σ δ)
  rw [Submodule.restrictScalars_top,
    CompactSplitting.isotypicComponent_eq_iSup_range, Submodule.restrictScalars_iSup]
  have he : (⨆ f ∈ gkHoms ρ π σ δ, LinearMap.range f) =
      (⊤ : Submodule ℂ (ActionModule σ δ)) := h
  apply top_unique
  rw [← he]
  apply iSup₂_le fun f hf => ?_
  exact le_iSup (fun g : ActionModule ρ π →ₗ[𝒜] ActionModule σ δ =>
    (LinearMap.range g).restrictScalars ℂ) (actionLinearMap ρ π σ δ hf)

variable {U : Type*} [AddCommGroup U] [Module ℂ U]
  (τ : Representation ℂ K U) (η : L →ₗ⁅ℂ⁆ Module.End ℂ U)

/-- A `(𝔤, K)`-submodule of a module isotypic for a simple source is irreducible
if it has a nonzero vector scaled by every compact-equivariant endomorphism. -/
theorem isIrreducibleGKModule_of_injective_of_isotypic
    (hirr : IsIrreducibleGKModule ρ π) (hiso : IsGKIsotypic ρ π σ δ)
    (f : U →ₗ[ℂ] W) (hf : f ∈ gkHoms τ η σ δ) (hinj : Function.Injective f)
    (x : U) (hx : x ≠ 0)
    (hline : ∀ E : Module.End ℂ U, (∀ k y, E (τ k y) = τ k (E y)) →
      ∃ c : ℂ, E x = c • x) :
    IsIrreducibleGKModule τ η := by
  classical
  let : IsSimpleModule 𝒜 (ActionModule ρ π) :=
    (isSimpleModule_actionModule_iff ρ π).mpr hirr
  let a := actionLinearMap τ η σ δ hf
  have ha : Function.Injective a := hinj
  have htop : isotypicComponent 𝒜 (ActionModule τ η) (ActionModule ρ π) = ⊤ := by
    rw [← CompactSplitting.isotypicComponent_comap_of_injective 𝒜 _ a ha,
      action_isotypicComponent_eq_top ρ π σ δ hiso, Submodule.comap_top]
  let : IsSemisimpleModule 𝒜 (ActionModule τ η) :=
    IsSemisimpleModule.congr ((Submodule.topEquiv (R := 𝒜) (M := ActionModule τ η)).symm.trans
      (LinearEquiv.ofEq _ _ htop.symm))
  obtain ⟨J, ⟨e⟩⟩ := (IsIsotypicOfType.of_isotypicComponent_eq_top htop).linearEquiv_finsupp
  have hex : e x ≠ 0 := fun he => hx (e.injective (he.trans e.map_zero.symm))
  have hi : ∃ i : J, e x i ≠ 0 := by
    by_contra! h
    exact hex (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hj : ∀ j : J, j = i := by
    intro j
    by_contra hji
    let B : Module.End 𝒜 (ActionModule τ η) :=
      e.symm.toLinearMap ∘ₗ Finsupp.lsingle j ∘ₗ Finsupp.lapply i ∘ₗ e.toLinearMap
    let E : Module.End ℂ (ActionModule τ η) := B.restrictScalars ℂ
    obtain ⟨c, hc⟩ := hline E (fun k y => by
      have hm := B.map_smul (FreeAlgebra.ι ℂ (Sum.inl k)) (y : ActionModule τ η)
      rw [generator_smul, generator_smul] at hm
      exact hm)
    have heq : Finsupp.single j (e x i) = c • e x := by
      have hec := congrArg e hc
      change e (e.symm (Finsupp.single j (e x i))) = e (c • (x : ActionModule τ η)) at hec
      rw [e.apply_symm_apply] at hec
      exact hec.trans ((e.restrictScalars ℂ).map_smul c x)
    have hci : c • e x i = 0 := by
      simpa only [Finsupp.single_eq_of_ne (Ne.symm hji), Finsupp.smul_apply] using
        (DFunLike.congr_fun heq i).symm
    have hc0 : c = 0 := (smul_eq_zero.mp hci).resolve_right hi
    rw [hc0, zero_smul] at heq
    exact hi (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using
      DFunLike.congr_fun heq j)
  let : Subsingleton J := ⟨fun j j' => (hj j).trans (hj j').symm⟩
  exact (isSimpleModule_actionModule_iff τ η).mp
    (IsSimpleModule.congr (e.trans (Finsupp.uniqueLinearEquiv 𝒜 _ i)))

end Langlands.Archimedean
