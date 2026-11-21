import Langlands.Automorphic.FiniteIsotypicOperatorQuotient
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.TensorProduct.MultiplicityCancellation
import Mathlib.RingTheory.Flat.Basic

/-! # Finite and infinite tensor actions on the free adelic operators -/

noncomputable section

universe u v

open scoped MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.AdelicFiniteInfiniteOperatorTensor

open Langlands.Automorphic
open Langlands.Correspondence (IsSubquotientOf)

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "G" => FiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "Ops" => FreeOperatorAlgebra F n
local notation "finOp" => fun g : G => FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))
local notation "cmpOp" => fun k : K => FreeAlgebra.ι ℂ (Sum.inl (Sum.inr k))

section TensorAction

variable {V W I : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup I] [Module ℂ I]
  (ρ : Representation ℂ (FiniteAdelicGL F n) V) (κ : Representation ℂ (standardInfiniteCompact F n) I)
  (δ : ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ I)

/-- The actual finite and infinite operators each act on their corresponding tensor factor. -/
def tensorOperatorAction : Ops →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] I) :=
  FreeAlgebra.lift ℂ fun
    | Sum.inl (Sum.inl g) => (ρ g).rTensor I
    | Sum.inl (Sum.inr k) => (κ k).lTensor V
    | Sum.inr X => (δ X).lTensor V

private theorem tensorOperatorAction_finite (g : G) :
    tensorOperatorAction F n ρ κ δ (finOp g) =
      Representation.tprod ρ (Representation.trivial ℂ G I) g := by
  rw [tensorOperatorAction, FreeAlgebra.lift_ι_apply]
  rfl

private theorem tensorOperatorAction_compact (k : K) :
    tensorOperatorAction F n ρ κ δ (cmpOp k) =
      Representation.tprod (Representation.trivial ℂ K V) κ k := by
  rw [tensorOperatorAction, FreeAlgebra.lift_ι_apply]
  rfl

variable {ρ} {σ : Representation ℂ (FiniteAdelicGL F n) W}

/-- Intertwiners on the finite factor commute with every free operator. -/
def tensorOperatorIntertwiner (f : ρ.IntertwiningMap σ) :
    Representation.IntertwiningMap (tensorOperatorAction F n ρ κ δ).toMonoidHom
      (tensorOperatorAction F n σ κ δ).toMonoidHom := by
  refine ⟨f.toLinearMap.rTensor I, fun a => ?_⟩
  apply LinearMap.ext
  intro x
  change f.toLinearMap.rTensor I (tensorOperatorAction F n ρ κ δ a x) =
    tensorOperatorAction F n σ κ δ a (f.toLinearMap.rTensor I x)
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 c => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | grade1 a =>
    have h : (f.toLinearMap.rTensor I).comp (tensorOperatorAction F n ρ κ δ (FreeAlgebra.ι ℂ a)) =
        (tensorOperatorAction F n σ κ δ (FreeAlgebra.ι ℂ a)).comp (f.toLinearMap.rTensor I) := by
      apply TensorProduct.ext'
      intro x y
      rcases a with (g | k) | X
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply,
          LinearMap.comp_apply, LinearMap.rTensor_tmul]
        exact congrArg (fun w : W => w ⊗ₜ[ℂ] y) (f.isIntertwining _ _ g x)
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply,
          LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      · simp only [tensorOperatorAction, FreeAlgebra.lift_ι_apply,
          LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact LinearMap.congr_fun h x
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

end TensorAction

section Isotypic

variable {W I : Type v} [AddCommGroup W] [Module ℂ W] [AddCommGroup I] [Module ℂ I]
  (σ : Representation ℂ (FiniteAdelicGL F n) W) [σ.IsIrreducible]

private theorem isotypicComponent_tensorFiniteAction_eq_top :
    isotypicComponent ℂ[G] (Representation.tprod σ (Representation.trivial ℂ G I)).asModule
      σ.asModule = ⊤ := by
  let τ := Representation.tprod σ (Representation.trivial ℂ G I)
  let S := isotypicComponent ℂ[G] τ.asModule σ.asModule
  have h (x : W) (y : I) : τ.asModuleEquiv.symm (x ⊗ₜ[ℂ] y) ∈ S := by
    let f : σ.IntertwiningMap τ := Langlands.TensorMultiplicity.slice σ y
    let A := ℂ[G]
    let L : σ.asModule →ₗ[A] τ.asModule := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
    change L (σ.asModuleEquiv.symm x) ∈ S
    obtain hL | hL := L.injective_or_eq_zero
    · exact (le_sSup (s := {P : Submodule A τ.asModule | Nonempty (P ≃ₗ[A] σ.asModule)})
        ⟨(LinearEquiv.ofInjective L hL).symm⟩) (LinearMap.mem_range_self L _)
    · rw [hL, LinearMap.zero_apply]
      exact S.zero_mem
  have hs (t : W ⊗[ℂ] I) : τ.asModuleEquiv.symm t ∈ S := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add]
      exact S.add_mem h₁ h₂
  apply top_unique
  intro z _
  obtain ⟨t, rfl⟩ := τ.asModuleEquiv.symm.surjective z
  exact hs t

end Isotypic

section Subquotients

variable {H V W Z : Type*} [Monoid H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ H V} {σ : Representation ℂ H W} {τ : Representation ℂ H Z}

private theorem isSubquotientOf_of_injective_of_surjective (i : ρ.IntertwiningMap σ)
    (hi : Function.Injective i) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q) :
    ∃ (S : Subrepresentation σ) (p : S.toRepresentation.IntertwiningMap τ), Function.Surjective p := by
  let j : ρ.IntertwiningMap i.range.toRepresentation :=
    ⟨i.toLinearMap.rangeRestrict, fun g => LinearMap.ext fun x => Subtype.ext (i.isIntertwining _ _ g x)⟩
  let e := j.ofBijective
    ⟨fun _ _ h => hi (congrArg Subtype.val h), LinearMap.surjective_rangeRestrict _⟩
  exact ⟨i.range, q.comp e.symm.toIntertwiningMap, hq.comp e.symm.surjective⟩

private theorem isSubquotientOf_of_composition
    (h₁ : ∃ (S : Subrepresentation ρ) (p : S.toRepresentation.IntertwiningMap σ), Function.Surjective p)
    (h₂ : ∃ (S : Subrepresentation σ) (p : S.toRepresentation.IntertwiningMap τ), Function.Surjective p) :
    ∃ (S : Subrepresentation ρ) (p : S.toRepresentation.IntertwiningMap τ), Function.Surjective p := by
  obtain ⟨U, q, hq⟩ := h₁
  obtain ⟨T, p, hp⟩ := h₂
  let D : Subrepresentation U.toRepresentation :=
    { toSubmodule := T.toSubmodule.comap q.toLinearMap
      apply_mem_toSubmodule g x hx := by
        change q (U.toRepresentation g x) ∈ T
        rw [q.isIntertwining]
        exact T.apply_mem_toSubmodule g hx }
  let d : D.toRepresentation.IntertwiningMap T.toRepresentation :=
    ⟨(q.toLinearMap.comp D.toSubmodule.subtype).codRestrict T.toSubmodule Subtype.property,
      fun g => LinearMap.ext fun x => Subtype.ext (q.isIntertwining _ _ g x.val)⟩
  have hd : Function.Surjective d := fun y => by
    obtain ⟨x, hx⟩ := hq y.val
    have hm : x ∈ D.toSubmodule := by
      change q x ∈ T.toSubmodule
      rw [hx]
      exact y.property
    exact ⟨⟨x, hm⟩, Subtype.ext hx⟩
  let i : D.toRepresentation.IntertwiningMap ρ :=
    ⟨U.toSubmodule.subtype.comp D.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  exact isSubquotientOf_of_injective_of_surjective i
    (U.toSubmodule.subtype_injective.comp D.toSubmodule.subtype_injective) (p.comp d) (hp.comp hd)

end Subquotients

section Selection

variable {V W I Z : Type v} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup I] [Module ℂ I] [Nontrivial I] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (FiniteAdelicGL F n) V} {σ : Representation ℂ (FiniteAdelicGL F n) W}
  [σ.IsIrreducible]
  (κ : Representation ℂ (standardInfiniteCompact F n) I)
  (δ : ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ I)

/-- A finite tensor subquotient survives as an embedded finite representation
of a simple full operator subquotient of the ambient section model. -/
theorem hasSimpleOperatorQuotientWithFiniteType_of_tensorEmbedding
    (h : IsSubquotientOf ρ σ) (a : Ops →ₐ[ℂ] Module.End ℂ Z)
    (j : Representation.IntertwiningMap (tensorOperatorAction F n ρ κ δ).toMonoidHom a.toMonoidHom)
    (hj : Function.Injective j) :
    HasSimpleOperatorQuotientWithFiniteType a finOp cmpOp σ := by
  let fin := Representation.tprod σ (Representation.trivial ℂ G I)
  let cmp := Representation.tprod (Representation.trivial ℂ K W) κ
  let b := tensorOperatorAction F n σ κ δ
  let : IsSimpleModule ℂ[G] σ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  let : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] σ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  obtain ⟨y, hy⟩ := exists_ne (0 : I)
  let : Nontrivial (W ⊗[ℂ] I) := ⟨x ⊗ₜ[ℂ] y, 0, TensorMultiplicity.tmul_ne_zero hx hy⟩
  have hs := hasSimpleOperatorQuotientWithFiniteType_of_isotypic b finOp cmpOp fin cmp σ
    (tensorOperatorAction_finite F n σ κ δ) (tensorOperatorAction_compact F n σ κ δ)
    (isotypicComponent_tensorFiniteAction_eq_top F n σ)
  obtain ⟨Y, _, _, c, hc, finY, cmpY, hfin, hcmp, he, S, p, hp⟩ := hs
  obtain ⟨U, q, hq⟩ := h
  let incl : U.toRepresentation.IntertwiningMap ρ := ⟨U.toSubmodule.subtype, fun _ => rfl⟩
  let i₀ := tensorOperatorIntertwiner F n κ δ incl
  let p₀ := tensorOperatorIntertwiner F n κ δ q
  have hi₀ : Function.Injective i₀ := Module.Flat.rTensor_preserves_injective_linearMap
    (M := I) incl.toLinearMap U.toSubmodule.subtype_injective
  have hp₀ : Function.Surjective p₀ := LinearMap.rTensor_surjective _ hq
  have hsub := isSubquotientOf_of_injective_of_surjective (j.comp i₀) (hj.comp hi₀) p₀ hp₀
  exact ⟨Y, inferInstance, inferInstance, c, hc, finY, cmpY, hfin, hcmp, he,
    isSubquotientOf_of_composition hsub ⟨S, p, hp⟩⟩

end Selection

end Langlands.Global.AdelicFiniteInfiniteOperatorTensor
