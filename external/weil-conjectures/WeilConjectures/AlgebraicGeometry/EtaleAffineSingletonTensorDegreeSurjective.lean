/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Surjectivity of the affine singleton tensor comparison

Source: Stacks Project, Tag 03P2, affine tensor calculation; Tags 01I4 and 01I9.
(blueprint: new-etale-affine-singleton-tensor-degree-surjective) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A normalized affine singleton comparison lifts every target section.
Source: Stacks Project, Tag 03P2; Tags 01I4, 01JQ, 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-surjective)

Proof: put A = Γ(U,O), B = Γ(W,O), M = Γ(U*F), and P equal to the
product of n+1 copies of W over U. Iterate the affine fibre-product spectrum
formula, including its projection equations, to identify Γ(P,O) with the
indexed tensor power of B over A. The affine pullback sections formula for
P→U, followed by the unit-normalized tensor-pullback composition comparison,
identifies M tensor Γ(P,O) with Γ(P,P*F). Quasi-coherence of the tensor
pullback to U follows by comparison with ordinary pullback via uniqueness
of left adjoints. Composing and tensoring the ring identification gives an
additive equivalence E from the unlifted source to Γ(P,P*F). Its pure-tensor
formula is the product of the pulled-back functions times the normalized
restriction of the coefficient. Let q be evaluation at the unique outer
Čech index followed by ULift.down. Tensor induction, and indexed tensor
induction with the balancing relation in its scalar case, extend the given
normalization to q(f(ULift.up t)) = E(t) for every tensor t. For a target
element y, choose t = E.symm(q(y)). Then q(f(ULift.up t)) = q(y).
Evaluation at the unique index is an isomorphism (productUniqueIso), and
ULift.down is injective, so q is injective. Thus f(ULift.up t)=y, giving the
required preimage. Zero modules and empty affine schemes cause no exception;
the number of factors is n+1, including one when n=0.
-/
theorem singletonTensorDegreeComparisonHom_surjective
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    Function.Surjective (AddCommGrpCat.Hom.hom f) := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  let N := Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)
  let D : (Fin (n + 1) → Fin 1) → AddCommGrpCat.{u + 1} :=
    fun _ ↦ AddCommGrpCat.of (ULift.{u + 1} N)
  let q : (singletonTensorCech X F U W g).X n →+ N :=
    (AddEquiv.ulift : ULift.{u + 1} N ≃+ N).toAddMonoidHom.comp (Pi.π D (fun _ ↦ 0)).hom
  have hq : Function.Injective q := by
    have hi : Function.Injective (Pi.π D (fun _ ↦ 0)) := by
      have he : (fun _ : Fin (n + 1) ↦ (0 : Fin 1)) =
          (default : Fin (n + 1) → Fin 1) := Subsingleton.elim _ _
      rw [he, ← productUniqueIso_hom]
      exact (ConcreteCategory.bijective_of_isIso (productUniqueIso D).hom).1
    exact (AddEquiv.ulift : ULift.{u + 1} N ≃+ N).injective.comp hi
  have hr : (q.comp f.hom).range = ⊤ := by
    apply top_unique
    rw [← singletonTensorSections_span X F U W g hU hW n]
    apply (AddSubgroup.closure_le _).mpr
    exact singletonTensorDegreeComparisonHom_normalized_range X F U W g n f hf
  intro y
  have hy : q y ∈ (q.comp f.hom).range := by rw [hr]; trivial
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hq hx⟩

end
end AlgebraicGeometry.Scheme
