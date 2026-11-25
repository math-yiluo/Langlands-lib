/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonProductRing
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv
import WeilConjectures.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Zero kernel of the affine singleton tensor comparison

Source: Stacks Project, Tag 03P2, affine tensor calculation; Tags 01I4 and 01I9.
(blueprint: new-etale-affine-singleton-tensor-degree-kernel) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section


private theorem tensor_generators_ext
    {R M B N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B] [AddCommGroup N] (n : ℕ)
    (H E : (M ⊗[R] (⨂[R] (_ : Fin (n + 1)), B)) →+ N)
    (hp : ∀ m b, H (m ⊗ₜ[R] PiTensorProduct.tprod R b) =
      E (m ⊗ₜ[R] PiTensorProduct.tprod R b)) : ∀ t, H t = E t := by
  intro t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ht hs
  | tmul m b =>
    induction b using PiTensorProduct.induction_on generalizing m with
    | add b d hb hd =>
      simp only [TensorProduct.tmul_add, map_add]
      exact congrArg₂ (· + ·) (hb m) (hd m)
    | smul_tprod r b =>
      simp only [← TensorProduct.smul_tmul]
      exact hp (r • m) b

private theorem tensor_kernel {R M B N : Type u} {T : Type (u + 1)}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [AddCommGroup T] (n : ℕ)
    (f : ULift.{u + 1} (M ⊗[R] (⨂[R] (_ : Fin (n + 1)), B)) →+ T)
    (q : T →+ N) (E : (M ⊗[R] (⨂[R] (_ : Fin (n + 1)), B)) ≃+ N)
    (hp : ∀ m b, q (f (ULift.up (m ⊗ₜ[R] PiTensorProduct.tprod R b))) =
      E (m ⊗ₜ[R] PiTensorProduct.tprod R b)) : ∀ x, f x = 0 → x = 0 := by
  let H := q.comp (f.comp AddEquiv.ulift.symm.toAddMonoidHom)
  have hall (t) : H t = E t := tensor_generators_ext n H E.toAddMonoidHom hp t
  intro x hx
  obtain ⟨t⟩ := x
  have ht : H t = 0 := (congrArg q hx).trans q.map_zero
  have ht0 := E.injective ((hall t).symm.trans (ht.trans E.map_zero.symm))
  exact congrArg ULift.up ht0


private theorem tensor_kernel_of_equivs
    {R M B C N : Type u} {T : Type (u + 1)}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup N] [AddCommGroup T] (n : ℕ)
    (f : ULift.{u + 1} (M ⊗[R] (⨂[R] (_ : Fin (n + 1)), B)) →+ T)
    (q : T →+ N) (e : (⨂[R] (_ : Fin (n + 1)), B) ≃ₗ[R] C)
    (c : (M ⊗[R] C) ≃+ N) (v : (Fin (n + 1) → B) → C)
    (action : M → C → N)
    (he : ∀ b, e (PiTensorProduct.tprod R b) = v b)
    (hc : ∀ m z, c (m ⊗ₜ[R] z) = action m z)
    (hq : ∀ m b, q (f (ULift.up (m ⊗ₜ[R] PiTensorProduct.tprod R b))) =
      action m (v b)) : ∀ x, f x = 0 → x = 0 := by
  let E := (TensorProduct.congr (LinearEquiv.refl R M) e).toAddEquiv.trans c
  apply tensor_kernel n f q E
  intro m b
  change q (f (ULift.up (m ⊗ₜ[R] PiTensorProduct.tprod R b))) =
    c (m ⊗ₜ[R] e (PiTensorProduct.tprod R b))
  rw [hc, he]
  exact hq m b



/-- A normalized affine singleton comparison has zero kernel.
Source: Stacks Project, Tag 03P2; Tags 01I4, 01JQ, 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-kernel)

Proof: write A = Γ(U,O), B = Γ(W,O), M = Γ(U*F), and let P be the
product of n+1 copies of W over U. Iterating the binary affine fibre-product
spectrum formula identifies Γ(P,O) with the indexed tensor power of B over A;
the single-factor inclusions are pullback along the projections. Affine
pullback sections identify M tensor Γ(P,O) with Γ(P,U*F pulled back to P).
Compare tensor pullback with ordinary pullback by uniqueness of left adjoints
to transport quasi-coherence. Compose with the unit-normalized tensor-pullback
composition isomorphism to identify the latter sections with Γ(P,P*F).
Tensoring the ring equivalence with M gives an additive equivalence E from
the unlifted source tensor module to Γ(P,P*F). Its value on m tensor tprod(b)
is the product of the pulled-back b_i times the normalized restriction of m.
Evaluation at the unique outer Čech index, followed by ULift.down, is an
additive map q from the target to these sections. The normalization of f
says q(f(ULift.up t)) = E(t) on pure generators. TensorProduct.induction_on,
then PiTensorProduct.induction_on in the second factor, extends this equality
to all tensors: handle sums by additivity, and move a scalar from an indexed
pure tensor to the coefficient using the tensor balancing relation. If
f(x)=0, this equality gives E(x.down)=0=E(0). Injectivity of E gives
x.down=0, and injectivity of ULift.down gives x=0. This proof covers zero
modules and empty affine schemes; n=0 still has one factor.
-/
theorem singletonTensorDegreeComparisonHom_kernel
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∀ x, (AddCommGrpCat.Hom.hom f) x = 0 → x = 0 := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let : Algebra Γ(U.left, ⊤)
      Γ((∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.left, ⊤) :=
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom.left.appTop.hom.toAlgebra
  obtain ⟨hP, e, he⟩ := singletonProduct_affine_ring X U W g hU hW n
  obtain ⟨c, hc⟩ := exists_etaleAffineTensorSectionsEquiv X F U
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom hU hP
  obtain ⟨q, hq⟩ := singletonTensor_normalization_evaluation X F U W g n f hf
  dsimp only at he hc hq
  change ∀ x : ULift.{u + 1} (Γ((Modules.tensorPullback U.hom).obj F, ⊤)
    ⊗[Γ(U.left, ⊤)] (⨂[Γ(U.left, ⊤)] (_ : Fin (n + 1)), Γ(W.left, ⊤))),
      (AddCommGrpCat.Hom.hom f) x = 0 → x = 0
  refine tensor_kernel_of_equivs n (AddCommGrpCat.Hom.hom f) q e c
    (fun b ↦ ∏ k : Fin (n + 1),
      (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k))
    (fun m z ↦ z • Modules.etaleTensorSectionsRestriction F
      (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom m)
    (fun b ↦ he b) (fun m z ↦ hc m z) (fun m b ↦ hq m b)

end
end AlgebraicGeometry.Scheme
