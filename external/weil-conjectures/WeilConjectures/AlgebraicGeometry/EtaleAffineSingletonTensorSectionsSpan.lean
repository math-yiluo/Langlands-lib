/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonProductRing
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv

/-! # Affine singleton tensor sections before the outer Čech product

Source: Stacks Project, Tags 03P2, 01I4, 01I9, 01IA.
(blueprint: new-etale-affine-singleton-tensor-sections-span) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

private theorem tensor_generators_span
    {R M B N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B] [AddCommGroup N] (n : ℕ)
    (E : (M ⊗[R] (⨂[R] (_ : Fin (n + 1)), B)) ≃+ N)
    (v : M × (Fin (n + 1) → B) → N)
    (hE : ∀ m b, E (m ⊗ₜ[R] PiTensorProduct.tprod R b) = v (m, b)) :
    AddSubgroup.closure (Set.range v) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨t, rfl⟩ := E.surjective x
  induction t using TensorProduct.inductionOn with
  | add t s ht hs =>
    simpa only [map_add] using (AddSubgroup.closure (Set.range v)).add_mem ht hs
  | tmul m b =>
    induction b using PiTensorProduct.induction_on generalizing m with
    | add b d hb hd =>
      simpa only [TensorProduct.tmul_add, map_add] using
        (AddSubgroup.closure (Set.range v)).add_mem (hb m) (hd m)
    | smul_tprod r b =>
      rw [← TensorProduct.smul_tmul, hE]
      exact AddSubgroup.subset_closure ⟨(r • m, b), rfl⟩

private theorem tensor_generators_span_of_equivs
    {R M B C N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup N]
    (n : ℕ) (e : (⨂[R] (_ : Fin (n + 1)), B) ≃ₗ[R] C)
    (c : (M ⊗[R] C) ≃+ N) (v : (Fin (n + 1) → B) → C)
    (action : M → C → N)
    (he : ∀ b, e (PiTensorProduct.tprod R b) = v b)
    (hc : ∀ m z, c (m ⊗ₜ[R] z) = action m z) :
    AddSubgroup.closure (Set.range (fun p : M × (Fin (n + 1) → B) ↦
      action p.1 (v p.2))) = ⊤ := by
  let E := (TensorProduct.congr (LinearEquiv.refl R M) e).toAddEquiv.trans c
  apply tensor_generators_span n E
  intro m b
  change c (m ⊗ₜ[R] e (PiTensorProduct.tprod R b)) = _
  rw [hc, he]

/-- Global sections on the iterated affine fibre product have the tensor description.
Source: Stacks Project, Tag 03P2, affine calculation; Tags 01I4, 01I9, 01IA.
(blueprint: new-etale-affine-singleton-tensor-sections-span)

Proof: write A = Γ(U,O), B = Γ(W,O), and M = Γ(U,U*F). Induct on the nonzero
number n+1 of factors, using the binary affine fibre-product spectrum formula and its
projection equations. This identifies the affine product P with the spectrum of the
indexed tensor product of the copies of B over A, with the projection pullbacks equal
to the indexed tensor inclusions. Compare tensor pullback U*F with ordinary pullback
by uniqueness of left adjoints to pushforward, and transport quasi-coherence along
this isomorphism. Apply the affine pullback sections formula to P→U and U*F.
Compose with the unit-normalized pullback composition isomorphism to identify the
iterated pullback with P*F. Tensoring the ring identification with M gives an additive
equivalence from M tensor the indexed tensor product to Γ(P,P*F). On pure tensors,
the affine sections formula multiplies the function by the unit-pulled coefficient;
the projection equations and unit normalization give the displayed generators.
Every tensor is a sum of pure tensors. Indexed tensor induction expresses the second
factor as sums of scalar multiples of tprod(b); move each scalar to M by balancing.
Thus every section is a sum of displayed generators, so their additive subgroup
closure is the whole group. For n=0 this is the ordinary affine sections formula.
Empty affine schemes and zero coefficient modules are covered by the construction.
-/
theorem singletonTensorSections_span
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    AddSubgroup.closure (Set.range (fun p :
      Γ((Modules.tensorPullback U.hom).obj F, ⊤) × (Fin (n + 1) → Γ(W.left, ⊤)) ↦
        (∏ k : Fin (n + 1),
          (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (p.2 k)) •
            Modules.etaleTensorSectionsRestriction F P.hom p.1)) = ⊤ := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let : Algebra Γ(U.left, ⊤) Γ((∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.left, ⊤) :=
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom.left.appTop.hom.toAlgebra
  obtain ⟨hP, e, he⟩ := singletonProduct_affine_ring X U W g hU hW n
  obtain ⟨c, hc⟩ := exists_etaleAffineTensorSectionsEquiv X F U
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left
    (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom hU hP
  exact tensor_generators_span_of_equivs n e c
    (fun b ↦ ∏ k : Fin (n + 1),
      (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k))
    (fun m z ↦ z • Modules.etaleTensorSectionsRestriction F
      (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom m)
    (fun b ↦ he b) (fun m z ↦ hc m z)

end
end AlgebraicGeometry.Scheme
