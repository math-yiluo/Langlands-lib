/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.RingTheory.PiTensorProduct

/-! # Functions on an affine singleton Čech product

Source: Stacks Project, Tags 01I4 and 01JQ.
(blueprint: new-etale-affine-singleton-product-ring) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

section TensorColimit

variable {ι : Type} {A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [Algebra A B]

-- The opposite of the common-base diagram for the factor algebras.
private abbrev ringDiagram :=
  (WidePullbackShape.wideCospan (op <| CommRingCat.of A)
    (fun _ : ι ↦ op <| CommRingCat.of B)
    (fun _ ↦ (CommRingCat.ofHom (algebraMap A B)).op)).leftOp

-- The factor inclusions form the canonical tensor-power cocone.
private noncomputable def tensorCocone : Cocone (ringDiagram (ι := ι) (A := A) (B := B)) where
  pt := CommRingCat.of (⨂[A] (_ : ι), B)
  ι :=
    { app := by
        intro j
        cases j with
        | op j =>
          cases j with
          | none => exact CommRingCat.ofHom (algebraMap A (⨂[A] (_ : ι), B))
          | some i =>
            exact CommRingCat.ofHom
              (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : ι ↦ B) i).toRingHom
      naturality := by
        intro j k f
        cases j with | op j =>
          cases k with | op k =>
            cases f with | op f =>
              cases f with
              | id j =>
                change ringDiagram.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
                simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
              | term i =>
                ext a
                exact (PiTensorProduct.singleAlgHom
                  (R := A) (A := fun _ : ι ↦ B) i).commutes a }

private noncomputable def coconeAlgHom
    (s : Cocone (ringDiagram (ι := ι) (A := A) (B := B))) (i : ι) :
    letI : Algebra A s.pt := (s.ι.app (op none)).hom.toAlgebra
    B →ₐ[A] s.pt := by
  letI : Algebra A s.pt := (s.ι.app (op none)).hom.toAlgebra
  exact
    { toRingHom := (s.ι.app (op (some i))).hom
      commutes' := fun a ↦ congrArg (fun t ↦ t.hom a)
        (s.w (Quiver.Hom.op (WidePullbackShape.Hom.term i))) }

-- Compatible factor maps extend uniquely by multiplying their values on pure tensors.
private noncomputable def tensorCoconeIsColimit :
    IsColimit (tensorCocone (ι := ι) (A := A) (B := B)) where
  desc s := by
    letI : Algebra A s.pt := (s.ι.app (op none)).hom.toAlgebra
    exact CommRingCat.ofHom (PiTensorProduct.liftCommAlgHom (coconeAlgHom s)).toRingHom
  fac s j := by
    let : Algebra A s.pt := (s.ι.app (op none)).hom.toAlgebra
    cases j with
    | op j =>
      cases j with
      | none =>
        ext a
        exact (PiTensorProduct.liftCommAlgHom (coconeAlgHom s)).commutes a
      | some i =>
        ext b
        exact PiTensorProduct.liftCommAlgHom_singleAlgHom (coconeAlgHom s) i b
  uniq s m hm := by
    let : Algebra A s.pt := (s.ι.app (op none)).hom.toAlgebra
    let m' : (⨂[A] (_ : ι), B) →ₐ[A] s.pt :=
      { toRingHom := m.hom
        commutes' := fun a ↦ congrArg (fun t ↦ t.hom a) (hm (op none)) }
    apply CommRingCat.hom_ext
    change m'.toRingHom = (PiTensorProduct.liftCommAlgHom (coconeAlgHom s)).toRingHom
    apply congrArg (fun f : (⨂[A] (_ : ι), B) →ₐ[A] s.pt ↦ f.toRingHom)
    apply PiTensorProduct.algHom_ext
    intro i
    ext b
    change m' (PiTensorProduct.singleAlgHom i b) =
      PiTensorProduct.liftCommAlgHom (coconeAlgHom s) (PiTensorProduct.singleAlgHom i b)
    rw [PiTensorProduct.liftCommAlgHom_singleAlgHom]
    exact congrArg (fun t ↦ t.hom b) (hm (op (some i)))

end TensorColimit

/-- The iterated product is affine, and its functions are the indexed tensor power,
with the expected formula on indexed pure tensors.
Source: Stacks Project, Tags 01I4 and 01JQ.
(blueprint: new-etale-affine-singleton-product-ring)

Proof: take affine spectrum charts for U and W.  For one factor the product is W
and the single-factor indexed tensor power is B.  Add one factor at a time using
Spec(B) × Spec(C) = Spec(B tensor C) over Spec(A).  Associativity of tensor products
and the universal property of the indexed tensor product identify the resulting
ring with the indexed tensor power.  The binary spectrum formula identifies each
projection with the corresponding tensor-factor inclusion.  Multiplying those
inclusions gives the displayed pure-tensor equation.  The spectrum charts also
prove affineness.  The induction starts with one factor, including n = 0; the zero
ring and the empty affine scheme require no extra hypotheses.
-/
theorem singletonProduct_affine_ring
    (X : Scheme.{u}) (U W : X.Etale) (g : W ⟶ U)
    (hU : IsAffine U.left) (hW : IsAffine W.left) (n : ℕ) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    letI : Algebra Γ(U.left, ⊤) Γ(P.left.left, ⊤) := P.hom.left.appTop.hom.toAlgebra
    IsAffine P.left.left ∧
      ∃ e : (⨂[Γ(U.left, ⊤)] (_ : Fin (n + 1)), Γ(W.left, ⊤)) ≃ₗ[Γ(U.left, ⊤)]
        Γ(P.left.left, ⊤),
        ∀ b : Fin (n + 1) → Γ(W.left, ⊤),
          e (PiTensorProduct.tprod Γ(U.left, ⊤) b) =
            ∏ k : Fin (n + 1),
              (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k) := by
  -- Compare the wide-pushout cocones of the tensor power and the product sections.
  classical
  dsimp only
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  let : Algebra Γ(U.left, ⊤) Γ(P.left.left, ⊤) := P.hom.left.appTop.hom.toAlgebra
  let D := Discrete.functor (fun _ : Fin (n + 1) ↦ Over.mk g)
  let E := Over.ConstructProducts.conesEquiv U D
  let c := E.inverse.obj (limit.cone D)
  have hc : IsLimit c := IsLimit.ofRightAdjoint E.toAdjunction (limit.isLimit D)
  let F := Etale.forget X ⋙ Over.forget X
  let cS := F.mapCone c
  have hS : IsLimit cS := isLimitOfPreserves F hc
  have : ∀ i, IsAffine
      ((Over.ConstructProducts.widePullbackDiagramOfDiagramOver U D ⋙ F).obj i) := by
    intro i
    cases i
    · exact hU
    · exact hW
  refine ⟨Scheme.isAffine_of_isLimit cS hS, ?_⟩
  let δ : ((Over.ConstructProducts.widePullbackDiagramOfDiagramOver U D ⋙ F) ⋙
      Scheme.Γ.rightOp) ≅
      WidePullbackShape.wideCospan (op <| CommRingCat.of Γ(U.left, ⊤))
        (fun _ : Fin (n + 1) ↦ op <| CommRingCat.of Γ(W.left, ⊤))
        (fun _ ↦ (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) Γ(W.left, ⊤))).op) :=
    WidePullbackShape.functorExt (Iso.refl _) (fun _ ↦ Iso.refl _) (by
      intro i
      rfl)
  let cG := (Cone.postcompose δ.hom).obj (Scheme.Γ.rightOp.mapCone cS)
  have hG : IsLimit cG := (IsLimit.postcomposeHomEquiv δ _).symm
    (isLimitOfPreserves Scheme.Γ.rightOp hS)
  let cR : Cocone (ringDiagram (ι := Fin (n + 1))
      (A := Γ(U.left, ⊤)) (B := Γ(W.left, ⊤))) := coconeLeftOpOfCone cG
  have hR : IsColimit cR := isColimitCoconeLeftOpOfCone _ hG
  let ht := tensorCoconeIsColimit (ι := Fin (n + 1))
    (A := Γ(U.left, ⊤)) (B := Γ(W.left, ⊤))
  let e := ht.coconePointUniqueUpToIso hR
  have he (j : (WidePullbackShape (Fin (n + 1)))ᵒᵖ) :=
    ht.comp_coconePointUniqueUpToIso_hom hR j
  let : Algebra Γ(U.left, ⊤) cR.pt := (cR.ι.app (op none)).hom.toAlgebra
  let eA : (⨂[Γ(U.left, ⊤)] (_ : Fin (n + 1)), Γ(W.left, ⊤)) ≃ₐ[Γ(U.left, ⊤)]
      Γ(P.left.left, ⊤) :=
    AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv)
      (fun a ↦ congrArg (fun t ↦ t.hom a) (he (op none)))
  have heq : eA.toAlgHom = PiTensorProduct.liftCommAlgHom (coconeAlgHom cR) := by
    apply PiTensorProduct.algHom_ext
    intro i
    ext b
    change eA (PiTensorProduct.singleAlgHom i b) =
      PiTensorProduct.liftCommAlgHom (coconeAlgHom cR) (PiTensorProduct.singleAlgHom i b)
    rw [PiTensorProduct.liftCommAlgHom_singleAlgHom]
    exact congrArg (fun t ↦ t.hom b) (he (op (some i)))
  refine ⟨eA.toLinearEquiv, ?_⟩
  intro b
  change eA.toAlgHom (PiTensorProduct.tprod Γ(U.left, ⊤) b) = _
  rw [heq]
  exact (PiTensorProduct.liftCommAlgHom_tprod (coconeAlgHom cR) b).trans (by rfl)
end
end AlgebraicGeometry.Scheme
