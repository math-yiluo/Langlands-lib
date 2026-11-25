/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
/-! # Morphisms between base-derived tensor cohomology models

Source: Stacks Project, More on Algebra, Tag 06Y6, functoriality of the
derived tensor product and its commuting coefficient actions.
(blueprint: lem-pc-base-derived-tensor-cohomology-model-map).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality lifted to the tensor-algebra cohomology objects of any two models.
Source: Stacks Project, More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-derived-tensor-cohomology-model-map).

Proof: the universal counits determine the unique derived-functor isomorphism
from L.derived to K.derived. Let delta be its forward natural transformation.
Apply cohomology to L.derived applied to f, then delta, and conjugate by the
two cohomologyIso isomorphisms. This is a B-linear map. For each a in A,
f commutes with multiplication by a; naturality of delta and the two
cohomologyIso_smul equations show that the conjugated map also commutes
with a tensor 1. Together with B-linearity, this gives linearity for every
pure tensor a tensor b, and tensor induction gives A tensor_R B-linearity.
Regard it as a ModuleCat morphism g. Its restriction to B is exactly the
conjugated map by construction, yielding the stated equation. -/
theorem exists_baseDerivedTensorCohomologyModelMap
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D) (i : ℤ) :
    ∃ (δ : L.derived ⟶ K.derived) (g : L.cohomology i ⟶ K.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            K.counit = L.counit ∧
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (K.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) := by
  classical
  let := L.universal
  let := K.universal
  let δ := (Functor.leftDerivedUnique K.derived L.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))).hom
  have hδ : Functor.whiskerLeft DerivedCategory.Qh δ ≫ K.counit = L.counit := by
    simp [δ, Functor.leftDerivedNatTrans,
      Functor.leftDerived_fac]
  let F := restrict R A ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙
    DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let β := (L.cohomologyIso i).hom ≫ H.map (L.derived.map (F.map f)) ≫
    H.map (δ.app (F.obj Q')) ≫ (K.cohomologyIso i).inv
  have hβ : β ≫ (K.cohomologyIso i).hom =
      (L.cohomologyIso i).hom ≫ H.map (L.derived.map (F.map f)) ≫
        H.map (δ.app (F.obj Q')) := by simp [β, Category.assoc]
  have hleft (a : A) :
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (L.cohomology i)) ≫ β =
      β ≫ (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (K.cohomology i)) := by
    let G := F ⋙ L.derived ⋙ H
    have hf : G.map (a • 𝟙 Q) ≫ G.map f = G.map f ≫ G.map (a • 𝟙 Q') := by
      rw [← G.map_comp, ← G.map_comp]
      congr 1
      simp
    have hn : H.map (L.derived.map (F.map (a • 𝟙 Q'))) ≫
          H.map (δ.app (F.obj Q')) =
        H.map (δ.app (F.obj Q')) ≫ H.map (K.derived.map (F.map (a • 𝟙 Q'))) := by
      simpa only [H.map_comp] using congrArg H.map (δ.naturality (F.map (a • 𝟙 Q')))
    apply (cancel_mono (K.cohomologyIso i).hom).1
    rw [Category.assoc, hβ, ← Category.assoc, L.cohomologyIso_smul i a]
    simp only [Category.assoc]
    rw [K.cohomologyIso_smul i a]
    rw [← Category.assoc β (K.cohomologyIso i).hom, hβ]
    simp only [Category.assoc]
    congr 1
    change G.map (a • 𝟙 Q) ≫ G.map f ≫ _ = _
    rw [← Category.assoc, hf, Category.assoc]
    change H.map (L.derived.map (F.map f)) ≫
        (H.map (L.derived.map (F.map (a • 𝟙 Q'))) ≫ H.map (δ.app (F.obj Q'))) = _
    rw [hn]
    rfl
  have hleft_apply (a : A) (x : L.cohomology i) :
      β ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • β x := by
    simpa using congrArg (fun k ↦ k x) (hleft a)
  have hright_apply (b : B) (x : L.cohomology i) :
      β ((Algebra.TensorProduct.includeRight (R := R) (A := A) b) • x) =
        (Algebra.TensorProduct.includeRight (R := R) (A := A) b) • β x := by
    exact β.hom.map_smul b x
  let g : L.cohomology i ⟶ K.cohomology i := ModuleCat.ofHom
    { toFun := β
      map_add' := β.hom.map_add
      map_smul' := by
        intro t x
        change β (t • x) = t • β x
        induction t using TensorProduct.inductionOn with
        | add t t' ht ht' =>
            simp only [add_smul, β.hom.map_add, ht, ht']
        | tmul a b =>
          have ht : a ⊗ₜ[R] b =
              Algebra.TensorProduct.includeLeft (S := R) a *
                Algebra.TensorProduct.includeRight (R := R) (A := A) b := by
            simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
              Algebra.TensorProduct.tmul_mul_tmul]
          rw [ht, mul_smul, mul_smul, hleft_apply, hright_apply] }
  refine ⟨δ, g, hδ, ?_⟩
  exact hβ

end RingTensorCohomology
