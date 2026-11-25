/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Scalar extension of an explicit mixed total tensor

The comparison is at the level of complexes, without derived-category or flatness assumptions.
Source: Stacks Project, Tag 06Y6, tensor associativity in the proof of derived change of rings.
(blueprint: new-lem-pc-mixed-total-tensor-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology
variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

private noncomputable def scalarCompIso :
    ModuleCat.extendScalars.{u,u,u} (algebraMap R A) ⋙
        ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq) ≅
      ModuleCat.extendScalars.{u,u,u} (algebraMap R Aq) := by
  have he : (algebraMap A Aq).comp (algebraMap R A) = algebraMap R Aq := by
    ext r
    exact (IsScalarTower.algebraMap_apply R A Aq r).symm
  exact (ModuleCat.extendScalarsComp (algebraMap R A) (algebraMap A Aq)).symm ≪≫
    eqToIso (by rw [he])

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def mixedModuleIso (M : ModuleCat.{u} A) (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap A Aq)).obj
        (((ModuleCat.mixedTensor (algebraMap R A)).obj M).obj N) ≅
      ((ModuleCat.mixedTensor (algebraMap R Aq)).obj
        ((ModuleCat.extendScalars (algebraMap A Aq)).obj M)).obj N :=
  (Functor.Monoidal.μIso (ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq)) M
    ((ModuleCat.extendScalars (algebraMap R A)).obj N)).symm ≪≫
      (tensorLeft ((ModuleCat.extendScalars (algebraMap A Aq)).obj M)).mapIso
        ((scalarCompIso R A Aq).app N)

omit [Algebra R Aq] in
private theorem scalarEqIso_tmul
    {f g : R →+* Aq} (h : f = g) (N : ModuleCat.{u} R) (y : N) :
    (eqToIso (congrArg (ModuleCat.extendScalars.{u,u,u}) h)).hom.app N
      ((1 : Aq) ⊗ₜ[R,f] y) = ((1 : Aq) ⊗ₜ[R,g] y) := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompIso_tmul (N : ModuleCat.{u} R) (y : N) :
    (scalarCompIso R A Aq).hom.app N
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] ((1 : A) ⊗ₜ[R,algebraMap R A] y)) =
      (1 : Aq) ⊗ₜ[R,algebraMap R Aq] y := by
  have hi : (ModuleCat.extendScalarsComp (algebraMap R A) (algebraMap A Aq)).inv.app N
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] ((1 : A) ⊗ₜ[R,algebraMap R A] y)) =
      (1 : Aq) ⊗ₜ[R,(algebraMap A Aq).comp (algebraMap R A)] y := by
    have hh := ModuleCat.extendScalarsComp_hom_app_one_tmul
      (algebraMap R A) (algebraMap A Aq) N y
    rw [← hh]
    exact Iso.hom_inv_id_apply
      ((ModuleCat.extendScalarsComp (algebraMap R A) (algebraMap A Aq)).app N) _
  dsimp only [scalarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [ModuleCat.comp_apply, hi]
  exact scalarEqIso_tmul R Aq
    (by ext r; exact (IsScalarTower.algebraMap_apply R A Aq r).symm) N y

private theorem mixedModuleIso_tmul (M : ModuleCat.{u} A) (N : ModuleCat.{u} R)
    (x : M) (y : N) :
    (mixedModuleIso R A Aq M N).hom
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) ⊗ₜ[Aq]
        ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y) := by
  dsimp only [mixedModuleIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv]
  rw [ModuleCat.comp_apply]
  change (((ModuleCat.extendScalars (algebraMap A Aq)).obj M) ◁
    (scalarCompIso R A Aq).hom.app N)
      (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (algebraMap A Aq)) M
        ((ModuleCat.extendScalars (algebraMap R A)).obj N)
          ((1 : Aq) ⊗ₜ[A,algebraMap A Aq]
            (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))) = _
  erw [ModuleCat.extendScalars_δ_tmul]
  change ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) ⊗ₜ[Aq]
    ((scalarCompIso R A Aq).hom.app N
      ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) = _
  rw [scalarCompIso_tmul]

private theorem mixedModuleIso_natural_left
    {M M' : ModuleCat.{u} A} (a : M ⟶ M') (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap A Aq)).map
        (((ModuleCat.mixedTensor (algebraMap R A)).map a).app N) ≫
      (mixedModuleIso R A Aq M' N).hom =
    (mixedModuleIso R A Aq M N).hom ≫
      ((ModuleCat.mixedTensor (algebraMap R Aq)).map
        ((ModuleCat.extendScalars (algebraMap A Aq)).map a)).app N := by
  let H := ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq)
  let E := ModuleCat.extendScalars.{u,u,u} (algebraMap R A)
  let E' := ModuleCat.extendScalars.{u,u,u} (algebraMap R Aq)
  let c := (scalarCompIso R A Aq).hom.app N
  change H.map (a ▷ E.obj N) ≫ Functor.OplaxMonoidal.δ H M' (E.obj N) ≫
      H.obj M' ◁ c =
    (Functor.OplaxMonoidal.δ H M (E.obj N) ≫ H.obj M ◁ c) ≫
      H.map a ▷ E'.obj N
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whisker_exchange]

private theorem mixedModuleIso_natural_right
    (M : ModuleCat.{u} A) {N N' : ModuleCat.{u} R} (a : N ⟶ N') :
    (ModuleCat.extendScalars (algebraMap A Aq)).map
        (((ModuleCat.mixedTensor (algebraMap R A)).obj M).map a) ≫
      (mixedModuleIso R A Aq M N').hom =
    (mixedModuleIso R A Aq M N).hom ≫
      ((ModuleCat.mixedTensor (algebraMap R Aq)).obj
        ((ModuleCat.extendScalars (algebraMap A Aq)).obj M)).map a := by
  let H := ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq)
  let E := ModuleCat.extendScalars.{u,u,u} (algebraMap R A)
  let E' := ModuleCat.extendScalars.{u,u,u} (algebraMap R Aq)
  let c := (scalarCompIso R A Aq).hom
  change H.map (M ◁ E.map a) ≫ Functor.OplaxMonoidal.δ H M (E.obj N') ≫
      H.obj M ◁ c.app N' =
    (Functor.OplaxMonoidal.δ H M (E.obj N) ≫ H.obj M ◁ c.app N) ≫
      H.obj M ◁ E'.map a
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  exact congrArg (fun z ↦ Functor.OplaxMonoidal.δ H M (E.obj N) ≫ H.obj M ◁ z)
    (c.naturality a)

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def mixedBicomplexIso
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars (algebraMap A Aq)).mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj
        (((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj Q |>.obj F) ≅
      (((ModuleCat.mixedTensor (algebraMap R Aq)).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj ((extend A Aq).obj Q)).obj F := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦
    HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ mixedModuleIso R A Aq (Q.X p) (F.X q)) ?_) ?_
  · intro q q' h
    exact (mixedModuleIso_natural_right R A Aq (Q.X p) (F.d q q')).symm
  · intro p p' h
    apply HomologicalComplex.Hom.ext
    funext q
    exact (mixedModuleIso_natural_left R A Aq (Q.d p p') (F.X q)).symm

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def mixedTotalIso
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extend A Aq).obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ≅
      ((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj ((extend A Aq).obj Q)).obj F := by
  let H := ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq)
  letI : H.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).left_adjoint_additive
  let S := (((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj Q).obj F
  exact (HomologicalComplex₂.mapTotalIso H S (.up ℤ)).symm ≪≫
    HomologicalComplex₂.total.mapIso (mixedBicomplexIso R A Aq Q F) (.up ℤ)

set_option backward.isDefEq.respectTransparency.types false in
private theorem mixedTotalIso_ι
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    (ModuleCat.extendScalars (algebraMap A Aq)).map
      (HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h) ≫
      (mixedTotalIso R A Aq Q F).hom.f n =
    (mixedModuleIso R A Aq (Q.X p) (F.X q)).hom ≫
      HomologicalComplex.ιMapBifunctor ((extend A Aq).obj Q) F
        (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h := by
  let H := ModuleCat.extendScalars.{u,u,u} (algebraMap A Aq)
  let : H.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).left_adjoint_additive
  let S := (((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj Q).obj F
  change H.map (S.ιTotal (.up ℤ) p q n h) ≫
    (HomologicalComplex₂.mapTotalXIso H S (.up ℤ) n).inv ≫
      (HomologicalComplex₂.total.map (mixedBicomplexIso R A Aq Q F).hom (.up ℤ)).f n = _
  rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc, HomologicalComplex₂.ιTotal_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem mixedTotalIso_formula
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q) :
    (mixedTotalIso R A Aq Q F).hom.f n ((1 : Aq) ⊗ₜ[A,algebraMap A Aq]
      ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))) =
    (HomologicalComplex.ιMapBifunctor ((extend A Aq).obj Q) F
      (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
        (((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) ⊗ₜ[Aq]
          ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y)) := by
  have hi := ConcreteCategory.congr_hom (mixedTotalIso_ι R A Aq Q F p q n h)
    ((1 : Aq) ⊗ₜ[A,algebraMap A Aq]
      (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))
  simp only [ModuleCat.comp_apply] at hi
  erw [ModuleCat.ExtendScalars.map_tmul, mixedModuleIso_tmul] at hi
  exact hi


/-- Scalar extension commutes with the mixed total tensor, with its pure-tensor formula.
Source: Stacks Project, Tag 06Y6, the total-tensor identifications in its proof.
(blueprint: new-lem-pc-mixed-total-tensor-scalar-extension).

Proof: in bidegree (p,q), the source is Aq tensor_A
(Q^p tensor_A (A tensor_R F^q)). Reassociate tensors, extend the second factor
A tensor_R F^q along A -> Aq, and identify its extension with Aq tensor_R F^q.
The resulting Aq-linear isomorphism sends a tensor (x tensor (b tensor y)) to
(a tensor x) tensor (algebraMap A Aq b tensor y). Its inverse sends
(a tensor x) tensor (c tensor y) to ac tensor (x tensor (1 tensor y)).
The balancing relations show that both maps are well-defined and mutually inverse.
They commute with each of the two differentials by their pure-tensor formulas;
the sign (-1)^p is unchanged. Extension of scalars preserves coproducts because
it is a left adjoint. Thus the bidegree isomorphisms assemble on each diagonal
into an isomorphism of total complexes. The specified formula follows by taking
a=b=c=1. No exactness of Aq tensor_A - is used, so nonflat and zero rings are allowed. -/
theorem exists_mixedTotalTensor_scalarExtension
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ θ : (extend A Aq).obj
        (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ≅
      ((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj ((extend A Aq).obj Q)).obj F,
    ∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
      θ.hom.f n ((1 : Aq) ⊗ₜ[A,algebraMap A Aq]
        ((HomologicalComplex.ιMapBifunctor Q F
          (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
            (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))) =
      (HomologicalComplex.ιMapBifunctor ((extend A Aq).obj Q) F
        (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
          (((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) ⊗ₜ[Aq]
            ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y)) := by
  refine ⟨mixedTotalIso R A Aq Q F, ?_⟩
  intro p q n h x y
  exact mixedTotalIso_formula R A Aq Q F p q n h x y

end RingTensorCohomology
