/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Local equational criterion with independent universes

Source: Stacks Project, Modules on Sites, Tag 08FC.
The converse is proved by local finite matrix elimination and tensor vanishing.
-/

@[expose] public section

universe uC vC r m w u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

open Function Submodule

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

private noncomputable def linearTensorRight {A : Type r} [CommRing A] (N : ModuleCat.{w} A) :
    ModuleCat.{w} A ⥤ ModuleCat.{w} A where
  obj M := ModuleCat.of A (M ⊗[A] N)
  map f := ModuleCat.ofHom (TensorProduct.map f.hom LinearMap.id)
  map_id M := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    rfl

private noncomputable def linearHomRight {A : Type r} [CommRing A] (N : ModuleCat.{w} A) :
    ModuleCat.{w} A ⥤ ModuleCat.{w} A where
  obj Q := ModuleCat.of A (N →ₗ[A] Q)
  map f := ModuleCat.ofHom
    { toFun := fun g ↦ f.hom.comp g
      map_add' := by intro a b; ext n; exact map_add f.hom (a n) (b n)
      map_smul' := by intro a b; ext n; exact map_smul f.hom a (b n) }
  map_id Q := by ext g n; rfl
  map_comp f g := by ext h n; rfl

private noncomputable def linearTensorAdjunction {A : Type r} [CommRing A]
    (N : ModuleCat.{w} A) : linearTensorRight N ⊣ linearHomRight N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M Q ↦
        { toFun := fun f ↦ ModuleCat.ofHom (TensorProduct.curry f.hom)
          invFun := fun f ↦ ModuleCat.ofHom (TensorProduct.lift f.hom)
          left_inv := by
            intro f
            apply ModuleCat.hom_ext
            apply TensorProduct.ext'
            intro m n
            rfl
          right_inv := by intro f; ext m n; rfl }
      homEquiv_naturality_left_symm := by
        intro M M' Q f g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m n
        rfl
      homEquiv_naturality_right := by intro M Q Q' f g; ext m; rfl }

private noncomputable instance {A : Type r} [CommRing A] (N : ModuleCat.{w} A) :
    (linearTensorRight N).IsLeftAdjoint := (linearTensorAdjunction N).isLeftAdjoint

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

private noncomputable def tensorEvaluationIso
    (N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    siteTensorRight N ⋙ PresheafOfModules.evaluation _ U ≅
      PresheafOfModules.evaluation _ U ⋙ linearTensorRight (N.obj U) :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    rfl)

private theorem siteTensorRight_preservesColimitsOfShape
    (N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (K : Type*) [Category* K] [HasColimitsOfShape K AddCommGrpCat.{w}] :
    PreservesColimitsOfShape K (siteTensorRight N) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply PresheafOfModules.evaluationJointlyReflectsColimits
    intro U
    have : PreservesColimit F (siteTensorRight N ⋙ PresheafOfModules.evaluation _ U) :=
      preservesColimit_of_natIso F (tensorEvaluationIso N U).symm
    exact isColimitOfPreserves (siteTensorRight N ⋙ PresheafOfModules.evaluation _ U)
      (colimit.isColimit F)

section Sheaves

variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (A : Sheaf J CommRingCat.{r})

private noncomputable abbrev associated := PresheafOfModules.sheafification.{w}
  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)

private noncomputable def associatedUnit
    (P : PresheafOfModules.{w} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((associated A).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.app P

private instance associatedUnit_locallyInjective
    (P : PresheafOfModules.{w} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (associatedUnit A P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private instance associatedUnit_locallySurjective
    (P : PresheafOfModules.{w} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (associatedUnit A P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private noncomputable def tensorAssociatedMap
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    siteTensorRight M.val ⋙ associated A ⟶ associated A ⋙ siteSheafTensorRight M where
  app P := (associated A).map (siteTensorHom (associatedUnit A P) M.val)
  naturality {P Q} f := by
    change (associated A).map (siteTensorHom f M.val) ≫
      (associated A).map (siteTensorHom (associatedUnit A Q) M.val) =
      (associated A).map (siteTensorHom (associatedUnit A P) M.val) ≫
      (associated A).map (siteTensorHom ((associated A).map f).val M.val)
    rw [← Functor.map_comp, ← Functor.map_comp,
      ← siteTensorHom_comp, ← siteTensorHom_comp]
    congr 2
    exact (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.naturality f

private instance tensorAssociatedMap_isIso
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    IsIso (tensorAssociatedMap A M) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  have := associatedUnit_locallyInjective A P
  have := associatedUnit_locallySurjective A P
  exact PresheafOfModules.sheafification_tensorHom_isIso (R := A.obj) (J := J)
    (f := associatedUnit A P)
    (N := M.val) ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).property

private theorem siteSheafTensorRight_preservesFiniteColimits
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    PreservesFiniteColimits (siteSheafTensorRight M) where
  preservesFiniteColimits K _ _ := by
    have : PreservesColimitsOfShape K (siteTensorRight M.val) :=
      siteTensorRight_preservesColimitsOfShape M.val K
    have := tensorAssociatedMap_isIso A M
    have : PreservesColimitsOfShape K (associated A ⋙ siteSheafTensorRight M) :=
      preservesColimitsOfShape_of_natIso (asIso (tensorAssociatedMap A M))
    constructor
    intro F
    let G := F ⋙ (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _))
    let adj := PresheafOfModules.sheafificationAdjunction.{w}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    let e : G ⋙ associated A ≅ F :=
      Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
    have : PreservesColimit (G ⋙ associated A) (siteSheafTensorRight M) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (associated A) (colimit.isColimit G))
        (isColimitOfPreserves (associated A ⋙ siteSheafTensorRight M) (colimit.isColimit G))
    exact preservesColimit_of_iso_diagram (siteSheafTensorRight M) e

end Sheaves

end SheafOfModules

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}
  (M : SheafOfModules.{m}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))

private def RowCriterion : Prop :=
  ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U)) (s : Fin n → M.val.obj (op U)),
    (∑ i, a i • s i) = 0 →
    ∃ S : Sieve U, S ∈ J U ∧ ∀ V (f : V ⟶ U), S f →
      ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
        (t : Fin l → M.val.obj (op V)),
        (∀ i, M.val.map f.op (s i) = ∑ j, b i j • t j) ∧
        (∀ j, ∑ i, R.obj.map f.op (a i) * b i j = 0)

private def matrixSieve {U : C} {n q : ℕ}
    (a : Fin q → Fin n → R.obj.obj (op U)) (s : Fin n → M.val.obj (op U)) : Sieve U where
  arrows V f := ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
      (t : Fin l → M.val.obj (op V)),
      (∀ i, M.val.map f.op (s i) = ∑ j, b i j • t j) ∧
      (∀ k j, ∑ i, R.obj.map f.op (a k i) * b i j = 0)
  downward_closed := by
    rintro V W f ⟨l, b, t, hs, ha⟩ g
    refine ⟨l, (fun i j ↦ R.obj.map g.op (b i j)),
      (fun j ↦ M.val.map g.op (t j)), ?_, ?_⟩
    · intro i
      simp only [op_comp, M.val.map_comp_apply, hs, map_sum, M.val.map_smul]
      rfl
    · intro k j
      simp only [op_comp, Functor.map_comp_apply, ← map_mul, ← map_sum, ha, map_zero]

private theorem matrixSieve_mem (hM : RowCriterion M) {q : ℕ} (U : C) (n : ℕ)
    (a : Fin q → Fin n → R.obj.obj (op U)) (s : Fin n → M.val.obj (op U))
    (heq : ∀ k, (∑ i, a k i • s i) = 0) : matrixSieve M a s ∈ J U := by
  classical
  induction q generalizing U n with
  | zero =>
    have htop : matrixSieve M a s = ⊤ := by
      apply top_unique
      intro V f _
      refine ⟨n, (fun i j ↦ if i = j then 1 else 0),
        (fun i ↦ M.val.map f.op (s i)), ?_, ?_⟩
      · intro i
        simp
      · intro k
        exact Fin.elim0 k
    rw [htop]
    exact J.top_mem _
  | succ q ih =>
    obtain ⟨S, hS, hfac⟩ := hM U n (a 0) s (heq 0)
    apply J.transitive hS
    intro V f hf
    obtain ⟨l, b, t, hs, hb⟩ := hfac V f hf
    let a' (k : Fin q) (j : Fin l) : R.obj.obj (op V) :=
      ∑ i, R.obj.map f.op (a k.succ i) * b i j
    have heq' (k : Fin q) : ∑ j, a' k j • t j = 0 := by
      calc
        _ = ∑ i, R.obj.map f.op (a k.succ i) • ∑ j, b i j • t j := by
          simp only [a', Finset.sum_smul, mul_smul, Finset.smul_sum]
          exact Finset.sum_comm
        _ = ∑ i, R.obj.map f.op (a k.succ i) • M.val.restrictₛₗ f.op (s i) := by
          simp only [PresheafOfModules.restrictₛₗ_apply, hs]
        _ = 0 := by
          have h := congrArg (fun z : M.val.obj (op U) ↦ M.val.map f.op z) (heq k.succ)
          simp only [map_sum, M.val.map_smul, map_zero] at h
          exact h
    apply J.superset_covering _ (ih V l a' t heq')
    rintro W g ⟨l', c, v, ht, hc⟩
    refine ⟨l', (fun i k ↦ ∑ j, R.obj.map g.op (b i j) * c j k), v, ?_, ?_⟩
    · intro i
      simp only [op_comp, M.val.map_comp_apply, hs, map_sum, M.val.map_smul, ht]
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    · intro k z
      change ∑ i, R.obj.map (g ≫ f).op (a k i) *
        (∑ j, R.obj.map g.op (b i j) * c j z) = 0
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · calc
          _ = ∑ j, R.obj.map g.op (∑ i, R.obj.map f.op (a 0 i) * b i j) * c j z := by
            simp only [op_comp, Functor.map_comp_apply, map_sum, map_mul,
              Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
          _ = 0 := by simp only [hb, map_zero, zero_mul, Finset.sum_const_zero]
      · calc
          _ = ∑ j, R.obj.map g.op (a' k j) * c j z := by
            simp only [a', op_comp, Functor.map_comp_apply, map_sum, map_mul,
              Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
          _ = 0 := hc k z

private theorem tensor_equalizerSieve_mem (hM : RowCriterion M)
    {P N : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (g : P ⟶ N) (hg : ∀ U, Function.Injective (g.app U))
    (U : C) (t : (siteTensorPresheaf P M.val).obj (op U))
    (ht : (siteTensorHom g M.val).app (op U) t = 0) :
    Presheaf.equalizerSieve (F := (siteTensorPresheaf P M.val).presheaf) t 0 ∈ J U := by
  classical
  obtain ⟨n, p, m, htm⟩ := TensorProduct.exists_sum_tmul_eq
    (t : TensorProduct (R.obj.obj (op U)) (P.obj (op U)) (M.val.obj (op U)))
  have ht₀ : ∑ k, m k ⊗ₜ[R.obj.obj (op U)] g.app (op U) (p k) = 0 := by
    let g' : P.obj (op U) →ₗ[R.obj.obj (op U)] N.obj (op U) := (g.app (op U)).hom
    have h : (TensorProduct.map g' (LinearMap.id (R := R.obj.obj (op U)))) t = 0 := ht
    rw [htm] at h
    have h' := congrArg (TensorProduct.comm (R.obj.obj (op U)) _ _) h
    simpa only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.comm_tmul, map_zero] using h'
  obtain ⟨s, q, y, a, e, z, hma, hey, hcoeff⟩ :=
    TensorProduct.exists_relations_with_coefficients m
      (fun k ↦ g.app (op U) (p k)) ht₀
  let p' (j : Fin s) : P.obj (op U) := ∑ k, a k j • p k
  have ht' : (t : TensorProduct (R.obj.obj (op U)) (P.obj (op U))
      (M.val.obj (op U))) = ∑ j, p' j ⊗ₜ[R.obj.obj (op U)] y j := by
    rw [htm]
    simp only [hma, p', TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul]
    exact Finset.sum_comm
  have hkill (V : C) (f : V ⟶ U) (c : Fin s → R.obj.obj (op V))
      (hc : ∀ l, ∑ j, R.obj.map f.op (e l j) * c j = 0) :
      ∑ j, c j • P.restrictₛₗ f.op (p' j) = 0 := by
    simp only [PresheafOfModules.restrictₛₗ_apply]
    apply hg (op V)
    rw [map_sum, map_zero]
    have hcomponent (j : Fin s) :
        g.app (op V) (P.map f.op (p' j)) =
          -∑ l, R.obj.map f.op (e l j) • N.restrictₛₗ f.op (z l) := by
      simp only [PresheafOfModules.restrictₛₗ_apply]
      have h := congrArg (fun x : N.obj (op U) ↦ N.map f.op x) (hcoeff j)
      simp only [map_add, map_sum, N.map_smul, map_zero] at h
      apply eq_neg_of_add_eq_zero_left
      change (∑ k, R.obj.map f.op (a k j) • N.restrictₛₗ f.op (g.app (op U) (p k))) +
        (∑ l, R.obj.map f.op (e l j) • N.restrictₛₗ f.op (z l)) = 0 at h
      rw [PresheafOfModules.naturality_apply]
      dsimp only [p']
      rw [map_sum, map_sum]
      simp only [map_smul]
      exact h
    simp only [map_smul, hcomponent, PresheafOfModules.restrictₛₗ_apply, smul_neg,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hc' (l : Fin q) : ∑ j, c j * R.obj.map f.op (e l j) = 0 := by
      simpa only [mul_comm] using hc l
    simp only [hc', zero_smul, Finset.sum_const_zero, neg_zero]
  apply J.superset_covering _ (matrixSieve_mem M hM U s e y hey)
  rintro V f ⟨l, b, v, hfac, hzero⟩
  change (siteTensorPresheaf P M.val).map f.op t =
    (siteTensorPresheaf P M.val).map f.op 0
  rw [map_zero]
  let ρP : P.obj (op U) →ₛₗ[(R.obj.map f.op).hom] P.obj (op V) := P.restrictₛₗ f.op
  let ρM : M.val.obj (op U) →ₛₗ[(R.obj.map f.op).hom] M.val.obj (op V) :=
    M.val.restrictₛₗ f.op
  change TensorProduct.map ρP ρM t = 0
  rw [ht']
  simp only [map_sum, TensorProduct.map_tmul]
  change (∑ j, P.restrictₛₗ f.op (p' j) ⊗ₜ[R.obj.obj (op V)]
    M.val.restrictₛₗ f.op (y j)) = 0
  simp_rw [PresheafOfModules.restrictₛₗ_apply, hfac, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  change (∑ k, ∑ j, (b j k • (@id (P.obj (op V)) (P.map f.op (p' j))))
    ⊗ₜ[R.obj.obj (op V)] v k) = 0
  simp_rw [← TensorProduct.sum_tmul]
  apply Finset.sum_eq_zero
  intro k _
  have hk : (∑ j, b j k • (@id (P.obj (op V)) (P.map f.op (p' j)))) = 0 :=
    hkill V f (fun j ↦ b j k) (fun l ↦ hzero l k)
  exact (congrArg (fun z : P.obj (op V) ↦ z ⊗ₜ[R.obj.obj (op V)] v k) hk).trans
    (TensorProduct.zero_tmul _ _)

private theorem tensor_locallyInjective (hM : RowCriterion M)
    {P N : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)}
    (g : P ⟶ N) (hg : ∀ U, Function.Injective (g.app U)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (siteTensorHom g M.val)) where
  equalizerSieve_mem {U} x y hxy := by
    have h := tensor_equalizerSieve_mem M hM g hg U.unop (x - y)
      (by change (siteTensorHom g M.val).app U (x - y) = 0
          rw [map_sub]; exact sub_eq_zero.mpr hxy)
    apply J.superset_covering _ h
    intro V f hf
    change (siteTensorPresheaf P M.val).map f.op (x - y) =
      (siteTensorPresheaf P M.val).map f.op 0 at hf
    change (siteTensorPresheaf P M.val).map f.op x =
      (siteTensorPresheaf P M.val).map f.op y
    simpa only [map_sub, map_zero, sub_eq_zero] using hf

private theorem tensorSheaf_mono
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}]
    (hM : RowCriterion M)
    {P N : SheafOfModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : P ⟶ N) [Mono g] : Mono ((siteSheafTensorRight M).map g) := by
  have : Mono g.val := (SheafOfModules.forget _).map_mono g
  have hi := tensor_locallyInjective M hM g.val
    (fun U ↦ PresheafOfModules.injective_of_mono g.val U)
  have : Sheaf.IsLocallyInjective ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf _).map (siteTensorHom g.val M.val))) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).mpr hi
  have : Mono ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf _).map (siteTensorHom g.val M.val))) :=
    Sheaf.mono_of_isLocallyInjective _
  exact (toSheaf _).mono_of_mono_map (by exact this)

end SheafOfModules

namespace SheafOfModules

/-- The local relation criterion implies flatness with an independent module universe.
Source: Stacks Project, Modules on Sites, Tag 08FC, (2) implies (1)
(auxiliary; not a blueprint node).
Proof: the finite-matrix argument below factors the coefficients of any tensor
killed by a monomorphism. It makes this tensor locally zero, so tensoring
preserves monomorphisms. The tensor functor preserves finite colimits by its
sectionwise adjunction and module sheafification. In the abelian category of
module sheaves, these two properties imply exactness. No free module on the
coefficient ring is needed for this direction. -/
theorem isFlatOnSite_of_local_equationalCriterion
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hM : ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, R.obj.map f.op (a p) * b p q) = 0)) :
    IsFlatOnSite M := by
  have := CategoryTheory.hasSheafify_addCommGrp_of_weak.{uC, vC, m} J
  have hright := siteSheafTensorRight_preservesFiniteColimits R M
  have : (siteSheafTensorRight M).Additive :=
    (CategoryTheory.rightExactFunctor_le_additiveFunctor _ _) _ hright
  have : (siteSheafTensorRight M).PreservesMonomorphisms :=
    ⟨fun g _ ↦ tensorSheaf_mono M hM g⟩
  refine ⟨?_, hright⟩
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (siteSheafTensorRight M)).mpr
  intro S hS
  have := hS.mono_f
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, inferInstance⟩

/-- Flatness is equivalent to local finite relation factorization on a ringed site.
Source: Stacks Project, Modules on Sites, Tag 08FC, (1) iff (2)
(auxiliary; not a blueprint node).

Proof: The forward direction is the local relation theorem. For the converse,
induct on the rows of a finite relation matrix, applying the one-row condition
and composing its local factorization matrices on covering refinements.
For a tensor killed by an injective module-presheaf map, choose finite coefficient
identities witnessing its vanishing in the target. The matrix condition factors
its module entries locally so that every auxiliary relation vanishes columnwise.
Injectivity then makes each first-factor column zero, and the tensor is locally
zero. Sheafification turns this into preservation of monomorphisms by tensor.

Sectionwise tensor preserves colimits by the tensor–linear-Hom adjunction and
joint reflection of colimits by evaluation. The natural isomorphism between
associated presheaf tensor and tensor of associated sheaves transfers finite
colimit preservation to module sheaves. Existing weak abelian sheafification is
left exact under the stated local-bijectivity hypothesis, so module sheaves form
an abelian category. Right exactness and preservation of monomorphisms make the
tensor functor exact. All refinements use covering sieves; the site universes
are unrestricted and empty relations are included. -/
theorem isFlatOnSite_iff_local_equationalCriterion
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    IsFlatOnSite M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, R.obj.map f.op (a p) * b p q) = 0) := by
  have := CategoryTheory.hasSheafify_addCommGrp_of_weak.{uC, vC, max r m} J
  constructor
  · intro hM
    exact local_equationalCriterion_of_isFlatOnSite R M hM
  · intro hM
    have hright := siteSheafTensorRight_preservesFiniteColimits R M
    have : (siteSheafTensorRight M).Additive :=
      (CategoryTheory.rightExactFunctor_le_additiveFunctor _ _) _ hright
    have : (siteSheafTensorRight M).PreservesMonomorphisms :=
      ⟨fun g _ ↦ tensorSheaf_mono M hM g⟩
    refine ⟨?_, hright⟩
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (siteSheafTensorRight M)).mpr
    intro S hS
    have := hS.mono_f
    exact ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, inferInstance⟩

end SheafOfModules
