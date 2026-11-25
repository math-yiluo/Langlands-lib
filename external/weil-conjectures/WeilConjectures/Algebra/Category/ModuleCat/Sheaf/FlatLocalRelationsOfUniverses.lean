/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Local relations of a flat module sheaf in independent universes

Source: Stacks Project, Modules on Sites, Tag 08FC, and Algebra, Tag 04VX.
The proof uses free presheaves on coefficient tuples instead of site hom-sets.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false

open Function Submodule

namespace TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- A finite tensor relation has coefficient identities that remain valid after
arbitrary scalar restriction. Source: the proof of the finite tensor vanishing
criterion, Stacks Project, Algebra, Tag 04VX
(auxiliary; not a blueprint node).

Proof: Commute the vanishing tensor sum and place its second factors in their
finitely generated span. Tensor vanishing holds in a larger finitely generated
submodule. Generate that submodule by the original factors together with a finite
extra family. Apply the finite spanning-family tensor criterion, giving zero
coefficients for the extra entries on the first side. The original entries give
the factorization of `m`, the extra entries give the auxiliary zero relations,
and projection of the coefficient equations gives the final identities. -/
theorem exists_relations_with_coefficients {n : ℕ} (m : Fin n → M) (g : Fin n → N)
    (h : ∑ k, m k ⊗ₜ[R] g k = 0) :
    ∃ (s q : ℕ) (y : Fin s → M) (a : Fin n → Fin s → R)
      (e : Fin q → Fin s → R) (z : Fin q → N),
      (∀ k, m k = ∑ j, a k j • y j) ∧
      (∀ l, ∑ j, e l j • y j = 0) ∧
      (∀ j, (∑ k, a k j • g k) + ∑ l, e l j • z l = 0) := by
  classical
  -- the vanishing already happens in `Q ⊗ M` for a finitely generated `Q ⊆ N` containing `g`
  let P : Submodule R N := span R (Set.range g)
  have hP : P.FG := fg_span (Set.finite_range g)
  let t : P ⊗[R] M := ∑ k, (⟨g k, subset_span ⟨k, rfl⟩⟩ : P) ⊗ₜ m k
  have ht : LinearMap.rTensor M P.subtype t = 0 := by
    simp only [t, map_sum, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    simpa using congrArg (TensorProduct.comm R M N) h
  obtain ⟨Q, hPQ, ⟨S, hS⟩, hQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hP ht
  -- a spanning family of `Q`: the `gₖ` followed by the generators of `Q`
  let p := S.card
  let gen : Fin p → Q := fun l ↦ ⟨(S.equivFin.symm l : N), by
    rw [← hS]; exact subset_span (S.equivFin.symm l).2⟩
  let gg : Fin n ⊕ Fin p → Q := Sum.elim (fun k ↦ inclusion hPQ ⟨g k, subset_span ⟨k, rfl⟩⟩) gen
  let mm : Fin n ⊕ Fin p → M := Sum.elim m 0
  have hspan : span R (Set.range gg) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ span R (S : Set N) := by rwa [hS]
    have key : span R (S : Set N) ≤ (span R (Set.range gg)).map Q.subtype := by
      rw [span_le]
      intro z hz
      refine ⟨⟨z, by rw [← hS]; exact subset_span hz⟩, subset_span
        ⟨Sum.inr (S.equivFin ⟨z, hz⟩), ?_⟩, rfl⟩
      simp [gg, gen]
    obtain ⟨w, hw, hwx⟩ := key hx'
    have : w = ⟨x, hx⟩ := Subtype.ext hwx
    rwa [← this]
  have hsum : ∑ i, gg i ⊗ₜ[R] mm i = (0 : Q ⊗[R] M) := by
    rw [Fintype.sum_sum_type]
    simp only [gg, mm, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, tmul_zero,
      Finset.sum_const_zero, add_zero]
    rw [← hQ]
    simp [t, map_sum]
  obtain ⟨s, c, y, hmy, hcg⟩ := vanishesTrivially_of_sum_tmul_eq_zero R hspan hsum
  refine ⟨s, p, y, fun k j ↦ c (Sum.inl k) j, fun l j ↦ c (Sum.inr l) j,
    fun l ↦ (gen l : N), fun k ↦ hmy (Sum.inl k),
    fun l ↦ by simpa [mm] using (hmy (Sum.inr l)).symm, ?_⟩
  intro j
  have hc := congrArg (fun x : Q ↦ (x : N)) (hcg j)
  simpa [gg, Fintype.sum_sum_type] using hc

end TensorProduct

namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C]
variable (R : Cᵒᵖ ⥤ CommRingCat.{r}) (n : ℕ)
private abbrev Labels (X : Cᵒᵖ) := ULift.{m} (Fin n → R.obj X)
private noncomputable def coeffMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (Labels.{uC,vC,r,m} R n X →₀ R.obj X) →ₛₗ[(R.map f).hom]
      (Labels.{uC,vC,r,m} R n Y →₀ R.obj Y) :=
  (Finsupp.lmapDomain (R.obj Y) (R.obj Y)
    (fun a : Labels R n X ↦ (⟨fun i ↦ R.map f (a.down i)⟩ : Labels R n Y))).comp
    (Finsupp.mapRange.linearMap (R.map f).hom.toSemilinearMap)
private noncomputable def coeffPresheaf :
    PresheafOfModules.{max r m} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (Labels R n X →₀ R.obj X)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _ (coeffMap R n f)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change coeffMap R n (𝟙 X) x = x
    simp only [coeffMap, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapRange.linearMap_apply, RingHom.coe_toSemilinearMap, R.map_id]
    change Finsupp.mapDomain id (Finsupp.mapRange id rfl x) = x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change coeffMap R n (f ≫ g) x = coeffMap R n g (coeffMap R n f x)
    induction x using Finsupp.induction with
    | zero => simp
    | @single_add a c x _ _ ih =>
      rw [map_add, map_add, map_add, ih]
      congr 1
      simp [coeffMap, Finsupp.lmapDomain_apply, Finsupp.mapRange.linearMap_apply]

private noncomputable def coeffIdeal : (coeffPresheaf R n).Submodule where
  obj X := Submodule.span (R.obj X) (Set.range
    (fun p : Labels R n X × Fin n ↦ Finsupp.single p.1 (p.1.down p.2)))
  map {X Y} f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, i⟩, rfl⟩
    change coeffMap R n f (Finsupp.single a (a.down i)) ∈
      Submodule.span (R.obj Y) (Set.range
        (fun p : Labels R n Y × Fin n ↦ Finsupp.single p.1 (p.1.down p.2)))
    have h := Submodule.subset_span (R := R.obj Y) (s := Set.range
      (fun p : Labels R n Y × Fin n ↦ Finsupp.single p.1 (p.1.down p.2)))
      ⟨(⟨fun j ↦ R.map f (a.down j)⟩, i), rfl⟩
    have heq : coeffMap R n f (Finsupp.single a (a.down i)) =
        Finsupp.single (⟨fun j ↦ R.map f (a.down j)⟩ : Labels R n Y)
          (R.map f (a.down i)) := by
      simp only [coeffMap, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl
    exact heq ▸ h

private theorem coeffIdeal_coordinate (X : Cᵒᵖ) (a : Labels R n X)
    (x : (coeffIdeal R n).obj X) :
    ∃ d : Fin n → R.obj X, (@id (Labels R n X →₀ R.obj X) x.val) a =
      ∑ i, d i * a.down i := by
  have hxcoord : (@id (Labels R n X →₀ R.obj X) x.val) a ∈
      Submodule.span (R.obj X) (Set.range a.down) := by
    have hx := x.property
    change (@id (Labels R n X →₀ R.obj X) x.val) ∈ Submodule.span (R.obj X) _ at hx
    generalize hz : (@id (Labels R n X →₀ R.obj X) x.val) = z at hx ⊢
    clear hz
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a', i⟩, rfl⟩ := hx
      classical
      by_cases h : a' = a
      · subst a'
        simp only [Finsupp.single_eq_same]
        exact Submodule.subset_span (R := R.obj X) (s := Set.range a.down) ⟨i, rfl⟩
      · simp [h]
    | zero => exact Submodule.zero_mem _
    | add x y hx hy hi hj => simpa using Submodule.add_mem _ hi hj
    | smul c x hx hi => simpa using Submodule.smul_mem _ c hi
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R.obj X)).mp hxcoord
  exact ⟨d, hd.symm⟩

private noncomputable def coeffGenerator (X : Cᵒᵖ) (a : Labels R n X) (i : Fin n) :
    (coeffIdeal R n).toPresheafOfModules.obj X :=
  ⟨Finsupp.single a (a.down i), Submodule.subset_span ⟨(a, i), rfl⟩⟩

private theorem coeff_tensor_vanish (X : Cᵒᵖ) (a : Labels R n X)
    {N : Type*} [AddCommGroup N] [Module (R.obj X) N] (s : Fin n → N)
    (h : ∑ i, coeffGenerator R n X a i ⊗ₜ[R.obj X] s i = 0) :
    ∃ (l : ℕ) (b : Fin n → Fin l → R.obj X) (t : Fin l → N),
      (∀ i, s i = ∑ j, b i j • t j) ∧
      (∀ j, ∑ i, a.down i * b i j = 0) := by
  classical
  have h' : ∑ i, s i ⊗ₜ[R.obj X] coeffGenerator R n X a i = 0 := by
    simpa only [map_sum, TensorProduct.comm_tmul, map_zero] using
      congrArg (TensorProduct.comm (R.obj X) _ _) h
  obtain ⟨l, q, y, c, e, z, hc, he, hz⟩ :=
    TensorProduct.exists_relations_with_coefficients s _ h'
  choose d hd using fun k ↦ coeffIdeal_coordinate R n X a (z k)
  refine ⟨l, fun i j ↦ c i j + ∑ k, d k i * e k j, y, ?_, ?_⟩
  · intro i
    rw [hc i]
    simp_rw [add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [mul_smul, ← Finset.smul_sum, he, smul_zero, Finset.sum_const_zero, add_zero]
  · intro j
    have hh' := congrArg ((coeffIdeal R n).obj X).subtype (hz j)
    simp only [map_add, map_sum, map_smul, map_zero] at hh'
    have hh := congrArg (fun x : Labels R n X →₀ R.obj X ↦ x a) hh'
    change (∑ i, c i j • Finsupp.single a (a.down i) +
      ∑ k, e k j • (@id (Labels R n X →₀ R.obj X) (z k).val)) a = 0 at hh
    simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, hd] at hh
    rw [← hh]
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

section Sheaves
variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  (A : Sheaf J CommRingCat.{r})

private noncomputable abbrev associated := PresheafOfModules.sheafification.{max r m}
  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)

private noncomputable def associatedUnit
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((associated A).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.app P

private instance associatedUnit_locallyInjective
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (associatedUnit A P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private instance associatedUnit_locallySurjective
    (P : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (associatedUnit A P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private noncomputable def tensorAssociatedMap
    (M : SheafOfModules.{max r m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    siteTensorRight M.val ⋙ associated A ⟶ associated A ⋙ siteSheafTensorRight M where
  app P := (associated A).map (siteTensorHom (associatedUnit A P) M.val)
  naturality {P Q} f := by
    dsimp only [Functor.comp_map, siteTensorRight, siteSheafTensorRight,
      SheafOfModules.forget]
    rw [← Functor.map_comp, ← Functor.map_comp,
      ← siteTensorHom_comp, ← siteTensorHom_comp]
    congr 2
    exact (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.naturality f

private instance tensorAssociatedMap_isIso
    (M : SheafOfModules.{max r m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    IsIso (tensorAssociatedMap A M) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  have := associatedUnit_locallyInjective A P
  have := associatedUnit_locallySurjective A P
  exact PresheafOfModules.sheafification_tensorHom_isIso (R := A.obj) (J := J)
    (f := associatedUnit A P)
    (N := M.val) ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).property


private theorem tensor_mono_locallyInjective
    (M : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) (hM : IsFlatOnSite M)
    {P Q : PresheafOfModules.{max r m} (A.obj ⋙ forget₂ CommRingCat RingCat)}
    (f : P ⟶ Q) [Mono f] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (siteTensorHom f M.val)) := by
  have := CategoryTheory.hasSheafify_addCommGrp_of_weak.{uC, vC, max r m} J
  have : PreservesFiniteLimits (siteSheafTensorRight M) := hM.1
  have := tensorAssociatedMap_isIso A M
  have hf : Mono ((associated A).map (siteTensorHom f M.val)) := by
    have hnat := (tensorAssociatedMap A M).naturality f
    change (associated A).map (siteTensorHom f M.val) ≫
      (tensorAssociatedMap A M).app Q =
      (tensorAssociatedMap A M).app P ≫
        (siteSheafTensorRight M).map ((associated A).map f) at hnat
    have : Mono ((associated A).map (siteTensorHom f M.val) ≫
        (tensorAssociatedMap A M).app Q) := by
      rw [hnat]
      infer_instance
    exact mono_of_mono _ ((tensorAssociatedMap A M).app Q)
  have : Mono ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf _).map (siteTensorHom f M.val))) :=
    preserves_mono_of_preservesLimit (toSheaf _)
      ((associated A).map (siteTensorHom f M.val))
  apply (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).mp
  apply Presheaf.isLocallyInjective_of_injective
  intro U
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

private theorem flat_relations
    (M : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) (hM : IsFlatOnSite M)
    (U : C) (a : Fin n → A.obj.obj (op U)) (s : Fin n → M.val.obj (op U))
    (h : ∑ i, a i • s i = 0) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ (l : ℕ) (b : Fin n → Fin l → A.obj.obj (op V))
        (t : Fin l → M.val.obj (op V)),
        (∀ i, M.val.map f.op (s i) = ∑ j, b i j • t j) ∧
        (∀ j, ∑ i, A.obj.map f.op (a i) * b i j = 0) := by
  let P := (coeffIdeal A.obj n).toPresheafOfModules
  let Q := coeffPresheaf A.obj n
  let g : P ⟶ Q := (coeffIdeal A.obj n).ι
  let x : (siteTensorPresheaf P M.val).obj (op U) :=
    ∑ i, coeffGenerator A.obj n (op U) ⟨a⟩ i ⊗ₜ[A.obj.obj (op U)] s i
  have hg : Mono g := inferInstanceAs (Mono (coeffIdeal A.obj n).ι)
  have hzero : (siteTensorHom g M.val).app (op U) x = 0 := by
    let g' : P.obj (op U) →ₗ[A.obj.obj (op U)] Q.obj (op U) := (g.app (op U)).hom
    change TensorProduct.map g' (LinearMap.id :
      M.val.obj (op U) →ₗ[A.obj.obj (op U)] M.val.obj (op U))
      (∑ i, coeffGenerator A.obj n (op U) ⟨a⟩ i ⊗ₜ[A.obj.obj (op U)] s i) = 0
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply]
    change (∑ i, Finsupp.single (⟨a⟩ : Labels A.obj n (op U)) (a i) ⊗ₜ[A.obj.obj (op U)]
      s i) = 0
    calc
      _ = ∑ i, Finsupp.single (⟨a⟩ : Labels.{uC,vC,r,m} A.obj n (op U))
          (1 : A.obj.obj (op U)) ⊗ₜ[A.obj.obj (op U)] (a i • s i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← TensorProduct.smul_tmul]
        congr 1
        simp
      _ = _ ⊗ₜ[A.obj.obj (op U)] (∑ i, a i • s i) :=
        (TensorProduct.tmul_sum _ _ _).symm
      _ = 0 := by rw [h, TensorProduct.tmul_zero]
  have hi := tensor_mono_locallyInjective A M hM g
  let S := Presheaf.equalizerSieve
    (F := (siteTensorPresheaf P M.val).presheaf) x 0
  have hcover : S ∈ J U := by
    apply Presheaf.equalizerSieve_mem J
      ((PresheafOfModules.toPresheaf (A.obj ⋙ forget₂ CommRingCat RingCat)).map
        (siteTensorHom g M.val)) x 0
    change (siteTensorHom g M.val).app (op U) x =
      (siteTensorHom g M.val).app (op U) 0
    rw [map_zero]
    exact hzero
  refine ⟨S, hcover, ?_⟩
  intro V f hf
  have hx : (siteTensorPresheaf P M.val).map f.op x = 0 := by
    change (siteTensorPresheaf P M.val).map f.op x =
      (siteTensorPresheaf P M.val).map f.op 0 at hf
    simpa only [map_zero] using hf
  have hlocal : ∑ i, coeffGenerator A.obj n (op V)
      ⟨fun i ↦ A.obj.map f.op (a i)⟩ i ⊗ₜ[A.obj.obj (op V)]
        (show M.val.obj (op V) from M.val.map f.op (s i)) = 0 := by
    convert hx using 1
    dsimp only [x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    let ρP : P.obj (op U) →ₛₗ[(A.obj.map f.op).hom] P.obj (op V) := P.restrictₛₗ f.op
    let ρM : M.val.obj (op U) →ₛₗ[(A.obj.map f.op).hom] M.val.obj (op V) :=
      M.val.restrictₛₗ f.op
    change _ = TensorProduct.map ρP ρM
      (coeffGenerator A.obj n (op U) ⟨a⟩ i ⊗ₜ[A.obj.obj (op U)] s i)
    rw [TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    change Finsupp.single (⟨fun j ↦ A.obj.map f.op (a j)⟩ : Labels A.obj n (op V))
      (A.obj.map f.op (a i)) = coeffMap A.obj n f.op (Finsupp.single ⟨a⟩ (a i))
    simp only [coeffMap, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapDomain_single]
    rfl
  exact coeff_tensor_vanish A.obj n (op V) _ _ hlocal

end Sheaves
end SheafOfModules

namespace SheafOfModules

/-- Every finite relation between sections of a flat module sheaf is locally trivial.
Source: Stacks Project, Modules on Sites, Tag 08FC, implication (1) to (2), and
Tag 04VX for the finite tensor-vanishing criterion
(auxiliary; not a blueprint node).

Proof: For each V let T(V) be the coefficient n-tuples over V, lifted to the
module universe, and let Q(V) be the free module on T(V). Its restriction sends
a labelled coefficient to the correspondingly restricted labelled coefficient.
Let P be the submodule presheaf spanned by all a_i e_a. Sheafification preserves
the inclusion P → Q. Flatness and the natural isomorphism between associated
presheaf tensor and tensor of associated sheaves imply that P tensor M → Q tensor M
is locally injective. The given relation defines x = Σ (a_i e_a) tensor s_i,
whose image is e_a tensor Σ a_i s_i = 0, so x is locally zero.

A finite tensor-vanishing witness gives s_i = Σ_j c_ij y_j, auxiliary relations
Σ_j e_kj y_j = 0, and identities Σ_i c_ij g_i + Σ_k e_kj z_k = 0 in P(V).
Projection to the a-label writes z_k(a) = Σ_i d_ki a_i, by the defining span of P.
Set b_ij = c_ij + Σ_k d_ki e_kj. The auxiliary relations preserve the factorization
of the s_i, and projection of the identities yields Σ_i a_i b_ij = 0.
All objects are small in max(r,m), including the empty coefficient tuple; no
hom-set of the site is used as an index. -/
theorem local_equationalCriterion_of_isFlatOnSite
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    (R : Sheaf J CommRingCat.{r})
    (M : SheafOfModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hM : IsFlatOnSite M) :
      ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, R.obj.map f.op (a p) * b p q) = 0) := by
  intro U n a s h
  exact flat_relations (n := n) R M hM U a s h

end SheafOfModules
