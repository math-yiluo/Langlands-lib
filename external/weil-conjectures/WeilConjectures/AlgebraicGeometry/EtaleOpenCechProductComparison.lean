/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Comparing open products with étale fibre products

Source: Stacks Project, Tags 03AK and 03AM; product comparison in
lem-sc-etale-open-cech-injective-augmentation, proof step 1.
(blueprint: lem-sc-etale-open-cech-product-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private noncomputable def imageFan
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (t : Fin (n + 1) → ι) :
    Fan (fun k ↦ Over.mk (i.map (homOfLE (le_top (a := U (t k)))))) :=
  Fan.mk (Over.mk (i.map (homOfLE (le_top (a := ∏ᶜ fun k ↦ U (t k))))))
    (fun k ↦ Over.homMk (i.map (Pi.π (fun k ↦ U (t k)) k)) (by
      change i.map _ ≫ i.map _ = i.map _
      rw [← i.map_comp]
      congr 1))

private noncomputable def imageFanIsLimit
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (t : Fin (n + 1) → ι) :
    IsLimit (imageFan i U n t) := by
  let hi := isLimitOfHasProductOfPreservesLimit i (fun k ↦ U (t k))
  refine Fan.IsLimit.mk _
    (fun s ↦ Over.homMk
      (hi.lift (Fan.mk s.pt.left (fun k ↦ (s.proj k).left))) (ht.hom_ext _ _)) ?_ ?_
  · intro s k
    apply Over.OverMorphism.ext
    exact hi.fac (Fan.mk s.pt.left (fun k ↦ (s.proj k).left)) (Discrete.mk k)
  · intro s m hm
    apply Over.OverMorphism.ext
    apply hi.hom_ext
    intro k
    exact (congrArg (fun a ↦ a.left) (hm k.as)).trans
      (hi.fac (Fan.mk s.pt.left (fun k ↦ (s.proj k).left)) k).symm

private noncomputable def productIso
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (t : Fin (n + 1) → ι) :
    i.obj (∏ᶜ fun k ↦ U (t k)) ≅
      (∏ᶜ fun k ↦ Over.mk (i.map (homOfLE (le_top (a := U (t k)))))).left :=
  (Over.forget (i.obj ⊤)).mapIso
    ((imageFanIsLimit i ht U n t).conePointUniqueUpToIso (limit.isLimit _))

private theorem productIso_inv_π
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (t : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (productIso i ht U n t).inv ≫ i.map (Pi.π (fun k ↦ U (t k)) k) =
      (Pi.π (fun k ↦ Over.mk (i.map (homOfLE (le_top (a := U (t k)))))) k).left := by
  exact congrArg (fun a ↦ a.left)
    (IsLimit.conePointUniqueUpToIso_inv_comp
      (imageFanIsLimit i ht U n t) (limit.isLimit _) (Discrete.mk k))

private def tupleEquiv {ι : Type u} (n : ℕ) :
    (Fin (n + 1) → ULift.{u + 1} ι) ≃ (Fin (n + 1) → ι) :=
  Equiv.arrowCongr (Equiv.refl _) Equiv.ulift

private noncomputable def degreeIso
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u} (U : ι → X.Opens)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∏ᶜ (fun t : Fin (n + 1) → ι ↦ P.obj (op (i.obj (∏ᶜ fun k ↦ U (t k))))) ≅
      ∏ᶜ (fun s : Fin (n + 1) → ULift.{u + 1} ι ↦
        P.obj (op (∏ᶜ fun k ↦
          Over.mk (i.map (homOfLE (le_top (a := U (s k).down))))).left)) :=
  (Pi.reindex (tupleEquiv n) _).symm ≪≫
    Pi.mapIso (fun s ↦ P.mapIso ((productIso i ht U n (tupleEquiv n s)).symm.op))

private theorem degreeIso_hom_π
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u} (U : ι → X.Opens)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (s : Fin (n + 1) → ULift.{u + 1} ι) :
    (degreeIso i ht U P n).hom ≫ Pi.π _ s =
      Pi.π _ (tupleEquiv n s) ≫ P.map (productIso i ht U n (tupleEquiv n s)).inv.op := by
  simp only [degreeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Pi.mapIso_hom_π]
  rw [← Category.assoc, Pi.reindex_inv_π]
  rfl

private theorem productIso_indexMap
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u} (U : ι → X.Opens)
    {n m : ℕ} (t : Fin (n + 1) → ι) (α : Fin (m + 1) → Fin (n + 1)) :
    (Pi.lift (fun k ↦ Pi.π
      (fun k ↦ Over.mk (i.map (homOfLE (le_top (a := U (t k)))))) (α k))).left ≫
        (productIso i ht U m (t ∘ α)).inv =
      (productIso i ht U n t).inv ≫
        i.map (Pi.lift (fun k ↦ Pi.π (fun k ↦ U (t k)) (α k))) := by
  apply (isLimitOfHasProductOfPreservesLimit i (fun k ↦ U ((t ∘ α) k))).hom_ext
  intro k
  change _ ≫ i.map (Pi.π (fun k ↦ U ((t ∘ α) k)) k.as) =
    _ ≫ i.map (Pi.π (fun k ↦ U ((t ∘ α) k)) k.as)
  rw [Category.assoc, productIso_inv_π]
  rw [← Over.comp_left, Pi.lift_comp_π]
  rw [Category.assoc, ← i.map_comp]
  change _ = (productIso i ht U n t).inv ≫
    i.map ((Pi.lift (fun k ↦ Pi.π (fun k ↦ U (t k)) (α k))) ≫
      Pi.π (fun k ↦ U (t (α k))) k.as)
  rw [Pi.lift_comp_π, productIso_inv_π]

private theorem degreeIso_indexMap
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u} (U : ι → X.Opens)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {n m : ℕ}
    (α : Fin (m + 1) → Fin (n + 1)) :
    (degreeIso i ht U P m).hom ≫
      Pi.lift (fun s : Fin (n + 1) → ULift.{u + 1} ι ↦
        Pi.π _ (s ∘ α) ≫ P.map (Pi.lift (fun k ↦ Pi.π
          (fun k ↦ Over.mk (i.map (homOfLE (le_top (a := U (s k).down)))))
            (α k))).left.op) =
      Pi.lift (fun t : Fin (n + 1) → ι ↦ Pi.π _ (t ∘ α) ≫
        P.map (i.map (Pi.lift (fun k ↦ Pi.π (fun k ↦ U (t k)) (α k)))).op) ≫
          (degreeIso i ht U P n).hom := by
  apply Pi.hom_ext
  intro s
  simp only [Category.assoc, Pi.lift_comp_π]
  rw [← Category.assoc, degreeIso_hom_π]
  rw [degreeIso_hom_π, ← Category.assoc, Pi.lift_comp_π]
  simp only [Category.assoc]
  congr 1
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 1
  exact congrArg Quiver.Hom.op (productIso_indexMap i ht U (tupleEquiv n s) α)

/-- Finite-limit preservation identifies the pulled-back open Čech complex with
that of the image family over the terminal object, after lifting its index universe.

Source: Stacks Project, Tags 03AK and 03AM; the product comparison in step 1 of
lem-sc-etale-open-cech-injective-augmentation.
(blueprint: lem-sc-etale-open-cech-product-comparison)

Proof: For each nonempty finite tuple t, the image under i of its open product is
an étale product, because i preserves finite products. Since i(top) is terminal,
this is also the fibre product of the images over i(top). Construct the unique
projection-compatible isomorphism with the product in Over (i(top)). Restriction
by P gives the corresponding isomorphism of section groups. Reindex tuples by
s ↦ fun k ↦ (s k).down, whose inverse is t ↦ fun k ↦ ULift.up (t k), and use the
product universal property to get degreewise inverse maps. Omitting any factor
commutes with the product comparison: the two composites have the same projections.
This also holds for the tuple reindexing, so these maps commute with every face
and therefore with the alternating differential. The inverse maps give the
inverse complex map. For an empty family, every tuple index is empty because the
tuples have positive length; both section products are zero, and the same maps
are inverse. No sheaf, covering, finiteness of the index, or injectivity is used. -/
theorem etaleOpenCechProductComparison
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale) [PreservesFiniteLimits i]
    (ht : IsTerminal (i.obj ⊤)) {ι : Type u} (U : ι → X.Opens)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Nonempty ((cechComplexFunctor U).obj (i.op ⋙ P) ≅
      (cechComplexFunctor (fun t : ULift.{u + 1} ι ↦
        Over.mk (i.map (homOfLE (le_top (a := U t.down)))))).obj
          ((Over.forget (i.obj ⊤)).op ⋙ P)) := by
  classical
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n ↦ degreeIso i ht U P n) ?_⟩
  intro n m h
  have hm : n + 1 = m := h
  subst m
  simp only [cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
    Functor.comp_obj, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact degreeIso_indexMap i ht U P j.succAbove

end AlgebraicGeometry.Scheme
