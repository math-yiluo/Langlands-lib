/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Topology.Sheaves.Skyscraper
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Degreewise stalk tensor comparison

Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex-degrees).
-/

@[expose] public section

universe u₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance stalkTensorDegreesMonoidal :
    MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem stalk_preserves_colimits (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (RingedSpace.moduleStalkFunctor X x) := by
  classical
  have : PreservesColimitsOfShape J (SheafOfModules.toSheaf O) := inferInstance
  have : PreservesColimitsOfShape J
      (TopCat.Sheaf.forget AddCommGrpCat.{u₁} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u₁} x) :=
    (stalkSkyscraperSheafAdjunction x).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  -- Forgetting the stalk module structure gives the usual abelian-sheaf stalk functor.
  have : PreservesColimitsOfShape J
      (RingedSpace.moduleStalkFunctor X x ⋙
        forget₂ (ModuleCat.{u₁} (X.presheaf.stalk x)) AddCommGrpCat.{u₁}) :=
    inferInstanceAs (PreservesColimitsOfShape J
      (SheafOfModules.toSheaf O ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u₁} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u₁} x)))
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (RingedSpace.moduleStalkFunctor X x)
    (forget₂ (ModuleCat.{u₁} (X.presheaf.stalk x)) AddCommGrpCat.{u₁})

/-- Source: Stacks Project, Cohomology, Tag 06YB, tensor-stalk identification,
first two steps (blueprint: lem-pc-stalk-tensor-complex-degrees).

Proof: express the degree as the coproduct indexed by pairs `(p,q)` with `p+q=n`.
The canonical stalk/direct-sum comparison of Tag 009E identifies its stalk with
that coproduct of stalks. If its scalar ring is presented as a RingCat stalk,
identify it with the CommRingCat stalk by the canonical ring map on germs. Represent
scalars on a neighborhood to check that the two scalar actions agree, and transport
the linear equivalence along this identification. For smaller-universe diagonal
indices, lift the index type and reindex the coproduct along the lift equivalence.
Identify the algebraic direct sum with the categorical coproduct using
`ModuleCat.coprodIsoDirectSum`. Apply the tensor comparison to every summand and
use the universal property of the coproduct to obtain an isomorphism. Its value
on each injection is the displayed formula; no differential is involved. -/
theorem exists_stalk_tensor_degree_iso
    (φ : ∀ A B : SheafOfModules.{u₁} O,
      (RingedSpace.moduleStalkFunctor X x).obj (A ⊗ B) ≅
        (RingedSpace.moduleStalkFunctor X x).obj A ⊗
          (RingedSpace.moduleStalkFunctor X x).obj B) :
    ∃ e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ),
      ((S).obj (mapBifunctor F K (curriedTensor _))).X n ≅
        (mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _)).X n,
      ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (p q n : ℤ) (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
        (RingedSpace.moduleStalkFunctor X x).map
            (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ) p q n h) ≫
          (e F K n).hom =
        (φ (F.X p) (K.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((S).obj F) ((S).obj K) (curriedTensor _) (.up ℤ) p q n h := by
  classical
  let T := RingedSpace.moduleStalkFunctor X x
  let π := ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)
  let A (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) :
      GradedObject (ℤ × ℤ) (SheafOfModules.{u₁} O) := fun i ↦ F.X i.1 ⊗ K.X i.2
  have (n : ℤ) : PreservesColimitsOfShape (Discrete (π ⁻¹' {n})) T :=
    stalk_preserves_colimits X x _
  let e (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ) (n : ℤ) :=
    PreservesCoproduct.iso T ((A F K).mapObjFun π n) ≪≫
      Sigma.mapIso (fun i : π ⁻¹' {n} ↦ φ (F.X i.1.1) (K.X i.1.2))
  refine ⟨e, ?_⟩
  intro F K p q n h
  change T.map (Sigma.ι ((A F K).mapObjFun π n) ⟨(p, q), h⟩) ≫
    (e F K n).hom = _
  dsimp only [e, Iso.trans_hom]
  rw [← Category.assoc]
  have hh : (PreservesCoproduct.iso T ((A F K).mapObjFun π n)).hom =
      inv (sigmaComparison T ((A F K).mapObjFun π n)) := by
    apply (cancel_mono (sigmaComparison T ((A F K).mapObjFun π n))).1
    simp only [← PreservesCoproduct.inv_hom, Iso.hom_inv_id, IsIso.inv_hom_id]
  rw [hh]
  rw [map_ι_comp_inv_sigmaComparison, Sigma.ι_mapIso_hom]
  rfl

end CochainComplex
