/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Coherence on locally Noetherian schemes

Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.1, Tag 01XZ
(blueprint: pqf-lem-coherent-ft-locnoeth).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem isFinitePresentation_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((overEquiv (X := X) U).inverse.obj M).IsFinitePresentation := by
  have (V : CategoryTheory.Over U) :
      (Over.post (X := V) U.overEquivalence.symm.inverse).IsContinuous
        ((Opens.grothendieckTopology ↥X).over U |>.over V)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

private theorem isQuasicoherent_overEquiv (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsQuasicoherent] :
    ((overEquiv (X := X) U).functor.obj M).IsQuasicoherent := by
  have (V : TopologicalSpace.Opens ↥U) :
      (Over.post (X := V) U.overEquivalence.symm.functor).IsContinuous
        ((Opens.grothendieckTopology ↥U).over V)
        (((Opens.grothendieckTopology ↥X).over U).over
          (U.overEquivalence.inverse.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

private theorem isFinitePresentation_free
    {C : Type u} [SmallCategory C] [Limits.HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) [Finite I] : (SheafOfModules.free (R := R) I).IsFinitePresentation := by
  let P := SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (PEmpty.{u + 1}) ⟶ SheafOfModules.free (R := R) I)
    (𝟙 _) (by simp) (Limits.CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite I)⟩,
    ⟨inferInstanceAs (Finite (PEmpty.{u + 1}))⟩⟩
  exact P.isFinitePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem isFinitePresentation_of_generators_kernel
    {C : Type u} [SmallCategory C] [Limits.HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (G : M.GeneratingSections)
    [G.IsFiniteType] [(Limits.kernel G.π).IsFiniteType] : M.IsFinitePresentation := by
  classical
  obtain ⟨r, hr⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (Limits.kernel G.π)
  let H (j : r.I) := SheafOfModules.overFunctor R (r.X j)
  have (j : r.I) : Limits.PreservesColimitsOfSize.{u, u} (H j) :=
    inferInstanceAs (Limits.PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward (F := Over.forget (r.X j)) (𝟙 (R.over (r.X j)))))
  let e (j : r.I) := SheafOfModules.mapFreeIso (H j) G.I (Iso.refl _)
  let a (j : r.I) := (r.generators j).π ≫ (H j).map (Limits.kernel.ι G.π) ≫ (e j).inv
  let b (j : r.I) := (G.map (H j) (Iso.refl _)).π
  have hab (j : r.I) : a j ≫ b j = 0 := by
    dsimp only [a, b]
    rw [SheafOfModules.GeneratingSections.map_π_eq]
    simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      Limits.kernel.condition, Functor.map_zero, Limits.comp_zero]
  have hcol (j : r.I) : Limits.IsColimit (Limits.CokernelCofork.ofπ (b j) (hab j)) := by
    let c := Limits.CokernelCofork.ofπ G.π (Limits.kernel.condition G.π)
    have hc : Limits.IsColimit c := Abelian.epiIsCokernelOfKernel
      (Limits.KernelFork.ofι (Limits.kernel.ι G.π) (Limits.kernel.condition G.π))
      (Limits.kernelIsKernel _)
    have hh : ((H j).map (Limits.kernel.ι G.π) ≫ (e j).inv) ≫ b j = 0 := by
      dsimp only [b]
      rw [SheafOfModules.GeneratingSections.map_π_eq]
      simp only [e, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
        Limits.kernel.condition, Functor.map_zero]
    let c' := Limits.CokernelCofork.ofπ (b j) hh
    have hc' : Limits.IsColimit c' := Limits.IsCokernel.ofIso _ (c.mapIsColimit hc (H j)) c'
      (Iso.refl _) (e j).symm (Iso.refl _) (by simp)
      (by
        simp only [c', Limits.CokernelCofork.π_ofπ, b, e,
          SheafOfModules.GeneratingSections.map_π_eq, Iso.symm_hom,
          Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
        rfl)
    exact Limits.isCokernelEpiComp hc' (r.generators j).π rfl
  let D : M.QuasicoherentData :=
    { I := r.I
      X := r.X
      coversTop := r.coversTop
      presentation j := SheafOfModules.presentationOfIsCokernelFree (a j) (b j)
        (hab j) (hcol j) }
  have : D.IsFinitePresentation := ⟨fun j ↦ by
    have := hr.isFiniteType j
    exact ⟨⟨inferInstanceAs (Finite G.I)⟩,
      ⟨inferInstanceAs (Finite (r.generators j).I)⟩⟩⟩
  exact D.isFinitePresentation

private theorem isQuasicoherent_and_isFiniteType_of_isCoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (h : RingedSpace.IsCoherent X.toRingedSpace F) :
    F.IsQuasicoherent ∧ F.IsFiniteType := by
  classical
  have : F.IsFiniteType := h.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hfp (i : q.I) : (F.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using h.2 (q.X i) n f
    exact isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  have : F.IsFinitePresentation := by
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      F q.I q.X q.coversTop hfp
  exact ⟨inferInstance, h.1⟩

private theorem isCoherent_of_isQuasicoherent_and_isFiniteType
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hq : F.IsQuasicoherent) (ht : F.IsFiniteType) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  refine ⟨ht, ?_⟩
  intro U n f
  -- Reuse the sheafification hypotheses throughout the two sides of the equivalence.
  have : HasSheafify ((Opens.grothendieckTopology ↥X).over U) AddCommGrpCat.{u} :=
    inferInstance
  have : ((Opens.grothendieckTopology ↥X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : ∀ V : Over U, HasSheafify
      (((Opens.grothendieckTopology ↥X).over U).over V) AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  have : ∀ V : Over U,
      (((Opens.grothendieckTopology ↥X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun _ ↦ inferInstance
  have : HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u} := inferInstance
  have : (Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have : ∀ V : TopologicalSpace.Opens ↥U,
      HasSheafify ((Opens.grothendieckTopology ↥U).over V) AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  have : ∀ V : TopologicalSpace.Opens ↥U,
      ((Opens.grothendieckTopology ↥U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ ↦ inferInstance
  have : (F.over U).IsQuasicoherent := SheafOfModules.isQuasicoherent_over F U
  let e := overEquiv (X := X) U
  have hfree : (SheafOfModules.free
      (R := (Scheme.Opens.toScheme (X := X) U).ringCatSheaf)
      (ULift.{u} (Fin n))).IsFinitePresentation :=
    isFinitePresentation_free.{u} _
  have : (e.functor.obj (F.over U)).IsQuasicoherent :=
    isQuasicoherent_overEquiv X U (F.over U)
  have : (e.functor.obj
      (SheafOfModules.free (R := X.ringCatSheaf.over U)
        (ULift.{u} (Fin n)))).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation
      (Scheme.Opens.toScheme (X := X) U).ringCatSheaf).prop_of_iso
      (SheafOfModules.mapFreeIso e.functor (ULift.{u} (Fin n))
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm) hfree
  have hk := isFinitePresentation_kernel
    (X := Scheme.Opens.toScheme (X := X) U) (e.functor.map f)
  have hki := @isFinitePresentation_overEquiv_inverse X U
    (Limits.kernel (e.functor.map f)) hk
  let ek := e.unitIso.app (Limits.kernel f) ≪≫
    e.inverse.mapIso (Limits.PreservesKernel.iso e.functor f)
  have : (Limits.kernel f).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
      ek.symm hki
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (Limits.kernel f)

/-- On a locally Noetherian scheme, an `𝒪_X`-module is coherent exactly when it is
quasi-coherent and of finite type.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.1, Tag 01XZ
(blueprint: pqf-lem-coherent-ft-locnoeth).

Proof:
1. Choose finite local generators of a coherent module, reindexing their index sets by
   `ULift (Fin n)`. The coherence clause makes the kernel of each generator epimorphism
   finite type. Choose finite local generators of these kernels. Restriction preserves
   cokernels and free modules, so the restricted generator maps and relation maps give
   finite presentations on the refined cover. Glue them and use Mathlib's implication
   from finite presentation to quasi-coherence. The finite-type clause is retained.
2. For the converse, transport an arbitrary finite free map on `U` through `overEquiv U`
   to modules on the open subscheme. Its source has the finite presentation with zero
   relations and its target is quasi-coherent. The open subscheme is locally Noetherian,
   so `isFinitePresentation_kernel` gives a finitely presented kernel. The equivalence
   preserves kernels; transport the finite presentation back and use finite presentation
   implies finite type. This proves the kernel clause in the definition of coherence.
-/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules) :
    RingedSpace.IsCoherent X.toRingedSpace F ↔
      F.IsQuasicoherent ∧ F.IsFiniteType := by
  exact ⟨isQuasicoherent_and_isFiniteType_of_isCoherent X F,
    fun ⟨hq, ht⟩ ↦ isCoherent_of_isQuasicoherent_and_isFiniteType X F hq ht⟩

end AlgebraicGeometry.Scheme.Modules
