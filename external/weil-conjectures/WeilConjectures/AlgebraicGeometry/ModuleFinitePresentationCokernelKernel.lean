/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import Mathlib.Topology.Sheaves.Module
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-! # Finite type of relations for a cokernel

Source: Stacks Project, Modules, Lemma 0H96.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

-- These generator-transport helpers adapt the proved private helpers in
-- CoherentKernelConditionRestriction to arbitrary ringed spaces.
open SheafOfModules in
private theorem finiteType_of_data
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

open SheafOfModules in
private theorem finiteType_of_generatingSectionsData
    {C : Type u} [Category.{u} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (s : M.GeneratingSections) [s.IsFiniteType] :
    M.IsFiniteType := by
  have : s.localGeneratorsData.IsFiniteType := ⟨fun i ↦ by
    dsimp only [GeneratingSections.localGeneratorsData]
    infer_instance⟩
  exact finiteType_of_data s.localGeneratorsData

open SheafOfModules in
private theorem finiteType_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := ⟨fun i ↦ by
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType⟩
  exact finiteType_of_data q'

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules in
private theorem finiteType_pushforward
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  let Q : ((pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
          pushforward (𝟙 _)
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        let e : (pushforward.{u} (F := G') ψ).obj (unit (R.over (P.X i.2.1))) ≅
            unit (S.over i.1) := overS.mapIso η
        have : PreservesColimitsOfSize.{u, u} (pushforward.{u} (F := G') ψ) := h _ _ _
        exact (P.generators i.2.1).map (pushforward.{u} (F := G') ψ) e.symm }
  have : Q.IsFiniteType := ⟨fun i ↦ by
    have := hP.isFiniteType i.2.1
    dsimp [Q]
    infer_instance⟩
  exact finiteType_of_data Q

open SheafOfModules in
private theorem finiteType_pushforward_leftAdjoint
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}}
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  apply +allowSynthFailures finiteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_equivOver {X : RingedSpace.{u}} (U : TopologicalSpace.Opens X)
    (M : SheafOfModules.{u} ((moduleRings X).over U)) [M.IsFiniteType] :
    ((U.sheafOfModulesEquivOver (moduleRings X)).functor.obj M).IsFiniteType := by
  let := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : TopologicalSpace.Opens ↥U) : (Over.post U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over V)
      (((Opens.grothendieckTopology X).over U).over
        (U.overEquivalence.symm.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.symm.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.overPullbackSheafEquivOver.app (moduleRings X)).inv).obj M).IsFiniteType
  exact finiteType_pushforward_leftAdjoint U.overEquivalence.symm.functor _ (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_equivOverInverse {X : RingedSpace.{u}} (U : TopologicalSpace.Opens X)
    (M : SheafOfModules.{u} (U.sheafRestrict.obj (moduleRings X))) [M.IsFiniteType] :
    ((U.sheafOfModulesEquivOver (moduleRings X)).inverse.obj M).IsFiniteType := by
  have (V : Over U) : (Over.post U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.sheafRestrictSheafEquivOver.app (moduleRings X)).inv).obj M).IsFiniteType
  exact finiteType_pushforward_leftAdjoint U.overEquivalence.functor _
    (U.sheafOfModulesEquivOverInverseUnit (moduleRings X))

private theorem finiteType_kernel_of_exact (X : RingedSpace.{u})
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.Exact)
    [S.X₁.IsFiniteType] : (kernel S.g).IsFiniteType := by
  have : Epi (kernel.lift S.g S.f S.zero) := hS.epi_kernelLift
  exact (finiteType_image_extension X).1 (kernel.lift S.g S.f S.zero)

private theorem finiteType_kernel_comp_of_epi (X : RingedSpace.{u})
    {F G H : SheafOfModules.{u} (moduleRings X)} (f : F ⟶ G) (g : G ⟶ H)
    [Epi f] [(kernel f).IsFiniteType] [(kernel g).IsFiniteType] :
    (kernel (f ≫ g)).IsFiniteType := by
  have he := kernelCokernelCompSequence_exact f g
  let S := he.sc 0 (by decide)
  have hδ : kernelCokernelCompSequence.δ f g = 0 := by
    have hf : cokernel.π f = 0 := by
      apply (cancel_epi f).mp
      simp
    simp [kernelCokernelCompSequence.δ_fac, hf]
  have hS : S.ShortExact := by
    refine { exact := he.exact 0 (by decide), mono_f := ?_, epi_g := ?_ }
    · change Mono ((kernelCokernelCompSequence f g).map' 0 1)
      infer_instance
    · exact ((he.sc 1 (by decide)).exact_iff_epi hδ).mp (he.exact 1 (by decide))
  have : S.X₁.IsFiniteType := inferInstanceAs (kernel f).IsFiniteType
  have : S.X₃.IsFiniteType := inferInstanceAs (kernel g).IsFiniteType
  exact (finiteType_image_extension X).2.2 S hS

private theorem finiteType_kernel_of_equivOver {X : RingedSpace.{u}}
    (U : TopologicalSpace.Opens X)
    {M N : SheafOfModules.{u} ((moduleRings X).over U)} (f : M ⟶ N)
    [(kernel ((U.sheafOfModulesEquivOver (moduleRings X)).functor.map f)).IsFiniteType] :
    (kernel f).IsFiniteType := by
  let E := U.sheafOfModulesEquivOver (moduleRings X)
  have : (E.functor.obj (kernel f)).IsFiniteType :=
    finiteType_of_iso (R := U.sheafRestrict.obj (moduleRings X))
      (PreservesKernel.iso E.functor f).symm
  have : (E.inverse.obj (E.functor.obj (kernel f))).IsFiniteType :=
    finiteType_equivOverInverse U _
  exact finiteType_of_iso (R := (moduleRings X).over U)
    (M := E.inverse.obj (E.functor.obj (kernel f))) (E.unitIso.app (kernel f)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The relations of the quotient presentation are of finite type.
Source: Stacks Project, Modules, Lemma 0H96, proof, lines 1440-1454
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel-kernel).

Proof: Set c = cokernel.π f and π = P.generators.π on U. The kernel of π is
finite type since P has finitely many relations and their map onto that kernel is epi.
The image of f restricted to U is finite type, since restriction preserves finite type
and finite type passes to epi images. Set N = kernel (π ≫ c|U). The restriction of π
maps N onto image(f|U): lift sections locally through the epi π; their lifts belong to N
because c kills them. Its kernel is kernel π, computed sectionwise. This gives a short
exact sequence from kernel π to N to image(f|U). The finite-type extension theorem gives
the result. This argument also applies when either finite generating family is empty.
-/
theorem kernel_composite_cokernel_isFiniteType
    (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    {G H : SheafOfModules.{u} (moduleRings X)} (f : G ⟶ H) [G.IsFiniteType]
    (P : (H.over U).Presentation) [P.IsFinite] :
    (kernel (P.generators.π ≫
      (SheafOfModules.overFunctor (moduleRings X) U).map (cokernel.π f))).IsFiniteType := by
  let R := moduleRings X
  let A := SheafOfModules.overFunctor R U
  let E := U.sheafOfModulesEquivOver R
  let Y : RingedSpace := X.restrict U.isOpenEmbedding
  -- The finite relation family generates the kernel of the presentation map.
  have hP : (kernel P.generators.π).IsFiniteType :=
    finiteType_of_generatingSectionsData (R := R.over U) P.relations
  have hG : (G.over U).IsFiniteType := by
    exact finiteType_pushforward_leftAdjoint (Over.forget U) (𝟙 _) (Iso.refl _)
  have : (E.functor.obj (G.over U)).IsFiniteType := finiteType_equivOver U _
  have : (E.functor.obj (kernel P.generators.π)).IsFiniteType := finiteType_equivOver U _
  let π := E.functor.map P.generators.π
  let c := E.functor.map (A.map (cokernel.π f))
  have : (kernel π).IsFiniteType :=
    finiteType_of_iso (R := U.sheafRestrict.obj R)
      (PreservesKernel.iso E.functor P.generators.π)
  -- Exactness gives an epimorphism from the restricted source onto ker(c).
  have hc : (kernel c).IsFiniteType := by
    let T := ((ShortComplex.mk f (cokernel.π f) (by simp)).map A).map E.functor
    have : T.X₁.IsFiniteType := by
      change (E.functor.obj (G.over U)).IsFiniteType
      infer_instance
    exact finiteType_kernel_of_exact Y T
      (((ShortComplex.exact_cokernel f).map A).map E.functor)
  have : Epi π := by dsimp [π]; infer_instance
  -- Use the ambient kernels directly for these composite maps.
  have : HasKernel (π ≫ c) := HasKernels.has_limit _
  have hN : (kernel (π ≫ c)).IsFiniteType :=
    finiteType_kernel_comp_of_epi Y π c
  -- Transfer the finite-type conclusion back to the slice-site kernel.
  have : HasKernel (E.functor.map (P.generators.π ≫ A.map (cokernel.π f))) :=
    HasKernels.has_limit _
  have : (kernel (E.functor.map (P.generators.π ≫ A.map (cokernel.π f)))).IsFiniteType := by
    simpa only [Functor.map_comp] using hN
  exact finiteType_kernel_of_equivOver U (P.generators.π ≫ A.map (cokernel.π f))

end AlgebraicGeometry.RingedSpace
