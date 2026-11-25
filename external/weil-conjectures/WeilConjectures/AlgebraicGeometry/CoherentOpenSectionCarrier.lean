/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Coherent carrier of a section on an open subset

Source: Stacks Project, Tag 01YB, first paragraph of the proof.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem quasiCoherent_slice_image {X : Scheme.{u}} (U : X.Opens)
    {F G : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (Abelian.image φ).IsQuasicoherent := by
  have (V : Over U) :
      HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{u} :=
    inferInstance
  have (V : Over U) :
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have (V : U.toScheme.Opens) :
      HasSheafify ((Opens.grothendieckTopology U.carrier).over V) AddCommGrpCat.{u} :=
    inferInstance
  have (V : U.toScheme.Opens) :
      ((Opens.grothendieckTopology U.carrier).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : U.toScheme.Opens) :
      (Over.post U.overEquivalence.inverse).IsContinuous
        ((Opens.grothendieckTopology U.carrier).over V)
        (((Opens.grothendieckTopology X).over U).over
          (U.overEquivalence.inverse.obj V)) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.inverse _ _).overPost V)
  have (V : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over V)
        ((Opens.grothendieckTopology U.carrier).over (U.overEquivalence.functor.obj V)) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost V)
  let T := (overEquiv U).functor
  have : (T.obj F).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.inverse _ (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
  have : (T.obj G).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.inverse _ (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
  have hc := isQuasicoherent_cokernel (T.map φ)
  have : (T.obj (Limits.cokernel φ)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Limits.PreservesCokernel.iso T φ).symm hc
  have hk := isQuasicoherent_kernel (T.map (Limits.cokernel.π φ))
  have : (T.obj (Abelian.image φ)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Limits.PreservesKernel.iso T (Limits.cokernel.π φ)).symm hk
  have hback : ((overEquiv U).inverse.obj (T.obj (Abelian.image φ))).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    ((overEquiv U).unitIso.app (Abelian.image φ)).symm hback

private theorem finiteType_image_free_slice (X : Scheme.{u}) (U : X.Opens) (n : ℕ)
    {G : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (φ : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶ G) :
    (Abelian.image φ).IsFiniteType := by
  have hs (V : Over U) :
      HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{u} :=
    inferInstance
  have (V : Over U) :
      HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{u} :=
    (hs V).isRightAdjoint
  have (V : Over U) :
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let g := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n))).ofEpi (Abelian.factorThruImage φ)
  let q := g.localGeneratorsData
  have : g.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
  apply SheafOfModules.IsFiniteType.mk
  refine ⟨q, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := q) (fun i ↦ ?_)
  dsimp [q, SheafOfModules.GeneratingSections.localGeneratorsData]
  exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def section_on_open {X : Scheme.{u}} (E : X.Modules)
    (U : X.Opens) (s : E.val.obj (op U)) : (E.over U).sections :=
  (E.over U).val.sectionsMk
    (fun W ↦ E.val.map W.unop.hom.op s)
    (fun {W Z} f ↦ by
      change E.val.map f.unop.left.op (E.val.map W.unop.hom.op s) =
        E.val.map Z.unop.hom.op s
      exact (E.val.map_comp_apply W.unop.hom.op f.unop.left.op s).symm.trans
        (E.val.congr_map_apply (Subsingleton.elim _ _) s))

set_option backward.isDefEq.respectTransparency false in
/-- A section of a quasi-coherent module on an open of a Noetherian scheme
lifts to a coherent submodule.

Source: Stacks Project, Tag 01YB, first paragraph; Tags 01PF and 01XZ.
(blueprint: lem-pc-coherent-open-section-carrier)

Proof: Regard the section as a morphism from the structure module on U to E|U.
Its image is quasi-coherent and of finite type, since the structure module is
quasi-coherent and generated by one. Every open in a Noetherian space is
quasi-compact. Extend this image to a finite-type quasi-coherent submodule H
of E by Tag 01PF. Tag 01XZ makes H coherent. On U the extended submodule equals
the image; the original section is the image of one, so it has a preimage t
in H(U). This also covers the empty open, using its unique section. -/
theorem exists_coherent_open_section_carrier
    {X : Scheme.{u}} [IsNoetherian X]
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens) (s : E.val.obj (op U)) :
    ∃ (H : X.Modules) (h : H ⟶ E) (t : H.val.obj (op U)),
      H.IsQuasicoherent ∧ RingedSpace.IsCoherent X.toRingedSpace H ∧
      Mono h ∧ h.val.app (op U) t = s := by
  have hs : HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
    inferInstance
  have : HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
    hs.isRightAdjoint
  have : ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  let φ : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 1)) ⟶
      E.over U := (E.over U).freeHomEquiv.symm (fun _ ↦ section_on_open E U s)
  have : (E.over U).IsQuasicoherent := SheafOfModules.isQuasicoherent_over E U
  have hqc := quasiCoherent_slice_image U φ
  have hft := finiteType_image_free_slice X U 1 φ
  have : (Abelian.image φ).IsQuasicoherent := hqc
  have : (Abelian.image φ).IsFiniteType := hft
  obtain ⟨H, hHqc, hHft, h, hh, e, he⟩ :=
    exists_quasicoherent_finiteType_submodule_extension X U
      (TopologicalSpace.NoetherianSpace.isCompact _) E (Abelian.image φ) (Abelian.image.ι φ)
  let τ := (Abelian.image φ).freeHomEquiv (Abelian.factorThruImage φ) ⟨0⟩
  let t := e.inv.val.app (op (Over.mk (𝟙 U)))
    (τ.val (op (Over.mk (𝟙 U))))
  refine ⟨H, h, t, hHqc,
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mpr ⟨hHqc, hHft⟩, hh, ?_⟩
  have ht : (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U)))) = s := by
    have hsec := congrFun
      ((E.over U).freeHomEquiv.apply_symm_apply
        (fun _ : ULift.{u} (Fin 1) ↦ section_on_open E U s)) ⟨0⟩
    change (E.over U).freeHomEquiv φ ⟨0⟩ = section_on_open E U s at hsec
    rw [← Abelian.image.fac φ, SheafOfModules.freeHomEquiv_comp_apply] at hsec
    have hev := congrArg (fun z ↦ z.val (op (Over.mk (𝟙 U)))) hsec
    change (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U)))) = E.val.map (𝟙 _) s at hev
    simpa using hev
  have he' := congrArg (fun f ↦ f.val.app (op (Over.mk (𝟙 U)))) he
  change h.val.app (op U) =
    e.hom.val.app (op (Over.mk (𝟙 U))) ≫
      (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U))) at he'
  rw [he']
  change (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
    ((e.inv ≫ e.hom).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U))))) = s
  simpa using ht

end AlgebraicGeometry.Scheme.Modules
