/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators
import all WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineCapture
import all WeilConjectures.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # A finitely presented replacement on one affine open

Source: Stacks Project, Properties, Lemma 01PI, affine construction.
(blueprint: lem-weil-pbc-module-finite-presentation-affine-replacement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem sliceSheafify (X : Scheme.{u}) (U : X.Opens) : ∀ T : Over U,
      HasSheafify (((Opens.grothendieckTopology ↥X).over U).over T) AddCommGrpCat.{u} :=
  fun _ ↦ inferInstance
attribute [local instance] sliceSheafify

private theorem sliceWeakSheafify (X : Scheme.{u}) (U : X.Opens) : ∀ T : Over U,
      HasWeakSheafify (((Opens.grothendieckTopology ↥X).over U).over T) AddCommGrpCat.{u} :=
  fun T ↦ (sliceSheafify X U T).isRightAdjoint
attribute [local instance] sliceWeakSheafify

private theorem sliceLocallyBijective (X : Scheme.{u}) (U : X.Opens) : ∀ T : Over U,
      (((Opens.grothendieckTopology ↥X).over U).over T).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun _ ↦ inferInstance
attribute [local instance] sliceLocallyBijective

private theorem limits_overMap {X : Scheme.{u}} {U V : X.Opens} (f : U ⟶ V) :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.overMap.{u} X.ringCatSheaf f) := by
  let B := (overEquiv U).functor
  have : PreservesLimitsOfSize.{u, u}
      (SheafOfModules.overMap.{u} X.ringCatSheaf f ⋙ B) :=
    preservesLimits_of_natIso (overMapCompOverEquiv f).symm
  have : ReflectsLimitsOfSize.{u, u} B := reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves _ B

set_option backward.isDefEq.respectTransparency false in
private theorem fp_equivOver {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsFinitePresentation] :
    ((overEquiv U).functor.obj M).IsFinitePresentation := by
  have (T : U.toScheme.Opens) :
      (Over.post U.overEquivalence.inverse).IsContinuous
        ((Opens.grothendieckTopology ↥U).over T)
        (((Opens.grothendieckTopology X).over U).over
          (U.overEquivalence.inverse.obj T)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.inverse).overPost T)
  exact SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint
    U.overEquivalence.inverse _ (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
private theorem fp_equivOver_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((overEquiv U).inverse.obj M).IsFinitePresentation := by
  have (T : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over T)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj T)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.functor).overPost T)
  exact SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

private theorem fp_overMap {X : Scheme.{u}} {U V : X.Opens} (f : U ⟶ V)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over V)) [M.IsFinitePresentation] :
    ((SheafOfModules.overMap X.ringCatSheaf f).obj M).IsFinitePresentation := by
  let : (Over.map f).Faithful :=
    { map_injective := fun h ↦ by ext; exact congrArg (fun g ↦ g.left) h }
  let : (Over.map f).Full :=
    { map_surjective := fun {A B} g ↦
        ⟨Over.homMk g.left (by
          apply (cancel_mono f).mp
          have hg := g.w
          change g.left ≫ (B.hom ≫ f) = A.hom ≫ f at hg
          simpa only [Category.assoc] using hg), rfl⟩ }
  let J := _root_.Opens.grothendieckTopology X
  have (T : Over U) : (Over.post (X := T) (Over.map f)).IsContinuous
      ((J.over U).over T) ((J.over V).over ((Over.map f).obj T)) := by
    let F := Over.post (X := T) (Over.map f)
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfDownwardsClosed _ F ?_)
      ((GrothendieckTopology.over_map_coverPreserving J f).overPost T)
    intro c d a
    let d' : Over U := Over.mk (d.hom.left ≫ T.hom)
    let c' : Over T := Over.mk (Over.homMk d.hom.left : d' ⟶ T)
    exact ⟨c', Over.isoMk (Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
      (by ext; exact Subsingleton.elim _ _)⟩
  exact SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint
    (Over.map f) _ (SheafOfModules.overMapUnitIso f)

set_option backward.isDefEq.respectTransparency false in
private theorem qc_kernel_slice {X : Scheme.{u}} (U : X.Opens)
    {M N : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsQuasicoherent := by
  let E := overEquiv U
  have := overEquiv_quasiCoherent X U M
  have := overEquiv_quasiCoherent X U N
  have hk := isQuasicoherent_kernel (E.functor.map φ)
  have : (E.functor.obj (kernel φ)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (PreservesKernel.iso E.functor φ).symm hk
  have (T : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over T)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj T)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.functor).overPost T)
  have hback : (E.inverse.obj (E.functor.obj (kernel φ))).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    (E.unitIso.app (kernel φ)).symm hback

set_option backward.isDefEq.respectTransparency false in
private theorem ft_kernel_slice {X : Scheme.{u}} (U : X.Opens)
    {M : SheafOfModules.{u} (X.ringCatSheaf.over U)} [M.IsFinitePresentation]
    (n : ℕ)
    (φ : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶ M)
    [Epi φ] : (kernel φ).IsFiniteType := by
  let E := overEquiv U
  have := fp_equivOver U M
  let e := SheafOfModules.mapFreeIso E.functor (ULift.{u} (Fin n))
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  let ψ := e.hom ≫ E.functor.map φ
  have : Epi ψ := inferInstanceAs (Epi (e.hom ≫ E.functor.map φ))
  have hk := RingedSpace.finitePresentation_kernel_surjection_finiteType
    U.toScheme.toRingedSpace (E.functor.obj M) n ψ inferInstance
  have he : E.functor.obj (kernel φ) ≅ kernel ψ :=
    PreservesKernel.iso E.functor φ ≪≫
      (kernelIsIsoComp e.hom (E.functor.map φ)).symm
  have : (E.functor.obj (kernel φ)).IsFiniteType := finiteType_of_iso.{u, u, u} he.symm
  have hback : (E.inverse.obj (E.functor.obj (kernel φ))).IsFiniteType :=
    finiteType_equivOverInverse U (E.functor.obj (kernel φ))
  exact @finiteType_of_iso.{u, u, u} _ _ _ _ _ _ _ _
    (E.unitIso.app (kernel φ)).symm hback

private theorem fp_free_slice {X : Scheme.{u}} (U : X.Opens) (n : ℕ) :
    (free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n))).IsFinitePresentation := by
  let P := presentationOfIsCokernelFree (ι := PEmpty.{u + 1})
    (0 : free _ ⟶ free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n))) (𝟙 _)
    (by simp) (CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite :=
    ⟨⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩,
      ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩⟩
  exact P.isFinitePresentation

private theorem fp_cokernel_slice {X : Scheme.{u}} (U : X.Opens)
    {Q F : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    [Q.IsFiniteType] [F.IsFinitePresentation] (a : Q ⟶ F) :
    (cokernel a).IsFinitePresentation := by
  let B := overEquiv U
  have : HasFiniteColimits (SheafOfModules.{u} U.toScheme.ringCatSheaf) := inferInstance
  have : (B.functor.obj Q).IsFiniteType := finiteType_equivOver U Q
  have := fp_equivOver U F
  have hc := RingedSpace.isFinitePresentation_cokernel_of_isFiniteType
    U.toScheme.toRingedSpace (B.functor.map a)
  have : (B.functor.obj (cokernel a)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso B.functor a).symm hc
  have hb := fp_equivOver_inverse U (B.functor.obj (cokernel a))
  exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
    (B.unitIso.app (cokernel a)).symm hb

-- The cokernel comparison only needs the categorical exactness of restriction.
private theorem isIso_map_cokernel_desc_of_epi_kernel
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    [HasKernels C] [HasCokernels C] [Abelian D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms]
    [PreservesLimitsOfShape WalkingParallelPair T]
    [PreservesColimitsOfShape WalkingParallelPair T]
    {F M Q : C} (φ : F ⟶ M) (κ : Q ⟶ kernel φ)
    [Epi (T.map φ)] [Epi (T.map κ)] :
    IsIso (T.map (cokernel.desc (κ ≫ kernel.ι φ) φ (by simp))) := by
  let a := κ ≫ kernel.ι φ
  have ha : a ≫ φ = 0 := by simp [a]
  let j := cokernel.desc a φ ha
  change IsIso (T.map j)
  have hzero : T.map (kernel.ι φ) ≫ T.map φ = 0 :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (kernel.condition φ)).trans (T.map_zero _ _))
  have hc : IsColimit (CokernelCofork.ofπ (T.map φ) hzero) :=
    Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (T.map (kernel.ι φ)) hzero)
      ((KernelFork.ofι (kernel.ι φ) (kernel.condition φ)).mapIsLimit
        (kernelIsKernel φ) T)
  have hazero : T.map a ≫ T.map φ = 0 :=
    (T.map_comp _ _).symm.trans ((congrArg T.map ha).trans (T.map_zero _ _))
  have hc' : IsColimit (CokernelCofork.ofπ (T.map φ) hazero) :=
    isCokernelEpiComp hc (T.map κ) (by dsimp [a]; rw [Functor.map_comp])
  have hezero : T.map a ≫ T.map (cokernel.π a) = 0 :=
    (T.map_comp _ _).symm.trans
      ((congrArg T.map (cokernel.condition a)).trans (T.map_zero _ _))
  have hecol : IsColimit (CokernelCofork.ofπ (T.map (cokernel.π a)) hezero) :=
    (CokernelCofork.ofπ (cokernel.π a) (cokernel.condition a)).mapIsColimit
      (cokernelIsCokernel a) T
  have hdesc : T.map (cokernel.π a) ≫ T.map j = T.map φ :=
    (T.map_comp _ _).symm.trans (congrArg T.map (cokernel.π_desc a φ ha))
  let e := hecol.coconePointUniqueUpToIso hc'
  have hj : T.map j = e.hom := by
    apply Cofork.IsColimit.hom_ext hecol
    exact hdesc.trans (hecol.comp_coconePointUniqueUpToIso_hom hc' WalkingParallelPair.one).symm
  rw [hj]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Replace a quasi-coherent module on an affine open by a finitely presented module,
with a map which is an isomorphism on the overlap with the previous open.

Source: Stacks Project, Properties, Lemma 01PI, affine construction
(https://stacks.math.columbia.edu/tag/01PI).
(blueprint: lem-weil-pbc-module-finite-presentation-affine-replacement).

Proof: The intersection K = W intersect V is compact by quasi-separatedness.
Restrict the finite presentation on W to K. The finite affine generators lemma
supplies a map phi from a finite free module on V to H restricted to V, whose
restriction to K is epimorphic. Its kernel is quasi-coherent; restriction preserves
kernels. On K the target is finitely presented, so Modules 01BP makes the
restricted kernel finite type. Extend this quasi-coherent kernel from V to X
using 01PE(3) and its zero map into H. Apply affine finite-type capture to the
extension on K. This gives a finite-type module Q on V and a map kappa into the
kernel of phi, whose restriction to K is an isomorphism. Let a be kappa followed
by the kernel inclusion, and E its cokernel. E is finitely presented by Modules
0H96, because the target of a is finite free. The equation a followed by phi = 0
induces a map j from E to H restricted to V. On K, phi is the cokernel of its
kernel inclusion. Since restricted kappa is an isomorphism, phi is also the
cokernel of restricted a. Restriction preserves the cokernel defining E;
uniqueness of cokernels identifies restricted j with an isomorphism. All steps
allow K empty and rank zero, and no compactness of X is assumed. -/
theorem exists_finitePresentation_affine_replacement
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFinitePresentation] :
    ∃ E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V.1),
      E.IsFinitePresentation ∧ ∃ (j : E ⟶ H.over V.1),
        IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ⊓ V.1 ≤ V.1 from inf_le_right))).map j) := by
  classical
  let R := moduleRings X.toRingedSpace
  let K : X.Opens := W ⊓ V.1
  let f : K ⟶ V.1 := homOfLE inf_le_right
  -- Reuse the slice category structures throughout the kernel and cokernel comparisons.
  let : Abelian (SheafOfModules.{u} (R.over V.1)) := inferInstance
  let : Abelian (SheafOfModules.{u} (R.over K)) := inferInstance
  have : HasEqualizers (SheafOfModules.{u} (R.over V.1)) := inferInstance
  have : HasCoequalizers (SheafOfModules.{u} (R.over V.1)) := inferInstance
  have : HasEqualizers (SheafOfModules.{u} (R.over K)) := inferInstance
  have : HasCoequalizers (SheafOfModules.{u} (R.over K)) := inferInstance
  let T : SheafOfModules.{u} (R.over V.1) ⥤ SheafOfModules.{u} (R.over K) :=
    SheafOfModules.overMap R f
  have : PreservesColimitsOfSize.{u, u} T := inferInstance
  have : PreservesLimitsOfSize.{u, u} T := limits_overMap f
  have : PreservesLimitsOfSize.{0, 0} T := preservesSmallestLimits_of_preservesLimits T
  have : PreservesColimitsOfSize.{0, 0} T := preservesColimitsOfSize_shrink T
  have : T.PreservesZeroMorphisms := inferInstance
  have hK : IsCompact (K : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.1.isOpen V.2.isCompact
  have hfp : (H.over K).IsFinitePresentation := by
    have := fp_overMap (homOfLE (show K ≤ W from inf_le_left)) (H.over W)
    exact (SheafOfModules.isFinitePresentation (R.over K)).prop_of_iso
      ((SheafOfModules.overFunctorMap R
        (homOfLE (show K ≤ W from inf_le_left))).app H) this
  obtain ⟨n, φ, hφ⟩ :=
    exists_finiteType_affine_generators X V K hK inf_le_right H
  have : Epi (T.map φ) := hφ
  have : (H.over V.1).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_over H V.1
  have : (kernel φ).IsQuasicoherent := qc_kernel_slice V.1 φ
  have hTK : (T.obj (H.over V.1)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (R.over K)).prop_of_iso
      ((SheafOfModules.overFunctorMap R f).app H).symm hfp
  have hker : (T.obj (kernel φ)).IsFiniteType := by
    let e := SheafOfModules.mapFreeIso T (ULift.{u} (Fin n))
      (SheafOfModules.overMapUnitIso f).symm
    let ψ := e.hom ≫ T.map φ
    have : Epi ψ := inferInstanceAs (Epi (e.hom ≫ T.map φ))
    have hk := ft_kernel_slice K n ψ
    have he : T.obj (kernel φ) ≅ kernel ψ :=
      PreservesKernel.iso T φ ≪≫ (kernelIsIsoComp e.hom (T.map φ)).symm
    exact finiteType_of_iso.{u, u, u} he.symm
  have : CompactSpace V.1.toScheme := isCompact_iff_compactSpace.mp V.2.isCompact
  obtain ⟨L, hL, _, α, _⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X V.1 inferInstance H
      (kernel φ) (0 : kernel φ ⟶ H.over V.1)
  have : L.IsQuasicoherent := hL
  have : (L.over K).IsFiniteType := by
    let e := ((SheafOfModules.overFunctorMap R f).app L).symm ≪≫ T.mapIso α
    have : (T.obj (kernel φ)).IsFiniteType := hker
    exact finiteType_of_iso.{u, u, u} e.symm
  obtain ⟨Q, hQ, hQft, ι, hι, hιK⟩ :=
    exists_finiteType_affine_capture X V K hK inf_le_right L
  have : Q.IsFiniteType := hQft
  let κ : Q ⟶ kernel φ := ι ≫ α.hom
  have : IsIso (T.map ι) := hιK
  have : IsIso (T.map κ) := by dsimp [κ]; rw [Functor.map_comp]; infer_instance
  have : Epi (T.map κ) := IsIso.epi_of_iso _
  let a : Q ⟶ free (R := R.over V.1) (ULift.{u} (Fin n)) := κ ≫ kernel.ι φ
  have ha : a ≫ φ = 0 := by simp [a]
  let E : SheafOfModules.{u} (R.over V.1) := cokernel a
  let j : E ⟶ H.over V.1 := cokernel.desc a φ ha
  have : (free (R := R.over V.1) (ULift.{u} (Fin n))).IsFinitePresentation :=
    fp_free_slice V.1 n
  have hE : E.IsFinitePresentation := fp_cokernel_slice V.1 a
  refine ⟨E, hE, j, ?_⟩
  exact isIso_map_cokernel_desc_of_epi_kernel T φ κ

end AlgebraicGeometry.Scheme.Modules
