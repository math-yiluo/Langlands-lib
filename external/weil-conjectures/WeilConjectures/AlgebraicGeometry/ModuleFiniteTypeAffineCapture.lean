/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite-type capture on a compact open inside an affine open

Source: Stacks Project, Properties, Lemma 01PF, affine finite-numerator step.
(blueprint: lem-weil-pbc-module-finite-type-affine-capture).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

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
  infer_instance

/-- A quasi-coherent module on an affine open has a finite-type submodule agreeing
with it on a compact open where it is already of finite type.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), the affine
finite-numerator argument, and Lemma 01PB (label lemma-finite-type-module).
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-finite-type-affine-capture).

Proof: Choose a finite free-module map on V which becomes epimorphic on K by
exists_finiteType_affine_generators, the finite-numerator step of Lemma 01PF.
Take Q to be its abelian image, constructed as the kernel of its cokernel map.
The equivalence between the slice site Over V and modules on V.toScheme preserves
kernels and cokernels and quasi-coherence in both directions. The source-library
kernel and cokernel closure theorems therefore make Q quasi-coherent. The finite
standard basis maps to global generators of Q through the epimorphic image
factorization; their local-generators data makes Q of finite type. The image
inclusion is a monomorphism. Restriction to K preserves finite limits, hence
monomorphisms. The restricted finite free map factors through this restricted
inclusion, so its epimorphicity makes the inclusion epimorphic too. A morphism
which is both mono and epi in the abelian category of module sheaves is an
isomorphism. This argument allows K empty, n = 0, and K = V. No arbitrary witness
is used to define Q: its abelian image is an existing categorical construction. -/
theorem exists_finiteType_affine_capture
    (X : Scheme.{u}) (V : X.affineOpens) (K : X.Opens)
    (hK : IsCompact (K : Set X)) (hKV : K ≤ V.1)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over K).IsFiniteType] :
    ∃ Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V.1),
      Q.IsQuasicoherent ∧ Q.IsFiniteType ∧ ∃ (ι : Q ⟶ H.over V.1),
        Mono ι ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hKV)).map ι) := by
  obtain ⟨n, φ, hφ⟩ := exists_finiteType_affine_generators X V K hK hKV H
  let R := moduleRings X.toRingedSpace
  let T := SheafOfModules.overMap R (homOfLE hKV)
  have : (H.over V.1).IsQuasicoherent := SheafOfModules.isQuasicoherent_over H V.1
  have hqc := quasiCoherent_slice_image V.1 φ
  have hft := finiteType_image_free_slice X V.1 n φ
  refine ⟨Abelian.image φ, hqc, hft, Abelian.image.ι φ, inferInstance, ?_⟩
  have : Epi (T.map φ) := hφ
  have : T.PreservesMonomorphisms := by
    let B := (overEquiv K).functor
    have : Limits.PreservesLimitsOfSize.{u, u} (T ⋙ B) :=
      Limits.preservesLimits_of_natIso (overMapCompOverEquiv (homOfLE hKV)).symm
    have : Limits.ReflectsLimitsOfSize.{u, u} B :=
      Limits.reflectsLimits_of_reflectsIsomorphisms
    have : Limits.PreservesLimitsOfSize.{u, u} T :=
      Limits.preservesLimits_of_reflects_of_preserves _ B
    exact preservesMonomorphisms_of_preservesLimitsOfShape T
  have : Mono (T.map (Abelian.image.ι φ)) := T.map_mono _
  have : Epi (T.map (Abelian.image.ι φ)) :=
    epi_of_epi_fac (by rw [← T.map_comp, Abelian.image.fac])
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.Scheme.Modules
