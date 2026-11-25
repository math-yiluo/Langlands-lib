/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

set_option linter.privateModule false

/-! # Ambient pro-etale adjunction for the actual constant coefficient sheaf

## References

* Stacks Project, Tags 09BM and 09AH
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientEquivalence (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := ProEt.topology X) (K := ProEt.topology X) (S := R) (R := S)
    (CategoryTheory.Equivalence.refl (C := X.ProEt)) c.hom c.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [S.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) c.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [R.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) c.hom_inv_id)

private noncomputable def coefficientTransport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModules X S ≌
      proEtaleRingModules X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  coefficientEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def directImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleDirectImage f R S c ≅
      (coefficientTransport f R S c).functor ⋙ proEtaleRingedDirectImage f R := by
  let φ : proEtaleModuleCoefficients R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (proEtaleModuleCoefficients
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) :=
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⟶
        proEtaleModuleCoefficients S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom
  exact (SheafOfModules.pushforwardComp (F := proEtaleBaseChange f)
    (G := 𝟭 X.ProEt) (K' := ProEt.topology X)
    (R' := proEtaleModuleCoefficients S) φ ψ).symm

private noncomputable def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleModuleInverseImage f R ⊣ proEtaleRingedDirectImage f R) :
    proEtaleRingModulePullback f R S c ≅
      proEtaleModuleInverseImage f R ⋙ (coefficientTransport f R S c).inverse :=
  (proEtaleRingModuleAdjunction f R S c).leftAdjointUniq
    ((a.comp (coefficientTransport f R S c).symm.toAdjunction).ofNatIsoRight
      (directImageComparison f R S c).symm)

attribute [local irreducible] proEtaleRingModuleAdjunction

-- The pointwise kernel functor's identity proof needs more unfolding heartbeats.
private noncomputable def pointwiseKernel
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D where
  obj X := kernel (η.app X)
  map f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

private noncomputable def pointwiseKernelIso
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : kernel η ≅ pointwiseKernel η := by
  let ev := CategoryTheory.evaluation C D
  refine NatIso.ofComponents
    (fun X ↦ asIso (kernelComparison η (ev.obj X))) ?_
  intro X Y f
  apply (cancel_mono (kernel.ι (η.app Y))).mp
  simp only [Category.assoc]
  change (kernel η).map f ≫ kernelComparison η (ev.obj Y) ≫ kernel.ι (η.app Y) =
    kernelComparison η (ev.obj X) ≫
      kernel.map (η.app X) (η.app Y) (F.map f) (G.map f)
        (η.naturality f).symm ≫ kernel.ι (η.app Y)
  have hc (X : C) : kernelComparison η (ev.obj X) ≫ kernel.ι (η.app X) =
      (kernel.ι η).app X := kernelComparison_comp_ι η (ev.obj X)
  rw [hc, kernel.lift_ι, ← Category.assoc, hc]
  exact (kernel.ι η).naturality f

private noncomputable def supportKernelIso {T U : Scheme.{u}} (j : U ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    kernel (C := proEtaleRingModules T (proEtaleConstantRing T A) ⥤
      proEtaleRingModules T (proEtaleConstantRing T A))
        (sfConstantModuleAdjunction j A).unit ≅ sfIntrinsicSectionsWithSupport j A :=
  pointwiseKernelIso (sfConstantModuleAdjunction j A).unit

end AlgebraicGeometry.Scheme
