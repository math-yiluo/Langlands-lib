/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPullComparison
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem formalPushforward_coherent {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (F : CoherentModules X) :
    RingedSpace.IsCoherent Y.toRingedSpace ((Scheme.Modules.pushforward f).obj F.obj) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Scheme.Modules.isGrothendieckAbelian X
  have hcoh : F.obj.IsFinitePresentation := by
    have hq :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp F.property
    have : F.obj.IsQuasicoherent := hq.1
    have hs := (Scheme.Modules.isCoherent_pushforward_of_isFinite (𝟙 X) F.obj F.property).2
    have hloc (U : X.affineOpens) : (F.obj.over U.1).IsFinitePresentation := by
      have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      have : Module.Finite Γ(X, U.1) Γ(F.obj, U.1) := hs U.1 U.2 |>.2
      exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 F.obj inferInstance).1
        U.1 U.2).2.mpr (Module.finitePresentation_of_finite Γ(X, U.1) Γ(F.obj, U.1))
    exact SheafOfModules.IsFinitePresentation.of_coversTop F.obj (fun U : X.affineOpens ↦ U.1)
      ((Opens.coversTop_iff X _).mpr
        (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)))
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp F.property
  have := hq.1
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage f F.obj 0
  have hp : ((Scheme.Modules.pushforward f).obj F.obj).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app F.obj) hfp
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
    ⟨inferInstance, inferInstance⟩

/-- Core comparison and termwise annihilation needed for the formal push-pull theorem.
Source: Stacks Project, Cohomology of Schemes, Lemma 088B and Remark 0888.
(blueprint: lem-weil-pbc-formal-systems-push-pull-core)
The construction of the comparison morphism, coherence of the pushforward, and the
uniform termwise annihilation are the affine formal-functions and completion argument
of Lemma 088B. -/
theorem exists_formalSystemsPushPull_core {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (_hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (_β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj) :
    ∃ h : RingedSpace.IsCoherent Y.toRingedSpace
        ((Scheme.Modules.pushforward f).obj F.obj),
      ∃ α : G ⟶ (completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
        ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2
            (kernel (α.hom.app (op n)))) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower K.toModulesι t).2
            (cokernel (α.hom.app (op n)))) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  have h := formalPushforward_coherent f F
  obtain ⟨κ, α, hκ, hα⟩ := exists_formalSystemsPushPull_comparison J f adj G F _β h
  refine ⟨h, α, ?_⟩
  have ha := formalSystemsPushPull_affine_annihilation J K f _hV adj G F _β h κ α hκ hα
  exact (List.TFAE.out (coherentFormalModule_annihilated_iff Y J K G
    ((completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩) α) 2 1).mp ha

end AlgebraicGeometry
