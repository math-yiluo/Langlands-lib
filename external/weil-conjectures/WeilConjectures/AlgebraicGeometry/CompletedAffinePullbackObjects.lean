/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Algebra

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Coherent objects on the completed affine pullback

Source: Stacks Project, Tags 088B, 0887, 02KH and 02O5.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Proper coherent direct image in degree zero (Stacks, Tag 02O5). -/
private theorem coherent_pushforward {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (F : CoherentModules X) :
    RingedSpace.IsCoherent Y.toRingedSpace ((Scheme.Modules.pushforward f).obj F.obj) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := Scheme.Modules.isGrothendieckAbelian X
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp
    F.property
  have : F.obj.IsQuasicoherent := hq.1
  have : F.obj.IsFinitePresentation := by
    have hfp (V : X.affineOpens) : (F.obj.over V.1).IsFinitePresentation := by
      have := IsLocallyNoetherian.component_noetherian V
      have := Scheme.Modules.coherent_affine_sections_finite X F.obj F.property V.1 V.2
      have hp := Module.finitePresentation_of_finite Γ(X, V.1) Γ(F.obj, V.1)
      exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 F.obj hq.1).1
        V.1 V.2).2.mpr hp
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _ F.obj
      X.affineOpens (fun V ↦ V.1) (by
        rw [Opens.coversTop_iff]
        exact iSup_affineOpens_eq_top X) hfp
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage f F.obj 0
  have : ((Scheme.Modules.pushforward f).obj F.obj).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app F.obj) hfp
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mpr
    ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric and coherence part of completed affine base change.
Source: Stacks Project, Tag 088B, completed-base change paragraph; Tags 0887 and 02O5.
(blueprint: lem-weil-pbc-completed-affine-pullback-objects)

Proof: The ring of sections B of the affine open U is Noetherian. Its J(U)-adic
completion R is flat over B. The morphism Spec R to Y is the composite of this flat
map with the affine chart isomorphism and open immersion, so it is flat. On affine
sections, extension of the ideal J along this composite is J(U)R. The Spec global
sections isomorphism identifies its ideal sheaf with the displayed J₀; hence
J.comap g = J₀. The assumed Noetherian R makes S Noetherian, and proper base change
makes p proper and Z Noetherian. Apply formal-system pullback along g and use the
ideal equality to obtain G₀ with its specified underlying diagram. Coherent
pullback along q gives F₀ with its specified underlying module. Proper coherent
direct image gives coherence of p_*F₀. No comparison morphisms are constructed here.
The argument allows J = 0, J = 1, zero rings, zero modules and empty schemes. -/
theorem completedAffine_pullback_objects
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (G : CoherentFormalModule Y J) (F : CoherentModules X) (U : Y.affineOpens)
    [IsNoetherianRing (AdicCompletion (J.ideal U) Γ(Y, U.1))] :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let I := (J.ideal U).map (algebraMap B R)
    let J₀ := Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let Z := pullback f g
    let p : Z ⟶ S := pullback.snd f g
    ∃ (G₀ : CoherentFormalModule S J₀) (F₀ : CoherentModules Z)
      (_hD : RingedSpace.IsCoherent S.toRingedSpace
        ((Scheme.Modules.pushforward p).obj F₀.obj)),
      G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g ∧
      F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj ∧
      Flat g ∧ J.comap g = J₀ := by
  classical
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let S := Spec (CommRingCat.of R)
  let I := (J.ideal U).map (algebraMap B R)
  let J₀ := Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
    U.2.isoSpec.inv ≫ U.1.ι
  let Z := pullback f g
  let p : Z ⟶ S := pullback.snd f g
  change ∃ (G₀ : CoherentFormalModule S J₀) (F₀ : CoherentModules Z)
      (_hD : RingedSpace.IsCoherent S.toRingedSpace
        ((Scheme.Modules.pushforward p).obj F₀.obj)),
      G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g ∧
      F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj ∧
      Flat g ∧ J.comap g = J₀
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap B R))) :=
    Flat.SpecMap_iff.mpr ((RingHom.flat_algebraMap_iff).mpr inferInstance)
  have hg : Flat g := by dsimp only [g]; infer_instance
  have hI : J.comap g = J₀ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    change (J.comap (Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ U.2.fromSpec)).ideal
        ⟨⊤, isAffineOpen_top S⟩ = _
    rw [Scheme.IdealSheafData.ideal_top_comap_specMap_fromSpec,
      Scheme.IdealSheafData.ideal_top_ofIdealTop]
    rfl
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : IsProper p := inferInstance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian Z := {}
  have hP := (exists_formalSystemsPullback g J).1
  rw [hI] at hP
  obtain ⟨P, _, hP, _, _⟩ := hP
  obtain ⟨_, C, _, hC, _⟩ :=
    (exists_formalSystemsPullback (pullback.fst f g) (J.comap f)).1
  refine ⟨P.obj G, C.obj F, coherent_pushforward p (C.obj F), ?_, ?_, hg, hI⟩
  · exact congrArg (fun T ↦ T.obj G) hP
  · exact congrArg (fun T ↦ T.obj F) hC


end AlgebraicGeometry
