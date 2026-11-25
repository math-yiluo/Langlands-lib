/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.PseudoCoherentSummand
import WeilConjectures.AlgebraicGeometry.DerivedTensorVanishingRetract
import WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import all WeilConjectures.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude
import all WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.OpenImmersionTensorVanishingTest
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Direct summands of perfect complexes

Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteTorAmplitude_of_open_model (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (S.presheaf.obj (.op U)))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (W : S.Opens) (hUW : U ≤ W)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (hTor : HasFiniteTorDimension W.toScheme ((derivedPullback W.ι).obj K)) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (ModuleCat.{u} (S.presheaf.obj (.op U))) a b (DerivedCategory.Q.obj P) := by
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  let Z := Spec (S.presheaf.obj (.op U))
  let j : Z ⟶ W.toScheme := hU.isoSpec.inv ≫ S.homOfLE hUW
  let RW : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Modules.restrictFunctor W.ι
  have : RW.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits RW := by
    dsimp [RW, Modules.restrictFunctor]
    infer_instance
  have : RW.IsLeftAdjoint := by
    let H : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) := Modules.pushforward W.ι
    exact (show RW ⊣ H from Modules.restrictAdjunction W.ι).isLeftAdjoint
  let RJ : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) := Modules.restrictFunctor j
  have : RJ.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits RJ := by
    dsimp [RJ, Modules.restrictFunctor]
    infer_instance
  have : RJ.IsLeftAdjoint := by
    let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Modules.pushforward j
    exact (show RJ ⊣ H from Modules.restrictAdjunction j).isLeftAdjoint
  let A := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let E : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  have : E.functor.Additive := ⟨by intros; rfl⟩
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
    Modules.restrictFunctor hU.isoSpec.inv
  have : T.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits T := by
    dsimp [T, Modules.restrictFunctor]
    infer_instance
  let H : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.pushforward hU.isoSpec.inv
  have adjT : T ⊣ H := Modules.restrictAdjunction hU.isoSpec.inv
  have : T.IsLeftAdjoint := adjT.isLeftAdjoint
  let B := E.functor ⋙ T
  have : B.Additive := inferInstance
  have : PreservesFiniteLimits B := comp_preservesFiniteLimits _ _
  have : B.IsLeftAdjoint := (E.toAdjunction.comp adjT).isLeftAdjoint
  let T' : SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.restrictFunctor hU.isoSpec.hom
  have : T'.Additive := ⟨by intros; rfl⟩
  have : HasBinaryBiproducts
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let L : ModuleCat.{u} (S.presheaf.obj (.op U)) ⥤
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
    tilde.functor (S.presheaf.obj (.op U))
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : (affinePerfectSheafification S U hU).Additive := by
    change (L ⋙ T' ⋙ E.inverse).Additive
    infer_instance
  obtain ⟨C, hC, ⟨eC⟩⟩ := AlgebraicGeometry.exists_kFlat_model S K
  obtain ⟨eCW⟩ := AlgebraicGeometry.open_pullback_model_iso W.ι C hC
  let eW : (derivedPullback W.ι).obj K ≅ RW.mapDerivedCategory.obj K :=
    (derivedPullback W.ι).mapIso eC.symm ≪≫ eCW ≪≫
      (RW.mapDerivedCategoryFactors.app C).symm ≪≫ RW.mapDerivedCategory.mapIso eC
  let θ : RW ⋙ RJ ≅ A ⋙ B := by
    exact (Modules.restrictFunctorComp j W.ι).symm ≪≫
      Modules.restrictFunctorCongr (by simp [j, Category.assoc]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv U.ι ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U).symm
        (Modules.restrictFunctor hU.isoSpec.inv)
  obtain ⟨eP⟩ := hP
  let e : RJ.mapDerivedCategory.obj ((derivedPullback W.ι).obj K) ≅
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (S.presheaf.obj (.op U)))
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) _ _ _ _
          (tilde.functor (S.presheaf.obj (.op U))) ⟨fun _ _ ↦ tilde.map_zero⟩
          (ComplexShape.up ℤ)).obj P) := by
    exact RJ.mapDerivedCategory.mapIso eW ≪≫
      ((Functor.mapDerivedCategoryCompIso RW RJ).app K) ≪≫
      (Functor.mapDerivedCategoryNatIso θ).app K ≪≫
      (Functor.mapDerivedCategoryCompIso A B).symm.app K ≪≫
      B.mapDerivedCategory.mapIso eP ≪≫ B.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso
          (F := affinePerfectSheafification S U hU) (G := B) (H := L)
          (affine_cancel S U hU) (.up ℤ)).app P)
  obtain ⟨a, b, hab, hvan⟩ := hTor
  refine ⟨a, b, hab, (affine_torAmplitude_iff (S.presheaf.obj (.op U)) P a b hab).mp ?_⟩
  intro G i hi
  have hv := openImmersion_tensor_vanishing_test j
    ((derivedPullback W.ι).obj K) G i (hvan ((Modules.pushforward j).obj G) i hi)
  obtain ⟨D, hD, ⟨eD⟩, hz⟩ := hv
  exact ⟨D, hD, ⟨eD ≪≫ e⟩, hz⟩

private theorem perfect_of_pc_tor (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ W : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K)
    (hTor : HasLocallyFiniteTorDimension S K) : IsPerfect S K := by
  intro x
  obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hK x
  obtain ⟨W, hxW, a, c, hac, hW⟩ := hTor x
  obtain ⟨V, hV, hxV, hVUW⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ W) ⟨hxU, hxW⟩
  have hVU : V ≤ U := hVUW.trans inf_le_left
  have hVW : V ≤ W := hVUW.trans inf_le_right
  let F := SheafOfModules.overMap.{u} (moduleRings S.toRingedSpace) (homOfLE hVU)
  let G := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (PV.X i) := by
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
  have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
    obtain ⟨r, ⟨e⟩⟩ := hf i
    let ef : F.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r))) ≅
        SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
      (asIso (Limits.sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦
        SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)))).symm ≪≫
          Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso
            (R := moduleRings S.toRingedSpace) (homOfLE hVU))
    exact ⟨r, ⟨F.mapIso e ≪≫ ef⟩⟩
  have : Limits.PreservesFiniteLimits (G ⋙ F) := Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits (G ⋙ F) := Limits.comp_preservesFiniteColimits _ _
  let eV : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) V).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj PV :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u}
        (moduleRings S.toRingedSpace) (homOfLE hVU))).symm.app K ≪≫
      (Functor.mapDerivedCategoryCompIso G F).symm.app K ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
        F.mapDerivedCategoryFactors.app P
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_finiteFree_model S V hV PV hbV hfV
  let R := S.presheaf.obj (.op V)
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  have hMpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    ⟨M, b, hMb, hMf, ⟨Iso.refl _⟩⟩
  let eKM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
  have hMtor := finiteTorAmplitude_of_open_model S V hV K M ⟨eKM⟩
    W hVW ⟨a, c, hac, hW⟩
  obtain ⟨E, hEb, hEf, hEp, ⟨eE⟩⟩ :=
    DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
      (DerivedCategory.Q.obj M) hMpc hMtor
  let T := (affinePerfectSheafification S V hV).mapHomologicalComplex (.up ℤ)
  obtain ⟨D, _, ⟨c⟩⟩ := affine_localized_derived_sheafification S V hV
  refine ⟨V, hxV, T.obj E, affine_projective_strictlyPerfect S V hV E hEb hEf hEp, ?_⟩
  exact ⟨eKM ≪≫ (c.app M).symm ≪≫ D.mapIso eE.symm ≪≫ c.app E⟩

/-- A direct summand of a perfect complex is perfect, and the complementary summand
is perfect as well. First, `lem-pc-perfect-pseudo-coherent-locally-finite-tor` gives
pseudo-coherence and Tor amplitude in an interval on a neighbourhood of each point.
Second, `lem-pc-pseudo-coherent-summand` gives pseudo-coherence of both summands.
Third, both summands are retracts of K; derived pullback, derived tensor and
homology preserve these retracts. The proved
`lem-pc-derived-tensor-vanishing-retract` passes the same local Tor interval
to both summands (Tag 08CK). Finally,
`lem-pc-pseudo-coherent-locally-finite-tor-perfect` constructs perfect models
on affine subopens of the Tor neighbourhoods and gives perfectness on X.
Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand). -/
theorem perfect_of_directSum
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPerfect X K) :
    IsPerfect X L ∧ IsPerfect X M := by
  classical
  let hOpen (U : X.Opens) :
      HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    (hasDerivedCategory_of_equivalence (Modules.overEquiv U).symm).some
  let : ∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := hOpen
  obtain ⟨hpc, htor⟩ := perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension X K hK
  obtain ⟨hLpc, hMpc⟩ := pseudoCoherent_of_isIso_biproduct X K L M h hpc
  obtain ⟨e⟩ := h
  let rL : Retract L K :=
    { i := biprod.inl ≫ e.inv
      r := e.hom ≫ biprod.fst
      retract := by simp [Category.assoc] }
  let rM : Retract M K :=
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp [Category.assoc] }
  have tor_of_retract (N : schemeDerivedCategory X) (r : Retract N K) :
      HasLocallyFiniteTorDimension X N := by
    intro x
    obtain ⟨U, hx, a, b, hab, hU⟩ := htor x
    refine ⟨U, hx, a, b, hab, ?_⟩
    intro G i hi
    exact schemeDerivedTensorCohomologyVanishes_of_retract U.toScheme _ _
      (r.map (derivedPullback U.ι)) G i (hU G i hi)
  exact ⟨perfect_of_pc_tor X L hLpc
      (tor_of_retract L rL),
    perfect_of_pc_tor X M hMpc
      (tor_of_retract M rM)⟩

end AlgebraicGeometry.Scheme
