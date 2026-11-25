/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModel


public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
public import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModelExtension
public import WeilConjectures.AlgebraicGeometry.NoetherianProperBoundedCoherentImage
public import WeilConjectures.AlgebraicGeometry.ProperFlatCohomologyData
public import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProperCohomologyFiniteFreeResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent

/-! # Descent-first bounded flat Čech models

Descend the proper morphism and relatively flat coefficient module to a Noetherian
stage, resolve one universal ordinary Čech model there, and pull back the same
model and resolution. The comparisons are existential homology isomorphisms.

Source: Stacks Project, Tags 0A1H, 0B91 and 064U.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of module sheaves is additive pointwise. -/
local instance descentCechEvaluationAdditive (Y : Scheme.{u}) (V : Y.Opens) :
    (SheafOfModules.evaluation.{u} Y.ringCatSheaf (Opposite.op V)).Additive := ⟨rfl⟩

/-- The Noetherian algebra step needs no geometric derived base-change theorem.
It returns a real chain map and can therefore be used in any derived localization. -/
theorem noetherian_boundedFlat_finiteFreeResolution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (ha : C.IsStrictlyGE a) (hb : C.IsStrictlyLE b)
    (hflat : ∀ n : ℤ, Module.Flat R (C.X n))
    (hfin : ∀ n : ℤ, Module.Finite R (C.homology n)) :
    ∃ (F : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ),
      F.IsStrictlyLE d ∧
      (∀ n : ℤ, Module.Free R (F.X n) ∧ Module.Finite R (F.X n)) ∧
      ∃ e : F ⟶ C, QuasiIso e := by
  let : HasDerivedCategory.{u} (ModuleCat.{u} R) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u} R)
  have := ha
  have := hb
  have hbounded : DerivedCategory.TStructure.t.bounded (DerivedCategory.Q.obj C) :=
    ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  have hfinite (n : ℤ) : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (DerivedCategory.Q.obj C)) := by
    let : Module.Finite R
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n).obj C) := hfin n
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app C).symm.toLinearEquiv
  have hTor : DerivedCategory.finiteTorAmplitude (ModuleCat.{u} R)
      (DerivedCategory.Q.obj C) :=
    ⟨a, b, DerivedCategory.torAmplitudeIn_Q_obj_of_flat C a b
      (fun n ↦ (ModuleCat.flat_iff_flat (C.X n)).2 (hflat n))⟩
  obtain ⟨P, l, d, _, hPd, hP, ⟨eP⟩⟩ :=
    DerivedCategory.isPerfect_of_finiteTorAmplitude hbounded hfinite hTor
  have := hPd
  have : ∀ n : ℤ, Module.Projective R (P.X n) := fun n ↦ (hP n).1
  have : ∀ n : ℤ, Projective (P.X n) := fun n ↦ inferInstance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  obtain ⟨p, hp⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P C eP.inv
  have hpi : QuasiIso p :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) p).1 (by
      rw [hp]
      infer_instance)
  obtain ⟨F, hFd, hF, e, he⟩ :=
    CochainComplex.exists_finiteFree_model_of_finite_projective R P d hPd
      (fun n ↦ (hP n).2) (fun n ↦ (hP n).1)
  have := he
  have := hpi
  exact ⟨F, d, hFd, hF, e ≫ p, inferInstance⟩

theorem noetherian_boundedFlat_isPseudoCoherent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (ha : C.IsStrictlyGE a) (hb : C.IsStrictlyLE b)
    (hflat : ∀ n : ℤ, Module.Flat R (C.X n))
    (hfin : ∀ n : ℤ, Module.Finite R (C.homology n)) :
    DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj C) := by
  obtain ⟨F, d, hFd, hF, e, he⟩ :=
    noetherian_boundedFlat_finiteFreeResolution R C a b ha hb hflat hfin
  have := he
  exact ⟨F, d, hFd, hF, ⟨asIso (DerivedCategory.Q.map e)⟩⟩


/-- Flatness over the identity of a quasi-coherent module survives arbitrary
ordinary pullback; the stalk calculation uses extension of scalars. -/
theorem ordinary_pullback_flatOver_identity {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] (h : M.IsFlatOver (𝟙 Y)) :
    ((Modules.pullback g).obj M).IsFlatOver (𝟙 X) := by
  classical
  let F := Modules.pullback g
  let T := Scheme.Modules.tensorPullback g
  let c : T ≅ F := (Classical.choice (nonempty_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  apply relative_flat_of_stalks (𝟙 X)
  intro x
  let R := Y.presheaf.stalk (g x)
  let S := X.presheaf.stalk x
  let N := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (g x)).obj M
  have hN : Module.Flat R N := by
    let : Algebra (Y.presheaf.stalk ((𝟙 Y) (g x)))
      (Y.presheaf.stalk (g x)) := (RingHom.id R).toAlgebra
    have hn := relative_flat_module_stalk (𝟙 Y) M h (g x)
      (by rw [Scheme.Hom.stalkMap_id]; rfl)
    exact (Module.Flat.equiv_iff
      (((ModuleCat.restrictScalarsId R).app N).toLinearEquiv)).mp hn
  let : Algebra R S := (g.stalkMap x).hom.toAlgebra
  have he : Module.Flat S ((ModuleCat.extendScalars (g.stalkMap x).hom).obj N) := by
    have := hN
    change Module.Flat S (TensorProduct R S N)
    infer_instance
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso g x
  let k := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso (c.app M).symm ≪≫
    e.app M
  have : Module.Flat S ((Y.toRingedSpace.moduleStalkFunctor (g x) ⋙
      ModuleCat.extendScalars (g.stalkMap x).hom).obj M) := he
  have hp : Module.Flat S ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (F.obj M)) := Module.Flat.of_linearEquiv k.toLinearEquiv
  rw [Scheme.Hom.stalkMap_id]
  exact (Module.Flat.equiv_iff
    (((ModuleCat.restrictScalarsId S).app
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (F.obj M))).toLinearEquiv)).mpr hp

private theorem finiteFreeTerm_flat {Y : Scheme.{u}}
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (h : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian Y.ringCatSheaf
  obtain ⟨r, ⟨e⟩⟩ := h
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hf).2

/-- Pull back the fixed flat Čech model and its actual finite-free resolution. -/
theorem ordinary_pullback_model_resolution {X Y : Scheme.{u}} (g : X ⟶ Y)
    (C Q : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : C.IsStrictlyGE 0) (hle : C.IsStrictlyLE d)
    (hflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 Y))
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hQle : Q.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) :
    let F := (Modules.pullback g).mapHomologicalComplex (.up ℤ)
    CochainComplex.IsStrictlyGE (F.obj C) 0 ∧ CochainComplex.IsStrictlyLE (F.obj C) d ∧
    (∀ n : ℤ, ((F.obj C).X n).IsFlatOver (𝟙 X)) ∧
    (∀ n : ℤ, ((F.obj C).X n).IsQuasicoherent) ∧
    CochainComplex.IsStrictlyLE (F.obj Q) d ∧
    (∀ n : ℤ, ∃ r : ℕ,
      Nonempty ((F.obj Q).X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) ∧ QuasiIso (F.map e) := by
  have : C.IsStrictlyGE (0 : ℤ) := hge
  have : C.IsStrictlyLE (d : ℤ) := hle
  have : Q.IsStrictlyLE (d : ℤ) := hQle
  let F := (Modules.pullback g).mapHomologicalComplex (.up ℤ)
  have hkC : CochainComplex.IsKFlatTensor (R := Y.sheaf) C :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace Y.toRingedSpace C
      ⟨d, fun n hn ↦ C.isZero_of_isStrictlyLE d n hn⟩
      (fun n ↦ isFlat_of_affineFlatOver_identity (C.X n) (hflat n))
  have hkQ : CochainComplex.IsKFlatTensor (R := Y.sheaf) Q :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace Y.toRingedSpace Q
      ⟨d, fun n hn ↦ Q.isZero_of_isStrictlyLE d n hn⟩
      (fun n ↦ finiteFreeTerm_flat (Q.X n) (hfree n))
  have hQ : QuasiIso (F.map e) := by
    have : (tensorPullback g).Additive :=
      (Classical.choice (nonempty_tensorPullbackAdjunction g)).left_adjoint_additive
    have hq := tensorPullback_quasiIso_of_isKFlat g e hkQ hkC he
    let c : tensorPullback g ≅ Modules.pullback g :=
      (Classical.choice (nonempty_tensorPullbackAdjunction g)).leftAdjointUniq
        (pullbackPushforwardAdjunction g)
    let ec := NatIso.mapHomologicalComplex c (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ec.app Q) (ec.app C) (ec.hom.naturality e).symm)).mp hq
  refine ⟨inferInstance, inferInstance, ?_, ?_, inferInstance, ?_, hQ⟩
  · intro n
    have := hqc n
    exact ordinary_pullback_flatOver_identity g (C.X n) (hflat n)
  · intro n
    have := hqc n
    change ((Modules.pullback g).obj (C.X n)).IsQuasicoherent
    infer_instance
  · intro n
    obtain ⟨r, ⟨er⟩⟩ := hfree n
    exact ⟨r, ⟨(Modules.pullback g).mapIso er ≪≫ pullbackFreeIso g _⟩⟩


/-- The Noetherian part uses the already universal ordinary model; no canonical
scheme derived base-change morphism occurs in the statement or proof. -/
theorem noetherian_cohomology_model_sections_isPseudoCoherent
    {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f] [IsLocallyNoetherian T]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsFinitePresentation]
    (U : T.Opens) [IsAffine U.toScheme]
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hge : C.IsStrictlyGE 0) (hle : C.IsStrictlyLE d)
    (hflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hcomp :
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))) :
    (letI : CommRing (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(U.toScheme, ⊤));
      letI := HasDerivedCategory.standard
        (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)));
      DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
        (((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex
          (.up ℤ)).obj C))) := by
  classical
  let A := U.toScheme.ringCatSheaf.obj.obj (.op ⊤)
  let : CommRing A := inferInstanceAs (CommRing Γ(U.toScheme, ⊤))
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let : IsNoetherianRing Γ(U.toScheme, ⊤) := IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top U.toScheme⟩
  let : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing Γ(U.toScheme, ⊤))
  let G := SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)
  let : G.Additive := ⟨rfl⟩
  let K : CochainComplex (ModuleCat.{u} A) ℤ := (G.mapHomologicalComplex (.up ℤ)).obj C
  have : C.IsStrictlyGE (0 : ℤ) := hge
  have : C.IsStrictlyLE (d : ℤ) := hle
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  refine noetherian_boundedFlat_isPseudoCoherent A K 0 d inferInstance inferInstance ?_ ?_
  · intro n
    change Module.Flat Γ(U.toScheme, ⊤) Γ(C.X n, ⊤)
    convert hflat n ⟨⊤, isAffineOpen_top U.toScheme⟩
      ⟨⊤, isAffineOpen_top U.toScheme⟩ le_rfl using 1
    ext r m
    change r • m = ((Scheme.Hom.appLE (𝟙 U.toScheme) ⊤ ⊤ le_rfl).hom r) • m
    congr 1
    simp [Scheme.Hom.appLE]; rfl
  · intro n
    by_cases hn : n < 0
    · have hz : IsZero (K.homology n) :=
        ShortComplex.isZero_homology_of_isZero_X₂ _ (K.isZero_of_isStrictlyGE 0 n hn)
      have := ModuleCat.subsingleton_of_isZero hz
      infer_instance
    · let q := n.toNat
      have hqn : (q : ℤ) = n := Int.toNat_of_nonneg (by omega)
      let Y := Limits.pullback f U.ι
      let a : Y ⟶ X := pullback.fst f U.ι
      let b : Y ⟶ U.toScheme := pullback.snd f U.ι
      let : IsGrothendieckAbelian.{u} Y.Modules := Scheme.Modules.isGrothendieckAbelian Y
      have : HasInjectiveResolutions Y.Modules := inferInstance
      have : ((Modules.pullback a).obj F).IsFinitePresentation := inferInstance
      have : IsProper b := inferInstance
      have : Module.Finite Γ(U.toScheme, ⊤)
          Γ((higherDirectImage b q).obj ((Modules.pullback a).obj F), ⊤) :=
        finite_sections_proper_on_affine b ((Modules.pullback a).obj F) q
      let : Module.Finite A (G.obj
          ((higherDirectImage b q).obj ((Modules.pullback a).obj F))) := by
        change Module.Finite Γ(U.toScheme, ⊤)
          Γ((higherDirectImage b q).obj ((Modules.pullback a).obj F), ⊤)
        infer_instance
      obtain ⟨ec⟩ := hcomp (𝟙 U.toScheme) a b (by
        simpa using (IsPullback.of_hasPullback f U.ι)) q
      let eId := (NatIso.mapHomologicalComplex (Modules.pullbackId U.toScheme) (.up ℤ)).app C ≪≫
        (Functor.mapHomologicalComplexIdIso U.toScheme.Modules (.up ℤ)).app C
      let eH : C.homology n ≅ (higherDirectImage b q).obj ((Modules.pullback a).obj F) :=
        eqToIso (congrArg (fun z ↦ C.homology z) hqn.symm) ≪≫
        ((HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso eId).symm ≪≫ ec
      obtain ⟨eΓ⟩ := nonempty_affineSectionsHomologyIso U.toScheme C hqc n
      let eK := eΓ ≪≫ G.mapIso eH
      exact Module.Finite.equiv eK.symm.toLinearEquiv


/-- Noetherian stage of the exact root-facing Čech-model interface. -/
theorem noetherian_exists_proper_flat_cech_model
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [IsLocallyNoetherian T]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      (∃ e : Q ⟶ C, QuasiIso e) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  obtain ⟨U, C, d, ht, hU, hge, hle, hflat, hqc, hcomp⟩ :=
    exists_proper_flat_cohomology_model_data f F hF t
  have : IsAffine U.toScheme := hU
  have hpc := noetherian_cohomology_model_sections_isPseudoCoherent
    f F U C d hge hle hflat hqc hcomp
  obtain ⟨Q, hQle, hQfree, e, he⟩ :=
    exists_proper_cohomology_finite_free_resolution U C d hle hqc hpc
  exact ⟨U, C, Q, d, ht, hU, hge, hle, hflat, hqc, hQle, hQfree, ⟨e, he⟩, hcomp⟩


/-- The same transport when the universal model lives on a stage neighbourhood.
The morphism p still has its original target; only the complex's base is local. -/
theorem universal_ordinary_neighbourhood_model_transfer
    {X Y Z T U B T₀ : Scheme.{u}} (f : X ⟶ T) (p : Y ⟶ T₀)
    (u : U ⟶ T) (g₀ : U ⟶ B) (s : B ⟶ T₀)
    (a : Z ⟶ X) (q : Z ⟶ Y) (b : Z ⟶ U)
    (hX : IsPullback a b f u) (hY : IsPullback q b p (g₀ ≫ s))
    (F : X.Modules) (M : Y.Modules)
    (eM : (Modules.pullback q).obj M ≅ (Modules.pullback a).obj F)
    (C₀ : CochainComplex B.Modules ℤ)
    (hcomp : ∀ {S W : Scheme.{u}} (g : S ⟶ B) (v : W ⟶ Y) (h : W ⟶ S)
      [HasInjectiveResolutions W.Modules], IsPullback v h p (g ≫ s) → ∀ n : ℕ,
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C₀).homology n ≅
        (higherDirectImage h n).obj ((Modules.pullback v).obj M))) :
    ∀ {S W : Scheme.{u}} (g : S ⟶ U) (v : W ⟶ X) (h : W ⟶ S)
      [HasInjectiveResolutions W.Modules], IsPullback v h f (g ≫ u) → ∀ n : ℕ,
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
        (((Modules.pullback g₀).mapHomologicalComplex _).obj C₀)).homology n ≅
          (higherDirectImage h n).obj ((Modules.pullback v).obj F)) := by
  classical
  intro S W g v h _ hs n
  let k : W ⟶ Z := hX.lift v (h ≫ g) (by rw [Category.assoc, hs.w])
  have hkA : k ≫ a = v := hX.lift_fst _ _ _
  have hk : IsPullback k h b g := hs.of_right' hX
  have hy : IsPullback (k ≫ q) h p ((g ≫ g₀) ≫ s) := by
    simpa only [Category.assoc] using hk.paste_horiz hY
  obtain ⟨ec⟩ := hcomp (g ≫ g₀) (k ≫ q) h hy n
  let eC := (Functor.mapHomologicalComplexCompIso (Modules.pullbackComp g g₀) (.up ℤ)).app C₀
  let eF : (Modules.pullback (k ≫ q)).obj M ≅ (Modules.pullback v).obj F :=
    ((Modules.pullbackComp k q).app M).symm ≪≫ (Modules.pullback k).mapIso eM ≪≫
      (Modules.pullbackComp k a).app F ≪≫
      (eqToIso (congrArg (fun t ↦ (Modules.pullback t).obj F) hkA))
  exact ⟨((HomologicalComplex.homologyFunctor S.Modules (.up ℤ) n).mapIso eC) ≪≫
    ec ≪≫ (higherDirectImage h n).mapIso eF⟩


/-- The full root-facing model from a Noetherian geometric descent certificate.
This statement and proof require no canonical derived base-change map. -/
theorem exists_cech_model_of_noetherian_descent
    {X Y Z T U B : Scheme.{u}} (f : X ⟶ T) (p : Y ⟶ B)
    (u : U ⟶ T) [IsOpenImmersion u] (g : U ⟶ B)
    (a : Z ⟶ X) (q : Z ⟶ Y) (b : Z ⟶ U)
    (hX : IsPullback a b f u) (hY : IsPullback q b p g)
    [IsProper p] [IsLocallyNoetherian B]
    (F : X.Modules) (M : Y.Modules) [M.IsFinitePresentation]
    (hM : M.IsFlatOver p)
    (eM : (Modules.pullback q).obj M ≅ (Modules.pullback a).obj F)
    (x : U) :
    ∃ (V : T.Opens) (C Q : CochainComplex V.toScheme.Modules ℤ) (d : ℕ),
      u x ∈ V ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 V.toScheme)) ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      (∃ e : Q ⟶ C, QuasiIso e) ∧
      ∀ {S W : Scheme.{u}} (k : S ⟶ V.toScheme) (v : W ⟶ X) (h : W ⟶ S)
        [HasInjectiveResolutions W.Modules], IsPullback v h f (k ≫ V.ι) → ∀ n : ℕ,
        Nonempty ((((Modules.pullback k).mapHomologicalComplex _).obj C).homology n ≅
          (higherDirectImage h n).obj ((Modules.pullback v).obj F)) := by
  classical
  let : IsGrothendieckAbelian.{u} Y.Modules := Scheme.Modules.isGrothendieckAbelian Y
  have : HasInjectiveResolutions Y.Modules := inferInstance
  obtain ⟨W, C₀, Q₀, d, hxW, hW, hge, hle, hflat, hqc, hQle, hfree,
      ⟨e₀, he₀⟩, hcomp⟩ := noetherian_exists_proper_flat_cech_model p M hM (g x)
  let V₀ := g ⁻¹ᵁ W
  let V : T.Opens := u ''ᵁ V₀
  let c : V₀.toScheme ≅ V.toScheme := u.isoImage V₀
  let l : V.toScheme ⟶ U := c.inv ≫ V₀.ι
  let g₀ : V.toScheme ⟶ W.toScheme := c.inv ≫ g ∣_ W
  have hlu : l ≫ u = V.ι := by
    exact u.isoImage_inv_ι V₀
  have hlg : l ≫ g = g₀ ≫ W.ι := by
    dsimp only [l, g₀]
    simp only [Category.assoc, morphismRestrict_ι]
    rfl
  let Z₀ := Limits.pullback b l
  let r : Z₀ ⟶ Z := pullback.fst b l
  let b₀ : Z₀ ⟶ V.toScheme := pullback.snd b l
  let a₀ : Z₀ ⟶ X := r ≫ a
  let q₀ : Z₀ ⟶ Y := r ≫ q
  have hX₀ : IsPullback a₀ b₀ f V.ι := by
    have hs := (IsPullback.of_hasPullback b l).paste_horiz hX
    simpa only [a₀, r, b₀, hlu] using hs
  have hY₀ : IsPullback q₀ b₀ p (g₀ ≫ W.ι) := by
    have hs := (IsPullback.of_hasPullback b l).paste_horiz hY
    simpa only [q₀, r, b₀, hlg] using hs
  let eM₀ : (Modules.pullback q₀).obj M ≅ (Modules.pullback a₀).obj F :=
    ((Modules.pullbackComp r q).app M).symm ≪≫
      (Modules.pullback r).mapIso eM ≪≫ (Modules.pullbackComp r a).app F
  let H := (Modules.pullback g₀).mapHomologicalComplex (.up ℤ)
  let C : CochainComplex V.toScheme.Modules ℤ := H.obj C₀
  let Q : CochainComplex V.toScheme.Modules ℤ := H.obj Q₀
  obtain ⟨hCge, hCle, hCflat, _, hQle', hQfree, he⟩ :=
    ordinary_pullback_model_resolution g₀ C₀ Q₀ d hge hle hflat hqc hQle hfree e₀ he₀
  refine ⟨V, C, Q, d, ?_, hCge, hCle, hCflat, hQle', hQfree, ⟨H.map e₀, he⟩, ?_⟩
  · exact (u.apply_mem_image_iff).mpr hxW
  · exact universal_ordinary_neighbourhood_model_transfer f p V.ι g₀ W.ι
      a₀ q₀ b₀ hX₀ hY₀ F M eM₀ C₀ hcomp


/-- Direct replacement for the existing root-facing theorem. Geometric descent is
retained with its existing statement and ordinary pullback comparisons. -/
theorem descent_first_exists_proper_flat_cech_model {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [IsProper f]
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      (∃ e : Q ⟶ C, QuasiIso e) ∧
      ∀ {S W : Scheme.{u}} (k : S ⟶ U.toScheme) (v : W ⟶ X) (h : W ⟶ S)
        [HasInjectiveResolutions W.Modules], IsPullback v h f (k ≫ U.ι) → ∀ n : ℕ,
        Nonempty ((((Modules.pullback k).mapHomologicalComplex _).obj C).homology n ≅
          (higherDirectImage h n).obj ((Modules.pullback v).obj F)) := by
  classical
  let top : T.Opens := ⊤
  let x : top.toScheme := ⟨t, by trivial⟩
  obtain ⟨V, hx, B, Y, W, _, _, hB, _, p, hp, M, hfp, hflat,
      g, q, hy, ⟨eTensor⟩⟩ := properFlat_single_noetherian_descent f F hF top x
  have : IsNoetherian W.toScheme := hB
  have : IsProper p := hp
  have : M.IsFinitePresentation := hfp
  let u := V.ι ≫ top.ι
  let Z := Limits.pullback f u
  let a : Z ⟶ X := pullback.fst f u
  let b : Z ⟶ V.toScheme := pullback.snd f u
  let c₁ : tensorPullback q ≅ Modules.pullback q :=
    (Classical.choice (nonempty_tensorPullbackAdjunction q)).leftAdjointUniq
      (pullbackPushforwardAdjunction q)
  let c₂ : tensorPullback a ≅ Modules.pullback a :=
    (Classical.choice (nonempty_tensorPullbackAdjunction a)).leftAdjointUniq
      (pullbackPushforwardAdjunction a)
  let eM : (Modules.pullback q).obj M ≅ (Modules.pullback a).obj F :=
    (c₁.app M).symm ≪≫ eTensor ≪≫ c₂.app F
  have hx' : u (⟨x, hx⟩ : V.toScheme) = t := rfl
  obtain ⟨U, C, Q, d, ht, hge, hle, hCflat, hQle, hfree, he, hcomp⟩ :=
    exists_cech_model_of_noetherian_descent f p u g a q b
      (IsPullback.of_hasPullback f u) hy F M hflat eM ⟨x, hx⟩
  rw [hx'] at ht
  exact ⟨U, C, Q, d, ht, hge, hle, hCflat, hQle, hfree, he, hcomp⟩


end AlgebraicGeometry.Scheme.Modules
