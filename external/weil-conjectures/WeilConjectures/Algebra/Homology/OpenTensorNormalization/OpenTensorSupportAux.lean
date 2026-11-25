/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import Mathlib.CategoryTheory.Limits.FullSubcategory
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat

/-! Explicit projection comparison for open tensor support -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem ordinaryUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Mod (restrictRing m j R)) :
    IsIso (o.adjunction.unit.app M) := by
  have h : o.adjunction.unit.app M = (o.sectionIso M).inv := by
    apply (cancel_mono (o.sectionIso M).hom).1
    rw [o.sectionUnit, Iso.inv_hom_id]
    rfl
  rw [h]
  infer_instance

private theorem derivedUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Der (restrictRing m j R)) :
    IsIso ((exactDerivedAdjunction o.adjunction).unit.app M) := by
  let a := exactDerivedAdjunction o.adjunction
  have hQ (P : CochainComplex (Mod (restrictRing m j R)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ ordinaryUnit_isIso o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (restrict m j R).mapDerivedCategoryFactors.inv.app _ ≫
            (restrict m j R).mapDerivedCategory.map
              (o.ordinary.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem isIso_of_adjunct
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) [IsIso a.unit] {X : B} {Y : A} (f : F.obj Y ⟶ X)
    (hf : IsIso (a.homEquiv _ _ f)) (hs : F.essImage X) : IsIso f := by
  have : F.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : F.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app X) := a.isIso_counit_app_iff_mem_essImage.mpr hs
  have := hf
  have he : f = F.map (a.homEquiv _ _ f) ≫ a.counit.app X := by
    exact ((a.homEquiv _ _).symm_apply_apply f).symm
  rw [he]
  infer_instance

-- Tensor-model descent lets us use a native comparison with only one K-flat input.

private theorem nativeTensorIso_exists
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    (a : TensorModel R) :
    Nonempty (a.functor ≅ @MonoidalCategory.tensor (Der R) _
      (RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} J R)) := by
  let L := ((resolving R).ι ⋙ DerivedCategory.Q).prod
    ((resolving R).ι ⋙ DerivedCategory.Q)
  let W := (Functor.whiskeringLeft _ _ (Der R)).obj L
  have : W.Full := ⟨fun {F G} ↦ (a.descent F G).surjective⟩
  have : W.Faithful := ⟨fun {F G} ↦ (a.descent F G).injective⟩
  let e : W.obj a.functor ≅ W.obj (@MonoidalCategory.tensor (Der R) _
      (RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} J R)) :=
    a.representative.symm ≪≫ NatIso.ofComponents
      (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2}
        J R P.1.obj P.2.obj (Or.inl P.1.property.1))
      (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, u + 1, u + 2}
        J R _ _ _ _ _ _ f.1.hom f.2.hom)
  exact ⟨W.preimageIso e⟩

-- A termwise supported complex is extended: its ordinary counit is a chain isomorphism.
private theorem Q_supported {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (C : CochainComplex (Mod R) ℤ)
    (hC : ∀ n, o.ordinary.essImage (C.X n)) :
    o.ordinary.mapDerivedCategory.essImage (DerivedCategory.Q.obj C) := by
  have (A : Mod (restrictRing m j R)) : IsIso (o.adjunction.unit.app A) :=
    ordinaryUnit_isIso o A
  have : IsIso o.adjunction.unit := NatIso.isIso_of_isIso_app _
  have : o.ordinary.Full := o.adjunction.fullyFaithfulLOfIsIsoUnit.full
  have : o.ordinary.Faithful := o.adjunction.fullyFaithfulLOfIsIsoUnit.faithful
  have (n : ℤ) : IsIso (o.adjunction.counit.app (C.X n)) :=
    o.adjunction.isIso_counit_app_iff_mem_essImage.mpr (hC n)
  let f : (o.ordinary.mapHomologicalComplex (.up ℤ)).obj
      (((restrict m j R).mapHomologicalComplex (.up ℤ)).obj C) ⟶ C :=
    { f n := o.adjunction.counit.app (C.X n)
      comm' _ _ _ := (o.adjunction.counit.naturality _).symm }
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact ⟨DerivedCategory.Q.obj (((restrict m j R).mapHomologicalComplex (.up ℤ)).obj C),
    ⟨o.ordinary.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso (asIso f)⟩⟩

private theorem sliceTensor_supported
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) (W : C)
    (M : Mod (R.over W)) (N : Mod R) :
    (localizedSystemExtension.{u + 1, u, u + 1} R W).essImage
      (((tensor R).obj ((localizedSystemExtension.{u + 1, u, u + 1} R W).obj M)).obj N) := by
  obtain ⟨θ⟩ := ringedSlice_extension_tensor.{u + 1, u + 1, u} J R W
  exact Functor.essImage.ofIso (ringedOpenSheafComparison.{u + 1, u, u + 1} R W θ M N)
    ((localizedSystemExtension.{u + 1, u, u + 1} R W).obj_mem_essImage _)

private theorem ordinaryTensor_supported {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j]
    {R : Sheaf (topology .ordinary X) CommRingCat.{u + 1}}
    (o : OpenExtension .ordinary j R) (M : Mod (restrictRing .ordinary j R))
    (N : Mod R) : o.ordinary.essImage (((tensor R).obj (o.ordinary.obj M)).obj N) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} U.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let W : X.ProEt := ProEt.mk j
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := ProEt.sliceEquiv X W
  have : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology X).over W) :=
    ProEt.sliceDense X W
  let B := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing .ordinary j R)
  let c : B ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) ((ProEt.topology X).over W)).obj (A.over W) := Iso.refl _
  obtain ⟨q, hq⟩ := ProEt.module_transport.{u} ((ProEt.topology X).over W)
    (ProEt.topology U) e (A.over W) B c
  let E := localizedSystemExtension.{u + 1, u, u + 1} R W
  let a₀ : E ⊣ overFunctor.{u + 1} A W := localizedSystemAdjunction R W
  let L := q.inverse ⋙ E
  let a : L ⊣ restrict .ordinary j R :=
    (q.symm.toAdjunction.comp a₀).ofNatIsoRight (by
      apply Functor.fullyFaithfulCancelRight (forget B)
      change overFunctor.{u + 1} A W ⋙ q.functor ⋙ forget B ≅
        restrict .ordinary j R ⋙ forget B
      rw [hq]
      refine NatIso.ofComponents (fun M ↦ ?_) ?_
      · exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
      · intro M N f
        ext V x
        rfl)
  let α : L ≅ o.ordinary := a.leftAdjointUniq o.adjunction
  have hE := sliceTensor_supported R W (q.inverse.obj M) N
  obtain ⟨P, ⟨β⟩⟩ := hE
  refine ⟨q.functor.obj P, ⟨?_⟩⟩
  exact (α.app _).symm ≪≫ E.mapIso (q.unitIso.app P).symm ≪≫ β ≪≫
    ((tensor R).mapIso (α.app M)).app N

-- Check support using the counit, whose invertibility is detected at each coefficient level.

private theorem systemSliceTensor_supported
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (W : C)
    (hW : ∀ V : C, Subsingleton (V ⟶ W))
    (o : WeilConjectures.SemilinearSections.OpenSystems.{u + 1, u, 0} J B τ W)
    (M : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1} (J.over W)
      (WeilConjectures.SemilinearSections.openRings.{u + 1, u, 0} J B W)
      (WeilConjectures.SemilinearSections.openTransitions.{u + 1, u, 0} J B τ W))
    (N : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1} J B τ) :
    o.extension.essImage (((tensor
      (WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1} J B τ)).obj
        (o.extension.obj M)).obj N) := by
  let R := WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1} J B τ
  let Z := ((tensor R).obj (o.extension.obj M)).obj N
  suffices hZ : IsIso (o.ordinaryAdjunction.counit.app Z) by
    exact o.ordinaryAdjunction.mem_essImage_of_counit_isIso Z
  apply SystemPresentation.evaluation_reflects_isIso J B τ
  intro n
  let V := WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n
  let VU := WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1} (J.over W)
    (WeilConjectures.SemilinearSections.openRings.{u + 1, u, 0} J B W)
    (WeilConjectures.SemilinearSections.openTransitions.{u + 1, u, 0} J B τ W) n
  let E := localizedSystemExtension.{u + 1, u, 0} (B n) W
  let a := localizedSystemAdjunction.{u + 1, u, 0} (B n) W
  have (P : Mod ((B n).over W)) : IsIso (a.unit.app P) :=
    SystemPresentation.localizedUnit_isIso (B n) W hW P
  have : IsIso a.unit := NatIso.isIso_of_isIso_app _
  have : E.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : E.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have hs : E.essImage (V.obj Z) := by
    apply Functor.essImage.ofIso
      (WeilConjectures.SemilinearSections.ordinaryEvaluationTensor.{u + 1, u, 0}
        J B τ n (o.extension.obj M) N).symm
    apply Functor.essImage.ofIso
      (((tensor (B n)).mapIso ((o.extensionEvaluation n).app M).symm).app (V.obj N))
    exact sliceTensor_supported (B n) W (VU.obj M) (V.obj N)
  have : IsIso (a.counit.app (V.obj Z)) :=
    a.isIso_counit_app_iff_mem_essImage.mpr hs
  have hc : IsIso (E.map ((o.restrictionEvaluation n).hom.app Z) ≫
      a.counit.app (V.obj Z)) := by infer_instance
  change IsIso (_ ≫ (localizedSystemAdjunction.{u + 1, u, 0} (B n) W).counit.app _) at hc
  rw [o.counit_evaluation] at hc
  exact IsIso.of_isIso_comp_left
    ((o.extensionEvaluation n).inv.app
      ((WeilConjectures.SemilinearSections.openRestriction J B τ W).obj Z))
    (V.map (o.ordinaryAdjunction.counit.app Z))

-- Present the arbitrary vertical ring sheaf as a tower, then transport its actual adjunction.
open WeilConjectures WeilConjectures.SemilinearSections in
private theorem systemsTensor_supported {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j]
    {R : Sheaf (topology .systems X) CommRingCat.{u + 1}}
    (o : OpenExtension .systems j R) (M : Mod (restrictRing .systems j R))
    (N : Mod R) : o.ordinary.essImage (((tensor R).obj (o.ordinary.obj M)).obj N) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} U.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
    essentiallySmallSelf.{0, u, u + 1} _
  have : EssentiallySmall.{u + 1} (ℕ × U.ProEt) :=
    essentiallySmallSelf.{0, u, u + 1} _
  let J := ProEt.topology X
  have hX : topology .systems X = coefficientSequenceTopology J := topology_systems_eq X
  have hU : topology .systems U = coefficientSequenceTopology (ProEt.topology U) :=
    topology_systems_eq U
  let Rv : Sheaf (coefficientSequenceTopology J) CommRingCat.{u + 1} :=
    ⟨R.obj, by rw [← hX]; exact R.property⟩
  obtain ⟨B, τ, hR⟩ := SystemPresentation.systemRing_presentation J Rv
  let R₀ := systemRing.{u + 1, u, u + 1} J B τ
  let Rc : Sheaf (topology .systems X) CommRingCat.{u + 1} :=
    ⟨R₀.obj, by rw [hX]; exact R₀.property⟩
  have hRc : Rc = R := by
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun Q ↦ Q.obj) hR
  revert N
  revert M
  revert o
  rw [← hRc]
  intro o₀ M N
  let C₀ := ring.{u + 1, u, u + 1} (coefficientSequenceTopology J) R₀
  let Cc := (sheafCompose (topology .systems X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Rc
  let i := CategoryTheory.Equivalence.refl (C := ℕ × X.ProEt)
  have : i.functor.IsContinuous (topology .systems X) (coefficientSequenceTopology J) := by
    rw [hX]
    exact Functor.isContinuous_id _
  have : i.inverse.IsContinuous (coefficientSequenceTopology J) (topology .systems X) := by
    rw [hX]
    exact Functor.isContinuous_id _
  obtain ⟨p, hp⟩ := moduleTransport (topology .systems X) (coefficientSequenceTopology J)
    i Cc C₀ (Iso.refl _)
  let W : X.ProEt := ProEt.mk j
  obtain ⟨sd⟩ := semilinearDerivedSections.{u + 1, u, 0} J B τ
  let os := sd.localization W
  let e₀ := ProEt.sliceEquiv X W
  have : e₀.inverse.IsDenseSubsite (ProEt.topology U) (J.over W) := ProEt.sliceDense X W
  let e := (CategoryTheory.Equivalence.refl (C := ℕ)).prod e₀
  have : e.inverse.IsContinuous (topology .systems U)
      (coefficientSequenceTopology (J.over W)) := by
    rw [hU]
    exact sequenceContinuous (ProEt.topology U) (J.over W) e₀.inverse
  have : e.functor.IsContinuous (coefficientSequenceTopology (J.over W))
      (topology .systems U) := by
    rw [hU]
    exact sequenceContinuous (J.over W) (ProEt.topology U) e₀.functor
  let A := ring.{u + 1, u, u + 1} (coefficientSequenceTopology (J.over W))
    (systemRing.{u + 1, u, u + 1} (J.over W)
      (openRings.{u + 1, u, 0} J B W) (openTransitions.{u + 1, u, 0} J B τ W))
  let Ac := ((openSite W).sheafPushforwardContinuous RingCat.{u + 1}
    (coefficientSequenceTopology (J.over W)) (coefficientSequenceTopology J)).obj C₀
  let c₀ : Ac ≅ A := eqToIso (openRing.{u + 1, u, 0} J B τ W)
  let S := (sheafCompose (topology .systems U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing .systems j Rc)
  let V := e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
    (topology .systems U) (coefficientSequenceTopology (J.over W))
  let cS : S ≅ V.obj Ac := Iso.refl _
  let c : S ≅ V.obj A := cS ≪≫ V.mapIso c₀
  obtain ⟨q, hq⟩ := moduleTransport (coefficientSequenceTopology (J.over W))
    (topology .systems U) e A S c
  let φ : A ⟶ Ac := c₀.inv
  have hφ : openRestriction.{u + 1, u, 0} J B τ W =
      SheafOfModules.pushforward.{u + 1} (F := openSite W)
        (J := coefficientSequenceTopology (J.over W))
        (K := coefficientSequenceTopology J) (R := C₀) φ := rfl
  have hc : c.hom.hom ≫ Functor.whiskerLeft e.inverse.op φ.hom = 𝟙 S.obj := by
    simpa only [c, φ, cS, V, Iso.refl_hom, ObjectProperty.FullSubcategory.id_hom] using
      pushedRingIso_cancel e.inverse c₀ cS
  let L := q.inverse ⋙ os.extension ⋙ p.inverse
  let a : L ⊣ restrict .systems j Rc :=
    ((q.symm.toAdjunction.comp os.ordinaryAdjunction).comp p.symm.toAdjunction).ofNatIsoRight
      (by
        apply Functor.fullyFaithfulCancelRight (forget S)
        simp only [Functor.assoc, CategoryTheory.Equivalence.symm_inverse]
        rw [hq, hφ]
        erw [← Functor.assoc
          (SheafOfModules.pushforward.{u + 1} (F := openSite W)
            (J := coefficientSequenceTopology (J.over W))
            (K := coefficientSequenceTopology J) (R := C₀) φ)
          (forget A), pushforward_forget φ]
        simp only [Functor.assoc]
        erw [← Functor.assoc p.functor (forget C₀), hp]
        refine Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (forget Cc) (PresheafOfModules.pushforwardId C₀.obj))
          (PresheafOfModules.pushforward φ.hom ⋙ PresheafOfModules.pushforward c.hom.hom) ≪≫ ?_
        refine Functor.isoWhiskerLeft (forget Cc)
          (pushforwardCompOfEq (F := e.inverse) (G := openSite W)
            (R := C₀.obj) (S := A.obj) (T := S.obj) c.hom.hom φ.hom (𝟙 S.obj) hc) ≪≫ ?_
        exact Iso.refl _)
  have hW (V : X.ProEt) : Subsingleton (V ⟶ W) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have : i.inverse.IsCocontinuous (coefficientSequenceTopology J) (topology .systems X) := by
    rw [hX]
    change (𝟭 (ℕ × X.ProEt)).IsCocontinuous _ _
    infer_instance
  obtain ⟨μ, _, _⟩ := SiteRestriction.tensorIso_exists (topology .systems X)
    (coefficientSequenceTopology J) i.inverse Rc
  let G := SiteRestriction.res (topology .systems X) (coefficientSequenceTopology J)
    i.inverse Rc
  let γ : p.functor ≅ G := by
    apply Functor.fullyFaithfulCancelRight (forget C₀)
    rw [hp]
    exact Iso.refl _
  let α : L ≅ o₀.ordinary := a.leftAdjointUniq o₀.adjunction
  let Z := ((tensor Rc).obj (o₀.ordinary.obj M)).obj N
  let δ : p.functor.obj Z ≅ ((tensor R₀).obj
      (os.extension.obj (q.inverse.obj M))).obj (p.functor.obj N) :=
    γ.app Z ≪≫ μ (o₀.ordinary.obj M) N ≪≫
      ((tensor R₀).mapIso ((γ.app (o₀.ordinary.obj M)).symm ≪≫
        p.functor.mapIso (α.app M).symm ≪≫
        p.counitIso.app (os.extension.obj (q.inverse.obj M)))).app (G.obj N) ≪≫
      ((tensor R₀).obj (os.extension.obj (q.inverse.obj M))).mapIso (γ.app N).symm
  have hs := systemSliceTensor_supported J B τ W hW os (q.inverse.obj M) (p.functor.obj N)
  obtain ⟨P, ⟨β⟩⟩ := Functor.essImage.ofIso δ.symm hs
  refine ⟨q.functor.obj P, ⟨?_⟩⟩
  exact (α.app _).symm ≪≫
    p.inverse.mapIso (os.extension.mapIso (q.unitIso.app P).symm) ≪≫
    p.inverse.mapIso β ≪≫ (p.unitIso.app Z).symm

-- Resolve the ambient input only; support of total terms is stable under coproducts.
private theorem derivedTensor_supported_of_underived {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (a : TensorModel R)
    (h : ∀ (M : Mod (restrictRing m j R)) (N : Mod R),
      o.ordinary.essImage (((tensor R).obj (o.ordinary.obj M)).obj N))
    (M : Der (restrictRing m j R)) (N : Der R) :
    o.ordinary.mapDerivedCategory.essImage
      (a.functor.obj (o.ordinary.mapDerivedCategory.obj M, N)) := by
  let := cochainModulesMonoidal R
  have := cochainModulesPreadditive R
  have (A : Mod (restrictRing m j R)) : IsIso (o.adjunction.unit.app A) :=
    ordinaryUnit_isIso o A
  have : IsIso o.adjunction.unit := NatIso.isIso_of_isIso_app _
  have : o.ordinary.Full := o.adjunction.fullyFaithfulLOfIsIsoUnit.full
  have : o.ordinary.Faithful := o.adjunction.fullyFaithfulLOfIsIsoUnit.faithful
  have : PreservesColimitsOfSize.{0, 0} o.ordinary :=
    o.adjunction.leftAdjoint_preservesColimits
  let P := DerivedCategory.Q.objPreimage M
  obtain ⟨T, f, hT, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (DerivedCategory.Q.objPreimage N)
  have := hf
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr hf
  let eN : DerivedCategory.Q.obj T ≅ N :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  let EP := (o.ordinary.mapHomologicalComplex (.up ℤ)).obj P
  have htotal : ∀ n, o.ordinary.essImage ((HomologicalComplex.tensorObj EP T).X n) := by
    intro n
    exact ObjectProperty.prop_of_isColimit _ (GradedObject.isColimitCofanMapObj _ _ n)
      (fun k ↦ h (P.X k.as.1.1) (T.X k.as.1.2))
  obtain ⟨e⟩ := nativeTensorIso_exists a
  let eM : DerivedCategory.Q.obj EP ≅ o.ordinary.mapDerivedCategory.obj M :=
    (o.ordinary.mapDerivedCategoryFactors.app P).symm ≪≫
      o.ordinary.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact Functor.essImage.ofIso
    (RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2} (topology m X) R
        EP T (Or.inr hT) ≪≫
      (@MonoidalCategory.tensor (Der R) _
        (RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (topology m X) R)).mapIso
          (eM.prod eN) ≪≫ (e.app _).symm)
    (Q_supported o (HomologicalComplex.tensorObj EP T) htotal)

end SheafOfModules.OpenTensorNormalization
