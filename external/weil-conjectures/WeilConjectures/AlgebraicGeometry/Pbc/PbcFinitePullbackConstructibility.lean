/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
/-! # Constructible finite-coefficient module pullback

## References

* Stacks Tags 09AI and 09AL
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.ProEtale

private def scalarRestriction (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  ConstantScalarComparison.restriction (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)

private abbrev scalarEmbedding (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt A

private instance (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarEmbedding T A).Full := by
  unfold scalarEmbedding
  let := (ProEtale.coefficientModulePresheafFullyFaithful T.ProEt A).full
  infer_instance
private instance (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarEmbedding T A).Faithful := by
  unfold scalarEmbedding
  let := (ProEtale.coefficientModulePresheafFullyFaithful T.ProEt A).faithful
  infer_instance

private instance scalarRestriction_full (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).Full :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)).full
private instance scalarRestriction_faithful (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).Faithful :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) A
    (adicLisseRing T A) (adicLisseConstantUnit T A)).faithful

private instance scalarRestriction_essSurj (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRestriction T A).EssSurj where
  mem_essImage F := by
    let P := (scalarEmbedding T A).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit T A)
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{u + 1}
      (adicLisseConstantUnit T A)).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (scalarEmbedding T A)).preimageIso
      (asIso (adj.unit.app P)).symm

private instance scalarRestriction_equivalence (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : (scalarRestriction T A).IsEquivalence := {}

@[irreducible] private def constantCoefficients {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A) ≅
      adicLisseConstantRing Y A := by
  letI : IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of A)) := proEtaleConstantComparison_isIso g (CommRingCat.of A)
  exact asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of A))

@[irreducible] private def directImageEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleRingModuleDirectImage g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) ⋙ scalarRestriction X A ≅
      scalarRestriction Y A ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) g := by
  have adjunct : proEtaleRingDirectImageMap g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A) =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A) := by
    simp only [constantCoefficients, asIso_hom, proEtaleRingDirectImageMap]
    change (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ |>.symm
        (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))) = _
    exact (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ |>.apply_symm_apply _
  have sections : toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)).hom =
    Functor.whiskerLeft (proEtaleBaseChange g).op
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))) :=
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A) ⋙
        scalarRestriction X A).obj M).obj.obj U)
    let Q := (((scalarRestriction Y A ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[A] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ ?_ }).toModuleIso
    change ((proEtaleRingDirectImageMap g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A)).hom.app U).hom
      (((adicLisseConstantUnit X A).app U).hom a) •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m) =
      (((adicLisseConstantUnit Y A).app ((proEtaleBaseChange g).op.obj U)).hom a) •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m)
    rw [adjunct]
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m))
      (ConcreteCategory.congr_hom (congr_app sections U) a)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

@[irreducible] private def pullbackEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleRingModulePullback g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) ⋙ scalarRestriction Y A ≅
      scalarRestriction X A ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) g := by
  let EX := (scalarRestriction X A).asEquivalence
  let EY := (scalarRestriction Y A).asEquivalence
  let L := ProEtale.upperStar (ModuleCat.{u + 1} A) g
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} A) g
  let adj := EX.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      EY.symm.toAdjunction)
  let eR : EY.functor ⋙ R ⋙ EX.inverse ≅
      proEtaleRingModuleDirectImage g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) :=
    (Functor.isoWhiskerRight (directImageEncoding g A).symm EX.inverse) ≪≫
      Functor.isoWhiskerLeft _ EX.unitIso.symm
  let e := (proEtaleRingModuleAdjunction g (adicLisseConstantRing X A)
    (adicLisseConstantRing Y A) (constantCoefficients g A)).leftAdjointUniq
      (adj.ofNatIsoRight eR)
  exact Functor.isoWhiskerRight e EY.functor ≪≫
    Functor.associator EX.functor (L ⋙ EY.inverse) EY.functor ≪≫
    Functor.isoWhiskerLeft EX.functor
      (Functor.associator L EY.inverse EY.functor ≪≫
        Functor.isoWhiskerLeft L EY.counitIso ≪≫ Functor.rightUnitor L)

private abbrev relativeRing {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  (adicLisseForget Y).obj
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A))

private def relativeUnit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ (relativeRing g A).obj :=
  adicLisseConstantUnit Y A ≫ ((adicLisseForget Y).map (constantCoefficients g A).inv).hom

private instance relativeUnit_surjective {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective (ProEt.topology Y) (relativeUnit g A) := by
  unfold relativeUnit
  infer_instance

private abbrev relativeRestriction {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  ConstantScalarComparison.restriction (ProEt.topology Y) A
    (relativeRing g A) (relativeUnit g A)

@[irreducible] private def relativeEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleModuleInverseImage g (adicLisseConstantRing X A) ⋙ relativeRestriction g A ≅
      scalarRestriction X A ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) g := by
  let c := constantCoefficients g A
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso c)
  let e := (proEtaleRingExtensionAdjunction g (adicLisseConstantRing X A)
    (adicLisseConstantRing Y A) c).leftAdjointUniq E.symm.toAdjunction
  let er : relativeRestriction g A ≅ E.inverse ⋙ scalarRestriction Y A := Iso.refl _
  let ep : proEtaleModuleInverseImage g (adicLisseConstantRing X A) ⋙ E.inverse ≅
      proEtaleRingModulePullback g (adicLisseConstantRing X A)
        (adicLisseConstantRing Y A) c :=
    Functor.isoWhiskerLeft _ e.symm
  exact Functor.isoWhiskerLeft _ er ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ep _ ≪≫ pullbackEncoding g A

@[irreducible] private def scalarConstant (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (scalarRestriction X A).obj ((adicLisseConstantModules X A).obj M) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  letI := ConstantScalarComparison.constantComparisonHom_isIso (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M
  (asIso (ConstantScalarComparison.constantComparisonHom (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M)).symm

@[irreducible] private def relativeConstant {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] (M : ModuleCat.{u + 1} A) :
    (relativeRestriction g A).obj
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
        ((adicLisseConstantModules X A).obj M)) ≅
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M :=
  (relativeEncoding g A).app _ ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapIso (scalarConstant X A M) ≪≫
      ((((constantSheafΓAdj _ (ModuleCat.{u + 1} A)).comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)).ofNatIsoRight
          (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} A) g)).leftAdjointUniq
            (constantSheafΓAdj _ (ModuleCat.{u + 1} A))).app M

private def FixedFiniteModels (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : Prop :=
  ∃ S : Sieve (⊤_ Y.ProEt), S ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
    ∀ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt), S f →
      ∃ M : ModuleCat.{u + 1} A, Finite M ∧
        Nonempty (F.over V ≅
          (constantSheaf ((ProEt.topology Y).over V) (ModuleCat.{u + 1} A)).obj M)

@[irreducible] private def scalarOverIso (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (a : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (V : Y.ProEt) (F : SheafOfModules.{u + 1} R) :
    ((ConstantScalarComparison.restriction (ProEt.topology Y) A R a).obj F).over V ≅
      (ConstantScalarComparison.restriction ((ProEt.topology Y).over V) A (R.over V)
        (Functor.whiskerLeft (Over.forget V).op a)).obj (F.over V) := Iso.refl _

private theorem scalarOverModels (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (a : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    [Presheaf.IsLocallySurjective (ProEt.topology Y) a]
    (F N : SheafOfModules.{u + 1} R) (V : Y.ProEt)
    (M : ModuleCat.{u + 1} A)
    (em : ((ConstantScalarComparison.restriction (ProEt.topology Y) A R a).obj N).over V ≅
      (constantSheaf ((ProEt.topology Y).over V) (ModuleCat.{u + 1} A)).obj M) :
    Nonempty (F.over V ≅ N.over V) ↔
      Nonempty (((ConstantScalarComparison.restriction (ProEt.topology Y) A R a).obj F).over
        V ≅ (constantSheaf ((ProEt.topology Y).over V) (ModuleCat.{u + 1} A)).obj M) := by
  let E := ConstantScalarComparison.restriction ((ProEt.topology Y).over V) A
    (R.over V) (Functor.whiskerLeft (Over.forget V).op a)
  have : Presheaf.IsLocallySurjective ((ProEt.topology Y).over V)
      (Functor.whiskerLeft (Over.forget V).op a) :=
    Presheaf.isLocallySurjective_whisker ((ProEt.topology Y).over V)
      (ProEt.topology Y) (Over.forget V) a
  constructor
  · rintro ⟨e⟩
    exact ⟨scalarOverIso Y A R a V F ≪≫ E.mapIso e ≪≫
      (scalarOverIso Y A R a V N).symm ≪≫ em⟩
  · rintro ⟨e⟩
    exact ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology Y).over V) A (R.over V)
        (Functor.whiskerLeft (Over.forget V).op a)).preimageIso
          ((scalarOverIso Y A R a V F).symm ≪≫ e ≪≫ em.symm ≪≫
            scalarOverIso Y A R a V N)⟩

private theorem relativeFinite_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (F : ringedSiteModules.{u + 1} (relativeRing g A)) :
    IsRelativelyFiniteLisseModule g A F ↔
      FixedFiniteModels Y A ((relativeRestriction g A).obj F) := by
  have hm (V : Y.ProEt) (M : ModuleCat.{u + 1} A) :=
    scalarOverModels Y A (relativeRing g A) (relativeUnit g A) F
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
        ((adicLisseConstantModules X A).obj M)) V M
      (((ProEt.topology Y).overPullback (ModuleCat.{u + 1} A) V).mapIso
        (relativeConstant g A M) ≪≫
          (constantSheafOverIso (ProEt.topology Y) (ModuleCat.{u + 1} A) V M).symm)
  constructor
  · rintro ⟨S, hS, h⟩
    refine ⟨S, hS, fun V f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := h V f hf
    exact ⟨M, hM, (hm V M).mp he⟩
  · rintro ⟨S, hS, h⟩
    refine ⟨S, hS, fun V f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := h V f hf
    exact ⟨M, hM, (hm V M).mpr he⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fixedFiniteModels_iff (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :
    FixedFiniteModels Y A F ↔ ProEtale.IsFiniteLocallyConstant A F := by
  constructor
  · rintro ⟨S, hS, hs⟩
    let t := (ProEt.isTerminalMkId Y).uniqueUpToIso (terminalIsTerminal :
      IsTerminal (⊤_ Y.ProEt))
    obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp
      ((ProEt.topology Y).pullback_stable t.hom hS)
    obtain ⟨ι, U, f, rfl⟩ := P.exists_eq_ofArrows
    refine ⟨ι, fun i ↦ (U i).left, fun i ↦ (U i).hom, ?_, fun i ↦ ?_⟩
    · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
      have hw (i : ι) : (f i).left = (U i).hom := by
        exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (f i))
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage Y at hP
      simpa only [hw] using hP
    · obtain ⟨M, hM, ⟨e⟩⟩ := hs (U i) (f i ≫ t.hom) (hPS _ _ ⟨i⟩)
      have : (ProEt.sliceEquiv Y (U i)).inverse.IsDenseSubsite
          (ProEt.topology (U i).left) ((ProEt.topology Y).over (U i)) :=
        ProEt.sliceDense Y (U i)
      let E := (ProEt.sliceEquiv Y (U i)).sheafCongr
        ((ProEt.topology Y).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} A)
      let r : E.functor.obj (F.over (U i)) ≅
          (localizationRestriction (ModuleCat.{u + 1} A) (U i).hom (U i).prop).obj F :=
        ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
      exact ⟨M, Module.Finite.of_finite, ⟨(upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} A) (U i).hom (U i).prop).app F ≪≫ r.symm ≪≫
          E.functor.mapIso e ≪≫
            ((ProEt.sliceEquiv Y (U i)).constantSheafSheafCongrIso
              ((ProEt.topology Y).over (U i)) (ProEt.topology (U i).left)
                (ModuleCat.{u + 1} A) (Over.mkIdTerminal (X := U i))).app M⟩⟩
  · intro h
    obtain ⟨ι, U, f, hf, he⟩ := ProEtale.finiteModels_over A F (by
      obtain ⟨ι, W, g, hg, hW⟩ := h
      exact ⟨ι, W, g, hg, fun i ↦ by
        obtain ⟨M, hM, e⟩ := hW i
        exact ⟨M, Module.finite_of_finite A, e⟩⟩)
    let S : Sieve (⊤_ Y.ProEt) :=
      { arrows := fun V _ ↦ ∃ M : ModuleCat.{u + 1} A, Finite M ∧
          Nonempty (F.over V ≅
            (constantSheaf ((ProEt.topology Y).over V) (ModuleCat.{u + 1} A)).obj M)
        downward_closed := by
          intro V W a ha b
          obtain ⟨M, hM, ⟨e⟩⟩ := ha
          let G := (Over.map b).sheafPushforwardContinuous (ModuleCat.{u + 1} A)
            ((ProEt.topology Y).over W) ((ProEt.topology Y).over V)
          let c : G.obj ((constantSheaf ((ProEt.topology Y).over V)
              (ModuleCat.{u + 1} A)).obj M) ≅
              (constantSheaf ((ProEt.topology Y).over W) (ModuleCat.{u + 1} A)).obj M :=
            G.mapIso (constantSheafOverIso (ProEt.topology Y) (ModuleCat.{u + 1} A) V M) ≪≫
              (Sheaf.pushforwardOverMapIso
                ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M) b) ≪≫
                  (constantSheafOverIso (ProEt.topology Y) (ModuleCat.{u + 1} A) W M).symm
          exact ⟨M, hM, ⟨(F.pushforwardOverMapIso b).symm ≪≫ G.mapIso e ≪≫ c⟩⟩ }
    refine ⟨S, ?_, fun V f hf ↦ hf⟩
    let t := (ProEt.isTerminalMkId Y).uniqueUpToIso (terminalIsTerminal :
      IsTerminal (⊤_ Y.ProEt))
    apply (ProEt.topology Y).pullback_mem_iff_of_isIso (i := t.hom) |>.mp
    apply (ProEt.topology Y).superset_covering _ (Precoverage.generate_mem_toGrothendieck hf)
    intro V a ha
    obtain ⟨W, b, c, ⟨i⟩, hbc⟩ := ha
    exact S.downward_closed (f := f i ≫ t.hom) (he i) b

private theorem coefficientConstructible_iff (Y : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (F : pbcModules Y (adicLisseConstantRing Y A)) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y A F ↔
      ProEtale.IsConstructible A ((scalarRestriction Y A).obj F) := by
  constructor
  · rintro ⟨S, hn, hc, h⟩
    refine ⟨S, fun i ↦ ?_⟩
    apply ProEtale.isFiniteLocallyConstant_of_iso ((relativeEncoding (S.immersion i) A).app F)
    exact (fixedFiniteModels_iff _ _ _).mp
      ((relativeFinite_iff (S.immersion i) A _).mp (h i))
  · intro h
    obtain ⟨S, hn, hS⟩ := positive_stratification Y A _ h
    refine ⟨S, hn, S.isConstructible_stratum, fun i ↦ ?_⟩
    apply (relativeFinite_iff (S.immersion i) A _).mpr
    apply (fixedFiniteModels_iff _ _ _).mpr
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((relativeEncoding (S.immersion i) A).app F).symm (hS i)

private theorem fixedConstructible_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (hF : ProEtale.IsConstructible A F) :
    ProEtale.IsConstructible A ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj F) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hF
  have := hG
  have := IsConstructibleSheaf.upperStar g G
  exact ProEtale.isConstructible_of_iso
    (((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).app G).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapIso e)
    (ProEtale.isConstructible_comparisonUpperStar_obj _)

@[irreducible] private def levelPullbackEncoding {S T : Scheme.{u}} (g : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcRestrict (pbcLevelConstantComparison T d n).hom ⋙
      proEtaleRingModulePullback g (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1)))
        (adicLisseConstantRing S (A ⧸ d.ideal ^ (n + 1)))
        (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))) ≅
      proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
        ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n)) ⋙
          pbcRestrict (pbcLevelConstantComparison S d n).hom := by
  have hc : (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))).hom ≫
      (pbcLevelConstantComparison S d n).hom =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcLevelConstantComparison T d n).hom ≫ completedFiniteCoefficientMap g d n := by
    simp only [constantCoefficients, asIso_hom, completedFiniteCoefficientMap,
      ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    have hmap : ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (𝟙 (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))))) =
        𝟙 _ := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map_id _
    rw [hmap, Category.id_comp]
  have := proEtaleRingRestrictionPullbackInv_isIso g _ _ _ _
    (pbcLevelConstantComparison T d n).hom (pbcLevelConstantComparison S d n).hom
      (constantCoefficients g (A ⧸ d.ideal ^ (n + 1)))
      (asIso (completedFiniteCoefficientMap g d n)) hc
  exact asIso (proEtaleRingRestrictionPullbackInv g _ _ _ _
    (pbcLevelConstantComparison T d n).hom (pbcLevelConstantComparison S d n).hom
      (constantCoefficients g (A ⧸ d.ideal ^ (n + 1)))
      (asIso (completedFiniteCoefficientMap g d n)) hc)

/-- Exact finite-coefficient module inverse image preserves intrinsic constructibility.
No completed complex, derived category, completeness, or support interval is involved. -/
theorem pbc_finite_pullback_constructibility
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] (g : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (F : pbcModules T ((pbcAdicRings T d).obj (op n)))
    (h : @IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1)) _
      (d.quotientFinite n) ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj F)) :
    @IsConstructibleProEtaleCoefficientModuleSheaf S (A ⧸ d.ideal ^ (n + 1)) _
      (d.quotientFinite n) ((pbcRestrict (pbcLevelConstantComparison S d n).hom).obj
        ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
          ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n))).obj
            F)) := by
  have : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  apply (coefficientConstructible_iff S (A ⧸ d.ideal ^ (n + 1)) _).mpr
  let e := (scalarRestriction S (A ⧸ d.ideal ^ (n + 1))).mapIso
    ((levelPullbackEncoding g d n).app F).symm ≪≫
      (pullbackEncoding g (A ⧸ d.ideal ^ (n + 1))).app _
  exact ProEtale.isConstructible_of_iso e.symm
    (fixedConstructible_pullback g (A ⧸ d.ideal ^ (n + 1)) _
      ((coefficientConstructible_iff T (A ⧸ d.ideal ^ (n + 1)) _).mp h))

end AlgebraicGeometry.Scheme
