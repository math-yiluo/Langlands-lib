/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual coefficient kernel as a constant residue module

Source: Stacks Project, sites-cohomology.tex, Tag 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] HasDerivedCategory.standard completedAdicChangeData

namespace FiniteLayerKernelProof

private theorem constantUnitInjective (X : Scheme.{t}) (B : Type t) [CommRing B] :
    Presheaf.IsLocallyInjective (ProEt.topology X) (koszulConstantUnit X B) :=
  (koszulConstantUnit_local X B).1

private theorem constantUnitSurjective (X : Scheme.{t}) (B : Type t) [CommRing B] :
    Presheaf.IsLocallySurjective (ProEt.topology X) (koszulConstantUnit X B) :=
  (koszulConstantUnit_local X B).2

attribute [local instance] constantUnitInjective constantUnitSurjective

@[irreducible] private def restrictionCompIso (X : Scheme.{t})
    {R S T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ T) :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def restrictionIdIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    SheafOfModules.restrictScalars.{t + 1} (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

private theorem restrictionIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{t + 1} e.hom).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (SheafOfModules.restrictScalars e.inv)
  · exact (restrictionIdIso X S).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.inv_hom_id.symm) ≪≫
      restrictionCompIso X e.inv e.hom
  · exact (restrictionCompIso X e.hom e.inv).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.hom_inv_id) ≪≫
      restrictionIdIso X R

private theorem changeIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] : (completedAdicChange X φ).IsEquivalence := by
  let G := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  have : G.IsEquivalence := restrictionIsEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso (asIso φ))
  let a := (completedAdjunction X φ).choose
  exact a.isEquivalence_left_of_isEquivalence_right

private abbrev baseConstantFunctor (X : Scheme.{t}) (B : Type t) [CommRing B] :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙ koszulConstantFunctor X B

private theorem baseConstantExact (X : Scheme.{t}) (B : Type t) [CommRing B] :
    (baseConstantFunctor X B).Additive ∧
      PreservesFiniteLimits (baseConstantFunctor X B) ∧
      PreservesFiniteColimits (baseConstantFunctor X B) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} B)
  have : (koszulConstantFunctor X B).Additive := h.1
  have : PreservesFiniteLimits (koszulConstantFunctor X B) := h.2.1
  have : PreservesFiniteColimits (koszulConstantFunctor X B) := h.2.2
  have : PreservesFiniteLimits (baseConstantFunctor X B) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (baseConstantFunctor X B) := comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

@[irreducible] private def constantRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) (M : ModuleCat.{t} D) :
    (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (SheafOfModules.restrictScalars (adicModuleMap X f)).obj
        ((baseConstantFunctor X D).obj M) := by
  let α := koszulConstantUnit X B
  let β := koszulConstantUnit X D
  let φ := adicModuleMap X f
  have : Presheaf.IsLocallyInjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).2
  let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  let L' := ModuleCat.uliftFunctor.{t + 1, t} D ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).obj
    (L.obj ((ModuleCat.restrictScalars f).obj M))
  let P' := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} D)).obj
    (L'.obj M)
  let N := (baseConstantFunctor X D).obj M
  let a := (PresheafOfModules.sheafificationAdjunction β).unit.app P'
  let c : CommRingCat.of (ULift.{t + 1} B) ⟶ CommRingCat.of (ULift.{t + 1} D) :=
    CommRingCat.ofHom
                  (show ULift.{t + 1} B →+* ULift.{t + 1} D from RingHom.ulift f)
  let g : P ⟶ (PresheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars φ).obj N).val :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars φ).obj N).val).obj U)
        { toFun := a.app U
          map_add' := (a.app U).hom.map_add
          map_smul' := fun b m ↦ by
            have hs : β.app U ((RingHom.ulift f) b) = φ.hom.app U (α.app U b) :=
              ConcreteCategory.congr_hom
                (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).map c)) U) b
            change a.app U ((RingHom.ulift f) b • (show P'.obj U from m)) =
              φ.hom.app U (α.app U b) • (show N.val.obj U from a.app U m)
            rw [← hs]
            exact (a.app U).hom.map_smul ((RingHom.ulift f) b) m }
      naturality := fun {U V} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun k ↦ k m) (a.naturality h) }
  let e : (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ⟶
      (SheafOfModules.restrictScalars φ).obj N :=
    (PresheafOfModules.sheafificationHomEquiv α).symm g
  have hfac : toSheafify (ProEt.topology X) P.presheaf ≫
      ((SheafOfModules.toSheaf _).map e).hom =
        (PresheafOfModules.toPresheaf _).map g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := (SheafOfModules.restrictScalars φ).obj N)).apply_symm_apply g)
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (ProEt.topology X) _ hfac
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (ProEt.topology X) hfac
  have : IsIso ((SheafOfModules.toSheaf _).map e) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf _)
  exact asIso e

@[irreducible] private def changeUnitIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] :
    𝟭 _ ≅ completedAdicChange X φ ⋙ SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) := by
  have := changeIsEquivalence X φ
  let a := (completedAdjunction X φ).choose
  exact asIso a.unit

private theorem residueCoefficient_square (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    adicConstantMap X (adicQuotientMap d.ideal (n + 1) (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le n))) ≫ φ 0 =
      φ n ≫ completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
  let p := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let q := adicQuotientMap d.ideal (n + 1) (0 + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have hp : Function.Surjective (RingHom.ulift p) := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  let : Epi (CommRingCat.ofHom (RingHom.ulift p)) :=
    ConcreteCategory.epi_of_surjective _ hp
  let : (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).IsLeftAdjoint :=
    (constantSheafAdj (ProEt.topology X) CommRingCat.{t + 1}
      terminalIsTerminal).isLeftAdjoint
  have : Epi (adicConstantMap X p) := by
    unfold adicConstantMap
    infer_instance
  have hq : q.comp p = Ideal.Quotient.mk (d.ideal ^ (0 + 1)) := by
    ext x
    rfl
  apply (cancel_epi (adicConstantMap X p)).1
  calc
    adicConstantMap X p ≫ adicConstantMap X q ≫ φ 0 =
        adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (0 + 1))) ≫ φ 0 := by
      rw [← Category.assoc, adicConstantMap_comp, hq]
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d 0 := (hc.2 0).symm
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [completedAdicCommProjection_comp]
    _ = adicConstantMap X p ≫ φ n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [← Category.assoc, hc.2 n, Category.assoc]

private def regularMap {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) :
    ModuleCat.of B B ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of D D) :=
  ModuleCat.ofHom (X := ModuleCat.of B B)
    (Y := (ModuleCat.restrictScalars f).obj (ModuleCat.of D D))
    { toFun := f
      map_add' := map_add _
      map_smul' := fun r x ↦ f.map_mul r x }

private abbrev layerResidueMap {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :=
  Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1 + 1) :
      I ^ (n + 1 + 1) ≤ I ^ (0 + 1))

private abbrev layerPreviousMap {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :=
  Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
      I ^ (n + 1 + 1) ≤ I ^ (n + 1))

private abbrev layerCarrier {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :=
  (I ^ (n + 1) : Ideal A) ⧸
    (I ^ (0 + 1) • ⊤ : Submodule A (I ^ (n + 1) : Ideal A))

private def layerLinearMap {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    layerCarrier I n →ₗ[A] (A ⧸ I ^ (n + 1 + 1)) :=
  Submodule.mapQ (I ^ (0 + 1) • ⊤) (I ^ (n + 1 + 1))
    (Submodule.subtype (I ^ (n + 1))) (by
      intro x
      simp [Submodule.mem_smul_top_iff, pow_succ'])

private def layerInclusion {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    (ModuleCat.restrictScalars (layerResidueMap I n)).obj (finiteQuotientLayerModule I n) ⟶
      ModuleCat.of (A ⧸ I ^ (n + 1 + 1)) (A ⧸ I ^ (n + 1 + 1)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (layerResidueMap I n)).obj
      (finiteQuotientLayerModule I n))
    (Y := ModuleCat.of (A ⧸ I ^ (n + 1 + 1)) (A ⧸ I ^ (n + 1 + 1)))
    { toFun := layerLinearMap I n
      map_add' := (layerLinearMap I n).map_add
      map_smul' := fun r x ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Ideal.Quotient.mk (I ^ (n + 1 + 1)) (a * b) =
          Ideal.Quotient.mk (I ^ (n + 1 + 1)) a *
            Ideal.Quotient.mk (I ^ (n + 1 + 1)) b
        exact map_mul _ a b }

private abbrev layerQuotient {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :=
  regularMap (layerPreviousMap I n)

private theorem layer_sequence {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃ h : layerInclusion I n ≫ layerQuotient I n = 0,
      Nonempty (IsLimit (KernelFork.ofι (layerInclusion I n) h)) := by
  have hz : layerInclusion I n ≫ layerQuotient I n = 0 := by
    ext x
    obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Ideal.Quotient.mk (I ^ (n + 1)) a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  refine ⟨hz, ?_⟩
  let S := ShortComplex.mk (layerInclusion I n) (layerQuotient I n) hz
  have hs : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro x
      change layerPreviousMap I n x = 0 ↔ ∃ y, layerLinearMap I n y = x
      constructor
      · intro hx
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        have ha : a ∈ I ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp hx
        exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        change Ideal.Quotient.mk (I ^ (n + 1)) a = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    · intro x y h
      obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Ideal.Quotient.mk (I ^ (n + 1 + 1)) a =
        Ideal.Quotient.mk (I ^ (n + 1 + 1)) b at h
      exact (Submodule.Quotient.eq
        (p := (I ^ (0 + 1) • ⊤ : Submodule A (I ^ (n + 1) : Ideal A)))).mpr (by
        simpa only [Submodule.mem_smul_top_iff, Nat.reduceAdd, pow_one,
          Ideal.smul_eq_mul, pow_succ', pow_zero, mul_one, Submodule.coe_sub]
          using (Ideal.Quotient.eq.mp h))
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  exact ⟨hs.fIsKernel⟩

private abbrev forgetCommRing (X : Scheme.{t}) :=
  sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})

private abbrev liftedModule (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1} (R := ULift.{t + 1} B)
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

section CoefficientMap
variable (X : Scheme.{t}) {B D : Type t} [CommRing B] [CommRing D]
  {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
  (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
  (f : B →+* D) (ψ : R ⟶ S)
  (hsq : adicConstantMap X f ≫ φD = φB ≫ ψ)

private abbrev coefficientModule :=
  (SheafOfModules.restrictScalars.{t + 1} ((forgetCommRing X).map φB)).obj
    ((SheafOfModules.restrictScalars.{t + 1} ((forgetCommRing X).map ψ)).obj
      (SheafOfModules.unit ((forgetCommRing X).obj S)))

private abbrev coefficientPresheaf :=
  (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).obj
    ((liftedModule B).obj ((ModuleCat.restrictScalars f).obj (ModuleCat.of D D)))

@[irreducible] private def coefficientPresheafHom : coefficientPresheaf X f ⟶
    (PresheafOfModules.restrictScalars (koszulConstantUnit X B)).obj
      (coefficientModule X φB ψ).val where
  app U := ModuleCat.ofHom (X := (coefficientPresheaf X f).obj U)
    (Y := ((PresheafOfModules.restrictScalars (koszulConstantUnit X B)).obj
      (coefficientModule X φB ψ).val).obj U)
    { toFun := fun x ↦ φD.hom.app U ((koszulConstantUnit X D).app U x)
      map_add' := fun x y ↦ by rw [map_add, map_add]
      map_smul' := fun b x ↦ by
        have hunit : (koszulConstantUnit X D).app U ((RingHom.ulift f) b) =
            (adicConstantMap X f).hom.app U ((koszulConstantUnit X B).app U b) :=
          ConcreteCategory.congr_hom
            (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).map
                (CommRingCat.ofHom
                  (show ULift.{t + 1} B →+* ULift.{t + 1} D from RingHom.ulift f)))) U) b
        have hscalar := ConcreteCategory.congr_hom
          (NatTrans.congr_app (congrArg (fun a ↦ a.hom) hsq) U)
            ((koszulConstantUnit X B).app U b)
        change φD.hom.app U ((koszulConstantUnit X D).app U
          ((RingHom.ulift f) b * (show ULift.{t + 1} D from x))) = _
        rw [map_mul, map_mul, hunit]
        exact congrArg (fun z ↦ z * φD.hom.app U ((koszulConstantUnit X D).app U x))
          hscalar }
  naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((koszulConstantUnit X D ≫ ((forgetCommRing X).map φD).hom).naturality a) x

@[irreducible] private def coefficientHom :
    (baseConstantFunctor X B).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of D D)) ⟶
      coefficientModule X φB ψ :=
  (PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit X B)).symm
    (coefficientPresheafHom X φB φD f ψ hsq)

private theorem coefficientHom_isIso [IsIso φD] :
    IsIso (coefficientHom X φB φD f ψ hsq) := by
  let P := coefficientPresheaf X f
  let g := (PresheafOfModules.toPresheaf _).map
    (coefficientPresheafHom X φB φD f ψ hsq)
  let β := Functor.whiskerRight (koszulConstantUnit X D)
    (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1})
  let δ := Functor.whiskerRight (((forgetCommRing X).map φD).hom)
    (forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1})
  have : Presheaf.IsLocallyInjective (ProEt.topology X) β := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem (ProEt.topology X) (koszulConstantUnit X D) x y h
  have : Presheaf.IsLocallySurjective (ProEt.topology X) β := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem (ProEt.topology X) (koszulConstantUnit X D) x
  have : IsIso δ := inferInstance
  have hg : g = β ≫ δ := by dsimp only [g]; unfold coefficientPresheafHom; rfl
  have : Presheaf.IsLocallyInjective (ProEt.topology X) g := by
    rw [hg]
    exact inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X) (β ≫ δ))
  have : Presheaf.IsLocallySurjective (ProEt.topology X) g := by
    rw [hg]
    exact inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X) (β ≫ δ))
  have hfac : toSheafify (ProEt.topology X) P.presheaf ≫
      ((SheafOfModules.toSheaf _).map (coefficientHom X φB φD f ψ hsq)).hom = g := by
    calc
      _ = (PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit X B)
            (P := P) (F := coefficientModule X φB ψ))
              (coefficientHom X φB φD f ψ hsq)) :=
        (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
          (koszulConstantUnit X B) (coefficientHom X φB φD f ψ hsq)).symm
      _ = g := by
        unfold coefficientHom
        exact congrArg (PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationHomEquiv (koszulConstantUnit X B)
            (P := P) (F := coefficientModule X φB ψ)).apply_symm_apply
              (coefficientPresheafHom X φB φD f ψ hsq))
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf) :=
    ((ProEt.topology X).W_toSheafify P.presheaf).isLocallySurjective
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map (coefficientHom X φB φD f ψ hsq)).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (ProEt.topology X) g hfac
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map (coefficientHom X φB φD f ψ hsq)).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (ProEt.topology X) hfac
  have : IsIso ((SheafOfModules.toSheaf _).map (coefficientHom X φB φD f ψ hsq)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

end CoefficientMap

private def sheafUnitMap (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (ψ : R ⟶ S) :
    SheafOfModules.unit ((forgetCommRing X).obj R) ⟶
      (SheafOfModules.restrictScalars.{t + 1} ((forgetCommRing X).map ψ)).obj
        (SheafOfModules.unit ((forgetCommRing X).obj S)) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1}).map
      (((forgetCommRing X).map ψ).hom.app U))
    (fun r ↦ by ext m; exact ((((forgetCommRing X).map ψ).hom.app U).hom.map_mul r m).symm)
  val.naturality a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (((forgetCommRing X).map ψ).hom.naturality a) x

private theorem coefficientHom_step (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    (f : B →+* D) (ψ : R ⟶ S)
    (hsq : adicConstantMap X f ≫ φD = φB ≫ ψ) :
    (baseConstantFunctor X B).map (regularMap f) ≫ coefficientHom X φB φD f ψ hsq =
      coefficientHom X φB φB (RingHom.id B) (𝟙 R)
        (by rw [adicConstantMap_id]; simp) ≫
      (SheafOfModules.restrictScalars.{t + 1} ((forgetCommRing X).map φB)).map
        (sheafUnitMap X ψ) := by
  let α := koszulConstantUnit X B
  apply (PresheafOfModules.sheafificationHomEquiv α).injective
  change (PresheafOfModules.sheafificationAdjunction α).homEquiv _ _
      ((PresheafOfModules.sheafification α).map
        ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).map
          ((liftedModule B).map (regularMap f))) ≫ _) =
    (PresheafOfModules.sheafificationAdjunction α).homEquiv _ _ (_ ≫ _)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold coefficientHom
  change
    (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).map
        ((liftedModule B).map (regularMap f)) ≫
      (PresheafOfModules.sheafificationHomEquiv α
        (P := coefficientPresheaf X f) (F := coefficientModule X φB ψ))
        ((PresheafOfModules.sheafificationHomEquiv α
          (P := coefficientPresheaf X f) (F := coefficientModule X φB ψ)).symm
          (coefficientPresheafHom X φB φD f ψ hsq)) =
    (PresheafOfModules.sheafificationHomEquiv α
      (P := coefficientPresheaf X (RingHom.id B))
      (F := coefficientModule X φB (𝟙 R)))
        ((PresheafOfModules.sheafificationHomEquiv α
          (P := coefficientPresheaf X (RingHom.id B))
          (F := coefficientModule X φB (𝟙 R))).symm
          (coefficientPresheafHom X φB φB (RingHom.id B) (𝟙 R)
            (by rw [adicConstantMap_id]; simp))) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hunit := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom
        (show ULift.{t + 1} B →+* ULift.{t + 1} D from RingHom.ulift f)))) U) x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun a ↦ a.hom) hsq) U)
      ((koszulConstantUnit X B).app U x)
  unfold coefficientPresheafHom
  change φD.hom.app U ((koszulConstantUnit X D).app U ((RingHom.ulift f) x)) =
    ψ.hom.app U (φB.hom.app U ((koszulConstantUnit X B).app U x))
  exact (congrArg (φD.hom.app U) hunit).trans h

@[irreducible] private def coefficientRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ) (M : ModuleCat.{t} D) :
    (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)).obj
        ((finiteCoefficientConstantFunctor X D φD).obj M) ≅
      (finiteCoefficientConstantFunctor X B φB).obj ((ModuleCat.restrictScalars f).obj M) := by
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map φB)
  have : G.IsEquivalence := restrictionIsEquivalence X (H.mapIso (asIso φB))
  have hh : H.map φB ≫ H.map ψ = adicModuleMap X f ≫ H.map φD := by
    change H.map φB ≫ H.map ψ = H.map (adicConstantMap X f) ≫ H.map φD
    rw [← H.map_comp, ← H.map_comp, h]
  apply G.preimageIso
  exact ((restrictionCompIso X (H.map φB) (H.map ψ)).app _).symm ≪≫
    (eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) hh)).app _ ≪≫
    (restrictionCompIso X (adicModuleMap X f) (H.map φD)).app _ ≪≫
    (SheafOfModules.restrictScalars (adicModuleMap X f)).mapIso
      (((changeUnitIso X φD).app ((baseConstantFunctor X D).obj M)).symm) ≪≫
    (constantRestrictionIso X f M).symm ≪≫
    (changeUnitIso X φB).app
      ((baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M))

end FiniteLayerKernelProof

/-- The actual successor coefficient kernel is the constant ideal-power layer,
with its scalar action restricted from the residue coefficient sheaf.

Source: Stacks Project, sites-cohomology.tex, Tag 094I, the
identification of the successive-power ideal layer in the coefficient filtration.
(blueprint: lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison).

Proof: write B=A/I^(n+2), C=A/I and L=I^(n+1)/I I^(n+1). The map sending the
class of x in L to the class of x in B is additive and injective: its kernel is
exactly I I^(n+1)=I^(n+2). Its image is ker(B -> A/I^(n+1)). Multiplication by I
annihilates that kernel, so this is a C-linear identification, restricted along
B -> C. Constant module sheafification is exact, and the coefficient maps phi
are isomorphisms. Thus they carry the algebraic kernel to the kernel of the
actual coefficient-unit map. The scalar-compatibility equation hc.2, cancelled
against the constant quotient map from A, identifies the successor-to-residue
coefficient square. Consequently the transported B-action is exactly the
restriction displayed here. The proof includes I=0, I=top and the zero ring;
exact sheafification also covers an empty site. -/
theorem finiteQuotient_layer_kernel_constant_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ k : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (k + 1)) ⟶
      completedAdicFiniteCommRing X d k)
    (hφ : ∀ k : ℕ, IsIso (φ k))
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    Nonempty (kernel (finiteQuotientUnitMap X d n) ≅
      (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
            (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _)))).obj
        ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0)).obj
          (finiteQuotientLayerModule d.ideal n))) := by
  let H := FiniteLayerKernelProof.forgetCommRing X
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map (φ (n + 1)))
  have : IsIso (φ (n + 1)) := hφ (n + 1)
  have : IsIso (φ n) := hφ n
  have : IsIso (φ 0) := hφ 0
  have : G.IsEquivalence := FiniteLayerKernelProof.restrictionIsEquivalence X
    (H.mapIso (asIso (φ (n + 1))))
  let F := FiniteLayerKernelProof.baseConstantFunctor X B
  have : F.Additive := (FiniteLayerKernelProof.baseConstantExact X B).1
  have : PreservesFiniteLimits F := (FiniteLayerKernelProof.baseConstantExact X B).2.1
  let g := FiniteLayerKernelProof.layerQuotient d.ideal n
  let u := finiteQuotientUnitMap X d n
  let eb := FiniteLayerKernelProof.coefficientHom X (φ (n + 1)) (φ (n + 1))
    (RingHom.id B) (𝟙 _) (by rw [adicConstantMap_id]; simp)
  have : IsIso eb := FiniteLayerKernelProof.coefficientHom_isIso _ _ _ _ _ _
  let ed := FiniteLayerKernelProof.coefficientHom X (φ (n + 1)) (φ n)
    (FiniteLayerKernelProof.layerPreviousMap d.ideal n)
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) (hc.1 n)
  have : IsIso ed := FiniteLayerKernelProof.coefficientHom_isIso _ _ _ _ _ _
  have hmap : F.map g ≫ ed = eb ≫ G.map u :=
    FiniteLayerKernelProof.coefficientHom_step X (φ (n + 1)) (φ n)
      (FiniteLayerKernelProof.layerPreviousMap d.ideal n)
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) (hc.1 n)
  obtain ⟨hz, ⟨hk⟩⟩ := FiniteLayerKernelProof.layer_sequence d.ideal n
  let ek := (kernelIsKernel (F.map g)).conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ hk F)
  let eker := PreservesKernel.iso G u ≪≫
    (kernel.mapIso (F.map g) (G.map u) (asIso eb) (asIso ed) hmap).symm ≪≫ ek
  let er := FiniteLayerKernelProof.coefficientRestrictionIso X (φ (n + 1)) (φ 0)
    (FiniteLayerKernelProof.layerResidueMap d.ideal n)
    (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _))
    (FiniteLayerKernelProof.residueCoefficient_square X d φ hc (n + 1))
    (finiteQuotientLayerModule d.ideal n)
  let et := G.mapIso er ≪≫
    ((FiniteLayerKernelProof.changeUnitIso X (φ (n + 1))).app
      (F.obj ((ModuleCat.restrictScalars
        (FiniteLayerKernelProof.layerResidueMap d.ideal n)).obj
          (finiteQuotientLayerModule d.ideal n)))).symm
  exact ⟨G.preimageIso (eker ≪≫ et.symm)⟩

end AlgebraicGeometry.Scheme
