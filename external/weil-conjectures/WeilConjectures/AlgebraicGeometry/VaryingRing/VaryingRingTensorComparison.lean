/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # Normalized tensor comparison for varying-ring inverse image

Source: Stacks Project, Tags 03EL, 0B56, 06YS, 06YU and 07A4.
(blueprint: lem-pur-varying-ring-tensor-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open SheafOfModules.GeometricConstruction (mset)
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.VaryingRing

section RestrictedAdjunction
universe c₁ v₁ c₂ v₂ c₃ v₃ c₄ v₄ c₅ v₅
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restrictedAdjunction
    {C : Type c₁} {D : Type c₂} {E : Type c₃} {A : Type c₄} {B : Type c₅}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [Category.{v₄} A] [Category.{v₅} B]
    (I : C ⥤ E) (T : D ⥤ E) (Q : E ⥤ D) (q : Q ⊣ T) (P : D ⥤ C)
    (U : C ⥤ A) [U.Faithful] (W : E ⥤ B)
    (L : A ⥤ B) (V : B ⥤ A) (a : L ⊣ V)
    (eI : I ⋙ W ≅ U ⋙ L) (eP : P ⋙ U ≅ T ⋙ W ⋙ V)
    (E' : ∀ M H, (I.obj M ⟶ T.obj H) ≃ (M ⟶ P.obj H))
    (hE : ∀ M H f, U.map (E' M H f) ≫ eP.hom.app H =
      a.homEquiv _ _ (eI.inv.app M ≫ W.map f)) :
    ∃ am : I ⋙ Q ⊣ P, ∀ M H f,
      U.map (am.homEquiv M H f) ≫ eP.hom.app H =
        a.homEquiv _ _ (eI.inv.app M ≫ W.map (q.homEquiv _ _ f)) := by
  have hleft {M N : C} (b : M ⟶ N) (H : D) (f : I.obj N ⟶ T.obj H) :
      E' M H (I.map b ≫ f) = b ≫ E' N H f := by
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hE, U.map_comp, Category.assoc, hE, W.map_comp]
    have hn : eI.inv.app M ≫ W.map (I.map b) =
        L.map (U.map b) ≫ eI.inv.app N := (eI.inv.naturality b).symm
    rw [← Category.assoc, hn, Category.assoc, a.homEquiv_naturality_left]
  have hright (M : C) {H H' : D} (f : I.obj M ⟶ T.obj H) (b : H ⟶ H') :
      E' M H' (f ≫ T.map b) = E' M H f ≫ P.map b := by
    apply U.map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    have hp : U.map (P.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ V.map (W.map (T.map b)) := eP.hom.naturality b
    rw [hE, U.map_comp, Category.assoc, hp, ← Category.assoc,
      hE, W.map_comp, ← Category.assoc, a.homEquiv_naturality_right]
  let equiv : ∀ M H, ((I ⋙ Q).obj M ⟶ H) ≃ (M ⟶ P.obj H) :=
    fun M H ↦ (q.homEquiv _ _).trans (E' M H)
  have hn {M N : C} (b : M ⟶ N) (H : D) (f : (I ⋙ Q).obj N ⟶ H) :
      equiv M H ((I ⋙ Q).map b ≫ f) = b ≫ equiv N H f := by
    dsimp only [equiv, Equiv.trans_apply, Functor.comp_map]
    rw [q.homEquiv_naturality_left, hleft]
  let am : I ⋙ Q ⊣ P := Adjunction.mkOfHomEquiv {
    homEquiv := equiv
    homEquiv_naturality_left_symm := by
      intro M N H b f
      apply (equiv M H).injective
      rw [Equiv.apply_symm_apply, hn, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' f b
      dsimp only [equiv, Equiv.trans_apply]
      rw [q.homEquiv_naturality_right, hright] }
  refine ⟨am, ?_⟩
  intro M H f
  dsimp only [am]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact hE M H _
end RestrictedAdjunction

section NormalizedAdjunction
open SheafOfModules
open SheafOfModules.GeometricConstruction
open SheafOfModules.OpenTensorNormalization.GeneralizedRinged
attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The existential packaging of the normalized adjunction unfolds large site-module terms.
/-- The linear adjunction to the supplied sectionwise pushforward, retaining the
underlying set-sheaf hom equivalence. The scalar insertion is the image of `1 ⊗ m`.
This is the module adjunction construction of Stacks 03D7 with its normalization
recorded, rather than discarded by the existential wrapper. -/
private theorem normalizedAdjunction
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)
    [PreservesFiniteLimits L]
    (A : Sheaf J CommRingCat.{u + 1}) (B : Sheaf K CommRingCat.{u + 1})
    (φ : B ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj A)
    (RI : Sheaf J CommRingCat.{u + 1}) (I : AlgebraicInverseImage L B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (adj.homEquiv (rset B) (rset A)).symm
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ)) :
    ∃ am : I.modules ⋙ OpenTensorNormalization.GeneralizedRinged.tensorFunctor c ⊣
      SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ), ∀ M H a,
      (mset B).map (am.homEquiv M H a) =
        adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
          SheafOfModules.CochainTensorComparison.scalarInsertion B A RI L I c
            (I.modules ⋙ OpenTensorNormalization.GeneralizedRinged.tensorFunctor c)
            (fun _ ↦ rfl) M ≫ (mset A).map a) := by
  let V := F.sheafPushforwardContinuous (Type (u + 1)) K J
  let P := SheafOfModules.pushforward.{u + 1} (F := F) (J := K) (K := J)
      (R := base A) (S := base B)
    ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  let φs : rset B ⟶ V.obj (rset A) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map φ
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let eI := I.moduleUnderlying
  obtain ⟨L₀, hobj₀, hmap₀, V₀, ⟨a₀⟩, hAdd₀⟩ :=
    CategoryTheory.CochainPullback.ringedPullbackPresentation_exists
      (R := B) (S := A) L V adj RI I c
  let p : CategoryTheory.CochainPullback.RingedPullback.{u + 1, u + 1, u, u + 1, u}
      (J := K) (K := J) B A := {
    uInv := L, uPush := V, adj := adj, finiteLimits := inferInstance,
    RI := RI, I := I, coefficient := c, L := L₀, hobj := hobj₀, hmap := hmap₀,
    V := V₀, moduleAdj := a₀, additive := hAdd₀ }
  have hp : CategoryTheory.CochainPullback.structureMap p =
      (adj.homEquiv _ _).symm φs := by
    change I.ringUnderlying.hom ≫ _ = _
    rw [hc]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have hEquiv (M : SheafOfModules (base B)) (H : SheafOfModules (base A)) :
      ∃ E : (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)).obj H) ≃ (M ⟶ P.obj H),
        ∀ a, (mset B).map (E a) =
          adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    have ha : CategoryTheory.CochainPullback.moduleAddMap B (P.obj H) ≫ (𝟙 _) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (CategoryTheory.CochainPullback.moduleAddMap A H) := by
      simp only [Category.comp_id, prod.map_id_id, Category.id_comp]
      change _ = inv (prodComparison V ((mset A).obj H) ((mset A).obj H)) ≫ _
      apply (cancel_epi (prodComparison V ((mset A).obj H) ((mset A).obj H))).mp
      erw [IsIso.hom_inv_id_assoc]
      exact (pushforward_operations F A B φ H).symm
    have hs : CategoryTheory.CochainPullback.moduleSMulMap B (P.obj H) =
        prod.map φs (𝟙 _) ≫ inv (prodComparison V (rset A) ((mset A).obj H)) ≫
          V.map (CategoryTheory.CochainPullback.moduleSMulMap A H) :=
      pushforward_action F A B φ H
    have hg : adj.homEquiv _ _ (CategoryTheory.CochainPullback.structureMap p) = φs := by
      rw [hp, Equiv.apply_symm_apply]
    rw [← hg] at hs
    obtain ⟨E, hE⟩ := CategoryTheory.CochainPullback.linearMate_exists p H (P.obj H)
      (Iso.refl _) ha (by
        simp only [Iso.refl_hom]
        convert hs using 1
        rfl) M
    refine ⟨E, fun a ↦ ?_⟩
    have h := hE a
    change (mset B).map (E a) ≫ (𝟙 _) =
      adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) at h
    simpa only [Category.comp_id] using h
  obtain ⟨B', hB⟩ : ∃ B' : ∀ (M : SheafOfModules (base B))
      (H : SheafOfModules (base A)),
      (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)).obj H) ≃ (M ⟶ P.obj H),
      ∀ M H a, (mset B).map (B' M H a) =
        adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    exact ⟨fun M H ↦ (hEquiv M H).choose, fun M H ↦ (hEquiv M H).choose_spec⟩
  let restriction := restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)
  let eP : P ⋙ mset B ≅ restriction ⋙ mset RI ⋙ V :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  obtain ⟨am, ham⟩ := restrictedAdjunction I.modules restriction
    (OpenTensorNormalization.GeneralizedRinged.tensorFunctor c)
    (OpenTensorNormalization.GeneralizedRinged.tensorAdjunction c) P (mset B) (mset RI) L V
    adj eI eP B' (by
      intro M H a
      change (mset B).map (B' M H a) ≫ (𝟙 _) = _
      exact (Category.comp_id _).trans (hB M H a))
  refine ⟨am, ?_⟩
  intro M H a
  have h := ham M H a
  change (mset B).map (am.homEquiv M H a) ≫ (𝟙 _) = _ at h
  simp only [Category.comp_id] at h
  have hq : CategoryTheory.CochainPullback.insertion c (I.modules.obj M) =
      SheafOfModules.CochainTensorComparison.scalarInsertion B A RI L I c
        (I.modules ⋙ OpenTensorNormalization.GeneralizedRinged.tensorFunctor c)
        (fun _ ↦ rfl) M := by
    ext U x
    exact ((Classical.choose_spec
      (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique c)).1
        (I.modules.obj M) U x)
  have hm := CategoryTheory.CochainPullback.extensionHomEquiv_formula c
    (I.modules.obj M) H a
  change (mset RI).map
      ((OpenTensorNormalization.GeneralizedRinged.tensorAdjunction c).homEquiv _ _ a) =
    CategoryTheory.CochainPullback.insertion c (I.modules.obj M) ≫ (mset A).map a at hm
  rw [hq] at hm
  exact h.trans
    (congrArg (adj.homEquiv _ _) (congrArg (fun z ↦ eI.inv.app M ≫ z) hm))

end NormalizedAdjunction

section IsoCancellation
universe v₀ u₀
private theorem inverseChain
    {E : Type u₀} [Category.{v₀} E] {X₀ X₁ X₂ X₃ X₄ X₅ : E}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (q : X₄ ⟶ X₅) (w : X₀ ⟶ X₅)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ q = w) :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv ≫ w = q := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]
end IsoCancellation

section Model
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Total the inverse ordinary comparison and descend it on flat-term K-flat
representatives. The given tensor models identify the result with the two
specified closed tensor products. -/
private theorem modelOfOrdinary
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (F : SemilinearSections.Mod.{u + 1, u, u + 1} J R ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} K S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : SemilinearSections.Mod.{u + 1, u, u + 1} K S ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} J R) (adj : F ⊣ G)
    (A : SemilinearSections.Closed.{u + 1, u, u + 1} J R)
    (B : SemilinearSections.Closed.{u + 1, u, u + 1} K S)
    (TA : Models.{u + 1, u, u + 1} J R A)
    (TB : Models.{u + 1, u, u + 1} K S B)
    (e : ∀ M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R,
      F.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
        ordinaryTensor.{u + 1, u, u + 1} K S (F.obj M) (F.obj N))
    (he : ∀ {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (ordinaryTensorHom.{u + 1, u, u + 1} J R a b) ≫ (e M' N').hom =
        (e M N).hom ≫ ordinaryTensorHom.{u + 1, u, u + 1} K S (F.map a) (F.map b))
    (hk : ∀ P : CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1} J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      flatTerms.{u + 1, u, u + 1} J R P →
      CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := S)
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ mu : A.tensor ⋙ F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{u + 1, u, u + 1} J K R S F A B TA TB mu,
        model.ordinary = e := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let P := Scheme.ProjectionRestriction.resolving R
  let Q : ObjectProperty (CochainComplex (SemilinearSections.Mod.{u + 1, u, u + 1} K S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let i : P.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)) :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let r := Functor.isoWhiskerLeft (i.prod i) TA.comparison
  let H := F.mapHomologicalComplex (.up ℤ)
  have hH : ∀ X, P X → Q (H.obj X) := fun X h ↦ hk X h.1 h.2
  have hn {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R}
      (b : M ⟶ M') (d : N ⟶ N') :
      F.map (b ⊗ₘ d) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map b ⊗ₘ F.map d) := he b d
  let beta := SheafOfModules.OpenTensorNormalization.exactTensorTotalIso F e hn G adj
  obtain ⟨mu, hmu⟩ := SheafOfModules.OpenTensorNormalization.tensorDescentNormalized
    DerivedCategory.Q DerivedCategory.Q H F.mapDerivedCategory
    (Functor.mapDerivedCategoryFactors F).hom P Q hH
    (SheafOfModules.OpenTensorNormalization.resolvingQQ_fullyFaithful R (DerivedCategory
      (SemilinearSections.Mod.{u + 1, u, u + 1} K S)))
    (totalTensor.{u + 1, u, u + 1} J R) (totalTensor.{u + 1, u, u + 1} K S)
    A.tensor B.tensor r TB.comparison beta
    (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  refine ⟨mu, {
    ordinary := e
    chain := fun X Y ↦ beta.hom.app (X, Y)
    summand := ?_
    kflat := hk
    derived := ?_
  }, rfl⟩
  · intro X Y p q k h
    rw [SheafOfModules.OpenTensorNormalization.exactTensorTotalIso_hom_app]
    dsimp only [tensorPullbackTotal, tensorPullbackTotalComponent, tensorSummand]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  · intro X Y hx hy hfx hfy
    have hpx : P X :=
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat X).mp hx, hfx⟩
    have hpy : P Y :=
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Y).mp hy, hfy⟩
    have hm := hmu X Y hpx hpy
    change F.mapDerivedCategory.map (tensorModelIso.{u + 1, u, u + 1} J R A TA X Y hx hy).hom ≫
      mu.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
      B.tensor.map (Prod.mkHom ((Functor.mapDerivedCategoryFactors F).hom.app X)
        ((Functor.mapDerivedCategoryFactors F).hom.app Y)) ≫
      (tensorModelIso.{u + 1, u, u + 1} K S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).inv ≫
      DerivedCategory.Q.map (beta.hom.app (X, Y)) =
        (Functor.mapDerivedCategoryFactors F).hom.app
          ((totalTensor.{u + 1, u, u + 1} J R).obj (X, Y)) at hm
    have h := inverseChain
      (F.mapDerivedCategory.mapIso
        (tensorModelIso.{u + 1, u, u + 1} J R A TA X Y hx hy))
      (mu.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y))
      (B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app X)
        ((Functor.mapDerivedCategoryFactors F).app Y)))
      (tensorModelIso.{u + 1, u, u + 1} K S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).symm
      (DerivedCategory.Q.map (beta.hom.app (X, Y)))
      ((Functor.mapDerivedCategoryFactors F).hom.app
        ((totalTensor.{u + 1, u, u + 1} J R).obj (X, Y)))
      (by simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
        Iso.symm_hom] using hm)
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simpa only [H, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv, Iso.symm_inv] using h

end Model

section TensorTransport
universe vA vB uA uB
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transportTensor_natural
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : F ≅ G)
    (k : ∀ M N : C, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hk : ∀ {M M' N N' : C} (b : M ⟶ M') (d : N ⟶ N'),
      F.map (b ⊗ₘ d) ≫ (k M' N').hom =
        (k M N).hom ≫ (F.map b ⊗ₘ F.map d))
    {M M' N N' : C} (b : M ⟶ M') (d : N ⟶ N') :
    G.map (b ⊗ₘ d) ≫
        ((e.app (M' ⊗ N')).symm ≪≫ k M' N' ≪≫ tensorIso (e.app M') (e.app N')).hom =
      ((e.app (M ⊗ N)).symm ≪≫ k M N ≪≫ tensorIso (e.app M) (e.app N)).hom ≫
        (G.map b ⊗ₘ G.map d) := by
  have hn : (F.map b ⊗ₘ F.map d) ≫ (e.hom.app M' ⊗ₘ e.hom.app N') =
      (e.hom.app M ⊗ₘ e.hom.app N) ≫ (G.map b ⊗ₘ G.map d) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      e.hom.naturality b, e.hom.naturality d]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.app_hom, Iso.app_inv]
  rw [e.inv.naturality_assoc, ← Category.assoc (F.map (b ⊗ₘ d)), hk,
    Category.assoc, Category.assoc, hn]
  simp only [Category.assoc]
section OrdinaryTransport
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[irreducible] private noncomputable def transportedOrdinary
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (F G : SemilinearSections.Mod.{u + 1, u, u + 1} J R ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} K S) (e : F ≅ G)
    (k : ∀ M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R,
      F.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
        ordinaryTensor.{u + 1, u, u + 1} K S (F.obj M) (F.obj N))
    (M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R) :
    G.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
      ordinaryTensor.{u + 1, u, u + 1} K S (G.obj M) (G.obj N) :=
  letI := SheafOfModules.monoidalCategory S
  (e.app _).symm ≪≫ k M N ≪≫ tensorIso (e.app M) (e.app N)

private theorem transportedOrdinary_natural
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (F G : SemilinearSections.Mod.{u + 1, u, u + 1} J R ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} K S) (e : F ≅ G)
    (k : ∀ M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R,
      F.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
        ordinaryTensor.{u + 1, u, u + 1} K S (F.obj M) (F.obj N))
    (hk : ∀ {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R}
      (b : M ⟶ M') (d : N ⟶ N'),
      F.map (ordinaryTensorHom.{u + 1, u, u + 1} J R b d) ≫ (k M' N').hom =
        (k M N).hom ≫ ordinaryTensorHom.{u + 1, u, u + 1} K S (F.map b) (F.map d))
    {M M' N N' : SemilinearSections.Mod.{u + 1, u, u + 1} J R}
    (b : M ⟶ M') (d : N ⟶ N') :
    G.map (ordinaryTensorHom.{u + 1, u, u + 1} J R b d) ≫
        (transportedOrdinary J K R S F G e k M' N').hom =
      (transportedOrdinary J K R S F G e k M N).hom ≫
        ordinaryTensorHom.{u + 1, u, u + 1} K S (G.map b) (G.map d) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  unfold transportedOrdinary
  exact transportTensor_natural F G e k hk b d

private theorem transportedOrdinary_cancel
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (F G : SemilinearSections.Mod.{u + 1, u, u + 1} J R ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} K S) (e : F ≅ G)
    (k : ∀ M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R,
      F.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
        ordinaryTensor.{u + 1, u, u + 1} K S (F.obj M) (F.obj N))
    (M N : SemilinearSections.Mod.{u + 1, u, u + 1} J R) :
    letI := SheafOfModules.monoidalCategory S
    e.hom.app (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≫
        (transportedOrdinary J K R S F G e k M N).hom =
      (k M N).hom ≫ (tensorIso (e.app M) (e.app N)).hom := by
  let := SheafOfModules.monoidalCategory S
  unfold transportedOrdinary
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  exact Iso.hom_inv_id_app_assoc e _ _

end OrdinaryTransport

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem leftAdjointUniq_transpose
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    {F₀ F : C ⥤ D} {G : D ⥤ C} (a₀ : F₀ ⊣ G) (a : F ⊣ G)
    (M : C) (H : D) (b : F.obj M ⟶ H) :
    a₀.homEquiv M H ((Adjunction.leftAdjointUniq a₀ a).hom.app M ≫ b) =
      a.homEquiv M H b := by
  rw [a₀.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, a.homEquiv_unit]

private theorem transpose_precomp
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    {L : C ⥤ D} {V : D ⥤ C} (a : L ⊣ V)
    {Z T : C} {H : D} (z : Z ⟶ T) (k : L.obj T ⟶ H) :
    (a.homEquiv Z H).symm (z ≫ a.homEquiv T H k) = L.map z ≫ k := by
  rw [a.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

end TensorTransport

section SiteComparison
attribute [local irreducible] SheafOfModules.monoidalCategory
open SheafOfModules.GeometricConstruction

private abbrev modulePush
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (g : C ⥤ D) [g.IsContinuous J K]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (φ : R ⟶ (g.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S) :=
  SheafOfModules.pushforward.{u + 1} (F := g) (J := J) (K := K)
    (R := base S) (S := base R)
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)

/-- Transport the normalized pure pairing through the comparison of left adjoints.
The unit formula identifies its transpose with the specified lax tensor map. -/
private theorem ordinaryTranspose
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (g : C ⥤ D) [g.IsContinuous J K]
    (RY : Sheaf J CommRingCat.{u + 1}) (RX : Sheaf K CommRingCat.{u + 1})
    (φ : RY ⟶ (g.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj RX)
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (a : L ⊣ g.sheafPushforwardContinuous (Type (u + 1)) J K)
    [PreservesFiniteLimits L]
    (F₀ F : SemilinearSections.Mod.{u + 1, u, u + 1} J RY ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} K RX)
    (adj : F ⊣ modulePush g RY RX φ) (e : F₀ ≅ F)
    (k : ∀ M N, F₀.obj (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≅
      ordinaryTensor.{u + 1, u, u + 1} K RX (F₀.obj M) (F₀.obj N))
    (ins : ∀ T, L.obj ((mset RY).obj T) ⟶ (mset RX).obj (F₀.obj T))
    (transpose : ∀ T H (b : F.obj T ⟶ H),
      (mset RY).map (adj.homEquiv T H b) =
        a.homEquiv _ _ (ins T ≫ (mset RX).map (e.hom.app T ≫ b)))
    (pure : ∀ M N U v,
      (L.map (SheafOfModules.CochainInversePairing.pureSheaf RY M N) ≫
        ins (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≫
          (mset RX).map (k M N).hom).hom.app U v =
      tensorSection.{u + 1, u, u + 1} K RX (F₀.obj M) (F₀.obj N) U
        ((L.map (CartesianMonoidalCategory.fst ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins M).hom.app U v)
        ((L.map (CartesianMonoidalCategory.snd ((mset RY).obj M) ((mset RY).obj N)) ≫
          ins N).hom.app U v))
    (t : ∀ M N : SemilinearSections.Mod.{u + 1, u, u + 1} K RX,
      ordinaryTensor.{u + 1, u, u + 1} J RY
        ((modulePush g RY RX φ).obj M) ((modulePush g RY RX φ).obj N) ⟶
      (modulePush g RY RX φ).obj (ordinaryTensor.{u + 1, u, u + 1} K RX M N))
    (ht : ∀ M N U x y, (t M N).val.app U
      (tensorSection.{u + 1, u, u + 1} J RY _ _ U x y) =
      tensorSection.{u + 1, u, u + 1} K RX M N (g.op.obj U) x y) :
    ∀ M N, adj.homEquiv _ _ (transportedOrdinary J K RY RX F₀ F e k M N).hom =
      ordinaryTensorHom.{u + 1, u, u + 1} J RY
        (adj.unit.app M) (adj.unit.app N) ≫ t (F.obj M) (F.obj N) := by
  let := SheafOfModules.monoidalCategory RY
  let := SheafOfModules.monoidalCategory RX
  let ordinary := transportedOrdinary J K RY RX F₀ F e k
  intro M N
  let Z := (mset RY).obj M ⊗ (mset RY).obj N
  let x : Z ⟶ (mset RY).obj M := CartesianMonoidalCategory.fst _ _
  let y : Z ⟶ (mset RY).obj N := CartesianMonoidalCategory.snd _ _
  let z : Z ⟶ (mset RY).obj (ordinaryTensor.{u + 1, u, u + 1} J RY M N) :=
    SheafOfModules.CochainInversePairing.pureSheaf RY M N
  let b := ordinaryTensorHom.{u + 1, u, u + 1} J RY
      (adj.unit.app M) (adj.unit.app N) ≫ t (F.obj M) (F.obj N)
  have hz := SheafOfModules.OpenTensorNormalization.GeneralizedRinged.transpose_binary
    g L a (SheafOfModules.CochainInversePairing.pureSheaf RX (F.obj M) (F.obj N))
    (x ≫ (mset RY).map (adj.unit.app M))
    (y ≫ (mset RY).map (adj.unit.app N))
    (z ≫ (mset RY).map b) (by
      intro U v
      change M.val.obj U × N.val.obj U at v
      change (t (F.obj M) (F.obj N)).val.app U
        ((ordinaryTensorHom.{u + 1, u, u + 1} J RY
          (adj.unit.app M) (adj.unit.app N)).val.app U
          (tensorSection.{u + 1, u, u + 1} J RY M N U v.1 v.2)) = _
      exact (congrArg ((t (F.obj M) (F.obj N)).val.app U)
        (SheafOfModules.CochainScalarConstruction.pure_map RY
          (adj.unit.app M) (adj.unit.app N) U v.1 v.2)).trans
            (ht (F.obj M) (F.obj N) U _ _))
  have hleft : (a.homEquiv Z
      ((mset RX).obj (ordinaryTensor.{u + 1, u, u + 1} K RX (F.obj M) (F.obj N)))).symm
      (z ≫ (mset RY).map (adj.homEquiv _ _ (ordinary M N).hom)) =
      L.map z ≫ ins (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≫
        (mset RX).map ((k M N).hom ≫
          (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom) := by
    have he : e.hom.app (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≫
        (ordinary M N).hom = (k M N).hom ≫
          (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom := by
      exact transportedOrdinary_cancel J K RY RX F₀ F e k M N
    have h := congrArg
      (fun q ↦ (a.homEquiv Z ((mset RX).obj
        (ordinaryTensor.{u + 1, u, u + 1} K RX (F.obj M) (F.obj N)))).symm (z ≫ q))
      (transpose (ordinaryTensor.{u + 1, u, u + 1} J RY M N) _ (ordinary M N).hom)
    exact h.trans ((transpose_precomp a z _).trans
      (congrArg (fun q ↦ L.map z ≫ ins
        (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≫ (mset RX).map q) he))
  have units (T : SemilinearSections.Mod.{u + 1, u, u + 1} J RY) (w : Z ⟶ (mset RY).obj T) :
      (a.homEquiv Z ((mset RX).obj (F.obj T))).symm
        (w ≫ (mset RY).map (adj.unit.app T)) =
        L.map w ≫ ins T ≫ (mset RX).map (e.hom.app T) := by
    have h := transpose T (F.obj T) (𝟙 _)
    have hu : (mset RY).map (adj.unit.app T) =
        a.homEquiv _ _ (ins T ≫ (mset RX).map (e.hom.app T)) := by
      rw [adj.homEquiv_id, Category.comp_id] at h
      exact h
    exact (congrArg
      (fun q ↦ (a.homEquiv Z ((mset RX).obj (F.obj T))).symm (w ≫ q)) hu).trans
        (transpose_precomp a w _)
  have hp := pure M N
  have hEq : z ≫ (mset RY).map (adj.homEquiv _ _ (ordinary M N).hom) =
      z ≫ (mset RY).map b := by
    apply (a.homEquiv Z
      ((mset RX).obj (ordinaryTensor.{u + 1, u, u + 1} K RX
        (F.obj M) (F.obj N)))).symm.injective
    rw [hleft]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro v
    erw [hz U v, units M x, units N y]
    change (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom.val.app U
      ((L.map z ≫ ins (ordinaryTensor.{u + 1, u, u + 1} J RY M N) ≫
        (mset RX).map (k M N).hom).hom.app U v) = _
    erw [hp U v]
    exact SheafOfModules.CochainScalarConstruction.pure_map RX
      (e.hom.app M) (e.hom.app N) U _ _
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext RY M N _
  intro U m n
  exact congrArg (fun q ↦ q.hom.app U (m, n)) hEq

end SiteComparison

private abbrev verticalSite (X : Scheme.{u}) :=
  coefficientSequenceTopology (Scheme.ProEt.topology X)

private abbrev verticalRing (R : ℕ → CommRingCat.{u + 1})
    (φ : ∀ n, R (n + 1) ⟶ R n) (X : Scheme.{u}) :=
  systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)

private def commutativeRingMap (R : ℕ → CommRingCat.{u + 1})
    (φ : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    verticalRing R φ Y ⟶
      ((baseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (verticalSite Y) (verticalSite X)).obj (verticalRing R φ X) :=
  ⟨{ app U := CommRingCat.ofHom (ringMapApp R f U).hom
     naturality U V a := by
       apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
       exact ringMapApp_naturality R φ f a }⟩

section Main
attribute [local irreducible] SheafOfModules.monoidalCategory

end Main

end AlgebraicGeometry.ProEtale.VaryingRing
