/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentLiftBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

set_option linter.privateModule false

/-! # Coefficient-normalized ordinary component edges

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

private theorem restriction_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F F' : C ⥤ D} [F.IsContinuous J K] [F'.IsContinuous J K]
    (τ : F ⟶ F') :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousNatTrans τ A J K) := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  constructor
  · apply Sheaf.unit_hom_ext
    rw [Functor.map_comp, ← Category.assoc,
      Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous,
      Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous]
    ext U
    simpa using ((Functor.LaxMonoidal.ε (sheafToPresheaf K A)).naturality
      (τ.app U.unop).op).symm
  · intro X Y
    apply Sheaf.tensor_hom_ext
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous,
      ← Functor.LaxMonoidal.μ_natural_assoc,
      Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous]
    ext U
    change (𝟙 _ ≫ _) ≫ _ = _ ≫ 𝟙 _ ≫ _
    rw [Category.id_comp, Category.id_comp]
    convert ((Functor.LaxMonoidal.μ (sheafToPresheaf K A) X Y).naturality
      (τ.app U.unop).op).symm using 1 <;> rfl

private theorem restriction_adj_counit_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (a.sheafPushforwardContinuous J K (E := A)).counit := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  have : (F ⋙ G).IsContinuous J J := Functor.isContinuous_comp F G J K J
  let c := Functor.sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K J
  have ht := restriction_monoidal (A := A) J J a.unit
  have hh : (a.sheafPushforwardContinuous J K (E := A)).counit = c.hom ≫
      Functor.sheafPushforwardContinuousNatTrans a.unit A J J ≫
      (Functor.sheafPushforwardContinuousId' (Iso.refl _) A J).hom := by
    ext P U
    simp only [c, Iso.trans_hom, Iso.refl_hom,
      Functor.sheafPushforwardContinuousIso_hom,
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.comp_obj, Functor.id_obj,
      Adjunction.sheafPushforwardContinuous_counit_app_hom_app, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      Functor.whiskerRight_app, Functor.op_obj, op_unop, NatTrans.op_app,
      Functor.sheafPushforwardContinuousId'_hom_app_hom_app, Iso.refl_inv,
      NatTrans.id_app, op_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    change P.obj.map _ = 𝟙 _ ≫ P.obj.map _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  rw [hh]
  dsimp only [c]
  infer_instance

private theorem restriction_adj_unit_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (a.sheafPushforwardContinuous J K (E := A)).unit := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  have : (G ⋙ F).IsContinuous K K := Functor.isContinuous_comp G F K J K
  let c := Functor.sheafPushforwardContinuousComp' (Iso.refl (G ⋙ F)) A K J K
  have ht := restriction_monoidal (A := A) K K a.counit
  have hh : (a.sheafPushforwardContinuous J K (E := A)).unit =
      (Functor.sheafPushforwardContinuousId' (Iso.refl _) A K).inv ≫
      Functor.sheafPushforwardContinuousNatTrans a.counit A K K ≫ c.inv := by
    ext P U
    simp only [c, Iso.trans_inv, Iso.refl_inv,
      Functor.sheafPushforwardContinuousIso_inv,
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.id_obj, Functor.comp_obj,
      Adjunction.sheafPushforwardContinuous_unit_app_hom_app, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      Functor.sheafPushforwardContinuousId'_inv_app_hom_app, op_unop, Iso.refl_hom,
      NatTrans.id_app, op_id, CategoryTheory.Functor.map_id, Functor.whiskerRight_app,
      Functor.op_obj, NatTrans.op_app, Category.id_comp]
    change P.obj.map _ = P.obj.map _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
  rw [hh]
  dsimp only [c]
  infer_instance

private theorem lax_mate_monoidal
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.LaxMonoidal] [L₂.LaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    [NatTrans.IsMonoidal a.unit] [NatTrans.IsMonoidal b.counit]
    (d : R₁ ≅ R₂) [NatTrans.IsMonoidal d.hom] :
    NatTrans.IsMonoidal ((conjugateIsoEquiv a b).symm d).hom := by
  let z : L₂ ⟶ L₁ :=
    L₂.leftUnitor.inv ≫ Functor.whiskerRight a.unit L₂ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L₁ (Functor.whiskerRight d.hom L₂) ≫
      Functor.whiskerLeft L₁ b.counit ≫ L₁.rightUnitor.hom
  have hz : ((conjugateIsoEquiv a b).symm d).hom = z := by
    ext X
    simp [z, conjugateIsoEquiv, conjugateEquiv, mateEquiv]
  rw [hz]
  dsimp only [z]
  infer_instance

private local instance componentContinuous (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X) := by
  let F := CondensedRing.componentTests X
  have hF := (component_relative_profinite_site X).choose_spec
  -- Continuity is a consequence of the stated covering and limit properties.
  have : PreservesFiniteLimits F := hF.2.2.2.2.2.1
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro E R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨I, hI, V, f, hf, hm⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hR
  let E₀ : I → Over (affineComponentSpace X) := fun i ↦ Over.mk (f i ≫ E.hom)
  let a : ∀ i, E₀ i ⟶ E := fun i ↦ Over.homMk (f i) rfl
  have hjs : ∀ e : E.left, ∃ i x, (a i).left x = e :=
    ((Profinite.effectiveEpiFamily_tfae V f).out 1 3).mp hf
  have hc := hF.2.2.2.2.2.2.2.1 (ULift.{u} I) (fun i ↦ E₀ i.down) E
    (fun i ↦ a i.down) (by
      intro x
      obtain ⟨i, y, hy⟩ := hjs x
      exact ⟨⟨i⟩, y, hy⟩)
  apply (Scheme.ProEt.topology X).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hc)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W g hg
  obtain ⟨i⟩ := hg
  exact ⟨E₀ i.down, a i.down, 𝟙 _, (Sieve.overEquiv_iff R (f i.down)).mp (hm i.down),
    (Category.id_comp _).symm⟩

private local instance componentMonoidal (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentInverse X).Monoidal := by
  let : PreservesFiniteLimits (CondensedRing.componentTests X) :=
    (component_relative_profinite_site X).choose_spec.2.2.2.2.2.1
  let : RepresentablyFlat (CondensedRing.componentTests X) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.sheafPullbackMonoidal _ _ _ _

private local instance componentRawMonoidal (X : Scheme.{u}) [IsAffine X] :
    (Functor.sheafPullbackConstruction.sheafPullback (CondensedRing.componentTests X)
      Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)).Monoidal := componentMonoidal X

private local instance absoluteTestsContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)

private local instance componentBraided (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentInverse X).Braided :=
  { braided := (componentAdjunction X (componentContinuous X)).μ_comp_map_braiding }

private local instance componentLimits (X : Scheme.{u}) [IsAffine X] :
    PreservesFiniteLimits (CondensedRing.componentInverse X) := by
  let : PreservesFiniteLimits (CondensedRing.componentTests X) :=
    (component_relative_profinite_site X).choose_spec.2.2.2.2.2.1
  let : RepresentablyFlat (CondensedRing.componentTests X) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  unfold CondensedRing.componentInverse
  infer_instance

private local instance componentColimits (X : Scheme.{u}) [IsAffine X] :
    PreservesFiniteColimits (CondensedRing.componentInverse X) := by
  have : PreservesColimitsOfSize.{0, 0} (CondensedRing.componentInverse X) :=
    (componentAdjunction X (componentContinuous X)).leftAdjoint_preservesColimits
  infer_instance

private def absoluteBeta (X : Scheme.{u}) [IsAffine X]
    (e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
      profiniteToProEtOf X) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} (affineComponentSpace X) ⋙
      CondensedRing.componentInverse X ≅ upperStarFromPoint X := by
  let d := Functor.sheafPushforwardContinuousComp' e Ab.{u + 1}
    (coherentTopology Profinite.{u})
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
  exact (conjugateIsoEquiv (absoluteAdjunction X)
    ((slicePointAdjunction (affineComponentSpace X)).comp
      (componentAdjunction X (componentContinuous X)))).symm d.symm

private local instance absoluteBetaMonoidal (X : Scheme.{u}) [IsAffine X]
    (e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
      profiniteToProEtOf X) : NatTrans.IsMonoidal (absoluteBeta X e).hom := by
  have : (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ X)).IsContinuous
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X) := absoluteTestsContinuous X
  let c := Functor.sheafPushforwardContinuousComp profiniteToProEt
    (Scheme.proEtaleBaseChange (toSpecZ X)) Ab.{u + 1} (coherentTopology Profinite.{u})
    (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)
  have hc₀ : NatTrans.IsMonoidal c.hom := by
    let d := Functor.sheafPushforwardContinuousComp'
      (Iso.refl (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ X))) Ab.{u + 1}
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)
    have hd : NatTrans.IsMonoidal d.hom := by dsimp only [d]; infer_instance
    have he : c.hom = d.hom := by
      ext G U
      simp [c, d, Functor.sheafPushforwardContinuousComp',
        Functor.sheafPushforwardContinuousComp]
      rfl
    rw [he]
    exact hd
  have hu₀ : (absoluteAdjunction X).IsMonoidal := by
    unfold absoluteAdjunction
    apply Adjunction.isMonoidal_ofNatIsoRight
  have hu : NatTrans.IsMonoidal (absoluteAdjunction X).unit := by infer_instance
  have hc : NatTrans.IsMonoidal
      (slicePointAdjunction (affineComponentSpace X)).counit :=
    restriction_adj_counit_monoidal (A := Ab.{u + 1})
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (coherentTopology Profinite.{u}) (Over.forgetAdjStar _)
  have : NatTrans.IsMonoidal
      ((slicePointAdjunction (affineComponentSpace X)).comp
        (componentAdjunction X (componentContinuous X))).counit := by
    change NatTrans.IsMonoidal
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (slicePointAdjunction (affineComponentSpace X)).counit ≫
          (Functor.rightUnitor _).hom) _ ≫
            (componentAdjunction X (componentContinuous X)).counit)
    infer_instance
  let d := Functor.sheafPushforwardContinuousComp' e Ab.{u + 1}
    (coherentTopology Profinite.{u})
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
  let : NatTrans.IsMonoidal d.symm.hom := by
    change NatTrans.IsMonoidal d.inv
    dsimp only [d]
    infer_instance
  exact lax_mate_monoidal (absoluteAdjunction X)
    ((slicePointAdjunction (affineComponentSpace X)).comp
      (componentAdjunction X (componentContinuous X))) d.symm

private local instance sliceMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceInverse h).Monoidal := by
  let : RepresentablyFlat (Over.pullback h) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.sheafPullbackMonoidal _ _ _ _

private local instance sliceBraided {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceInverse h).Braided :=
  { braided := (sliceAdjunction h).μ_comp_map_braiding }

private local instance sliceLimits {P Q : Profinite.{u}} (h : Q ⟶ P) :
    PreservesFiniteLimits (sliceInverse h) := by
  let : RepresentablyFlat (Over.pullback h) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  unfold sliceInverse
  infer_instance

private local instance sliceColimits {P Q : Profinite.{u}} (h : Q ⟶ P) :
    PreservesFiniteColimits (sliceInverse h) := by
  have : PreservesColimitsOfSize.{0, 0} (sliceInverse h) :=
    (sliceAdjunction h).leftAdjoint_preservesColimits
  infer_instance

private theorem restriction_comp
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
    [F.IsContinuous J K] [G.IsContinuous K J]
    [F'.IsContinuous K L] [G'.IsContinuous L K]
    (a : F ⊣ G) (b : F' ⊣ G') :
    letI := Functor.isContinuous_comp F F' J K L
    letI := Functor.isContinuous_comp G' G L K J
    (b.sheafPushforwardContinuous K L (E := A)).comp
        (a.sheafPushforwardContinuous J K (E := A)) =
      (a.comp b).sheafPushforwardContinuous J L (E := A) := by
  apply Adjunction.ext
  ext P E
  simp [Adjunction.sheafPushforwardContinuous, Adjunction.comp_unit_app,
    ← Functor.map_comp, ← op_comp]

private abbrev sliceRestriction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (coherentTopology Profinite.{u}).overMapPullback Ab.{u + 1} h

private def restrictionAdjunction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (Over.mapPullbackAdj h).sheafPushforwardContinuous
    ((coherentTopology Profinite.{u}).over Q) ((coherentTopology Profinite.{u}).over P)
    (E := Ab.{u + 1})

private def restrictionComparison {P Q : Profinite.{u}} (h : Q ⟶ P) :
    sliceInverse h ≅ sliceRestriction h :=
  (sliceAdjunction h).leftAdjointUniq (restrictionAdjunction h)

private local instance restrictionComparisonMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    NatTrans.IsMonoidal (restrictionComparison h).hom := by
  have hu : NatTrans.IsMonoidal (restrictionAdjunction h).unit :=
    restriction_adj_unit_monoidal _ _ (Over.mapPullbackAdj h)
  have hd : NatTrans.IsMonoidal (Iso.refl (sliceDirect h)).hom := by
    change NatTrans.IsMonoidal (𝟙 (sliceDirect h))
    infer_instance
  have ht := lax_mate_monoidal (restrictionAdjunction h) (sliceAdjunction h)
    (Iso.refl (sliceDirect h))
  exact ht

private def restrictionPointComparison {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ sliceRestriction h ≅
      (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q :=
  Functor.sheafPushforwardContinuousComp'
    (F := Over.map h) (G := Over.forget P) (Iso.refl (Over.forget Q)) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over Q)
    ((coherentTopology Profinite.{u}).over P) (coherentTopology Profinite.{u})

private def normalizedSliceBeta {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ sliceInverse h ≅
      (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q :=
  Functor.isoWhiskerLeft
      ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P)
      (restrictionComparison h) ≪≫ restrictionPointComparison h

private def restrictionIdentity (P : Profinite.{u}) :
    sliceRestriction (𝟙 P) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (Over.mapId P) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P)

private def normalizedSliceIdentity (P : Profinite.{u}) :
    sliceInverse (𝟙 P) ≅ 𝟭 _ :=
  restrictionComparison (𝟙 P) ≪≫ restrictionIdentity P

private def restrictionComposition {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    sliceRestriction (g ≫ f) ≅ sliceRestriction f ⋙ sliceRestriction g :=
  (Functor.sheafPushforwardContinuousComp' (Over.mapComp g f).symm Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over R)
    ((coherentTopology Profinite.{u}).over Q)
    ((coherentTopology Profinite.{u}).over P)).symm

private def normalizedSliceComposition {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    sliceInverse (g ≫ f) ≅ sliceInverse f ⋙ sliceInverse g :=
  restrictionComparison (g ≫ f) ≪≫ restrictionComposition f g ≪≫
    Functor.isoWhiskerLeft (sliceRestriction f) (restrictionComparison g).symm ≪≫
    Functor.isoWhiskerRight (restrictionComparison f).symm (sliceInverse g)

private local instance normalizedSliceBetaMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    NatTrans.IsMonoidal (normalizedSliceBeta h).hom := by
  dsimp only [normalizedSliceBeta, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  have : NatTrans.IsMonoidal (restrictionPointComparison h).hom := by
    dsimp only [restrictionPointComparison]
    infer_instance
  infer_instance

private local instance normalizedSliceIdentityMonoidal (P : Profinite.{u}) :
    NatTrans.IsMonoidal (normalizedSliceIdentity P).hom := by
  have : NatTrans.IsMonoidal (restrictionIdentity P).hom := by
    dsimp only [restrictionIdentity]
    infer_instance
  dsimp only [normalizedSliceIdentity, Iso.trans_hom]
  infer_instance

private local instance normalizedSliceCompositionMonoidal {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    NatTrans.IsMonoidal (normalizedSliceComposition f g).hom := by
  have : NatTrans.IsMonoidal (restrictionComposition f g).hom := by
    change NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
      (Over.mapComp g f).symm Ab.{u + 1} _ _ _).inv
    infer_instance
  dsimp only [normalizedSliceComposition, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

private theorem normalized_mate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Q₁ : A ⥤ B} {Q₂ : A ⥤ C} {S₁ : B ⥤ A} {S₂ : C ⥤ A}
    {L T : B ⥤ C} {R : C ⥤ B}
    (p : Q₁ ⊣ S₁) (q : Q₂ ⊣ S₂) (a : L ⊣ R) (t : T ⊣ R)
    (c : Q₁ ⋙ T ≅ Q₂) :
    conjugateIsoEquiv (p.comp a) q
        (c.symm ≪≫ Functor.isoWhiskerLeft Q₁ (a.leftAdjointUniq t).symm) =
      conjugateIsoEquiv (p.comp t) q c.symm := by
  rw [conjugateIsoEquiv_trans (p.comp a) (p.comp t) q,
    conjugateIsoEquiv_isoWhiskerLeft]
  simp [Adjunction.leftAdjointUniq]

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
