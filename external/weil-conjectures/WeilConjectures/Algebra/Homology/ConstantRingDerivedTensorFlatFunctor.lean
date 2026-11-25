/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.Algebra.Homology.ConstantRingTensorRepresentatives
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor

/-! # Derived tensor computation under a flat-preserving monoidal functor

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 06YT and 0G7E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.ConstantScalarRestriction

attribute [local instance] complexTensorMemo derivedTensorMemo

private local instance nativeSmallColimits {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A] :
    HasColimitsOfSize.{0, 0} (Modules J A) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} (Modules J A)

-- Check the localization circuit with abstract categories, before its site specialization.
private def localizationTensorIso
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory D']
    (L : C ⥤ C') (Q : D ⥤ D') [Q.LaxMonoidal]
    (F : C ⥤ D) (H : C' ⥤ D') (α : L ⋙ H ≅ F ⋙ Q)
    (P N : C) (β : F.obj (P ⊗ N) ≅ F.obj P ⊗ F.obj N)
    [IsIso (Functor.LaxMonoidal.μ Q (F.obj P) (F.obj N))] :
    H.obj (L.obj (P ⊗ N)) ≅ H.obj (L.obj P) ⊗ H.obj (L.obj N) :=
  α.app (P ⊗ N) ≪≫ Q.mapIso β ≪≫
    (asIso (Functor.LaxMonoidal.μ Q (F.obj P) (F.obj N))).symm ≪≫
      tensorIso (α.app P).symm (α.app N).symm

section AbstractCochains

attribute [local instance] complexTensorStructMemo derivedTensorStructMemo
universe uD vD uE vE dD dE

private theorem nativeCochainTensorComparison
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    [IsGrothendieckAbelian.{vD} D] [IsGrothendieckAbelian.{vE} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [SymmetricCategory D] [SymmetricCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{dD} D] [HasDerivedCategory.{dE} E]
    (F : D ⥤ E) [F.Additive] [F.Monoidal] [F.IsLeftAdjoint] [F.PreservesFlat]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P N : CochainComplex D ℤ)
    (hN : N.IsKFlatForTotalTensor) (hf : ∀ i, ObjectProperty.flat (N.X i)) :
    Nonempty (F.mapDerivedCategory.obj (DerivedCategory.Q.obj (P ⊗ N)) ≅
      F.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⊗
        F.mapDerivedCategory.obj (DerivedCategory.Q.obj N)) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  have hFN := F.kFlat_map_of_flat_terms N hN hf
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (Fc.obj P) (Fc.obj N)) :=
    ConstantScalarRestriction.nativeTensorIso (Fc.obj P) (Fc.obj N) hFN
  exact ⟨localizationTensorIso DerivedCategory.Q DerivedCategory.Q Fc F.mapDerivedCategory
    F.mapDerivedCategoryFactors P N (F.mapCochainComplexμIso P N).symm⟩

end AbstractCochains

/-- An exact flat-preserving monoidal left adjoint computes the published constant-ring
unbounded derived tensor as the native tensor of its images.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 06YT and 0G7E.
(auxiliary; not a blueprint node).

Proof: choose flat-term K-flat representatives of both inputs. The published tensor's
cochain comparison computes their tensor. Flat-term K-flat preservation makes the
second image K-flat, so the target localization tensorator is invertible. Compose the
source comparison, exact-functor localization factors, the monoidal cochain comparison,
and that inverse tensorator. Map the two representative isomorphisms to finish. This
uses no boundedness, finiteness or flatness assumption on the derived inputs. -/
theorem constantRingDerivedTensorComparison {C D : Type w} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (T : GrothendieckTopology D)
    (A : Type w) [CommRing A]
    [HasDerivedCategory (Modules J A)]
    [HasDerivedCategory (Sheaf T (ModuleCat.{w} A))]
    (F : Modules J A ⥤ Sheaf T (ModuleCat.{w} A))
    [F.Additive] [F.Monoidal] [F.PreservesFlat] [F.IsLeftAdjoint]
    [PreservesFiniteLimits F]
    (K L : DerivedCategory (Modules J A)) :
    Nonempty (F.mapDerivedCategory.obj
        (((SheafOfModules.KFlatFixedTensor.derivedTensor (ring J A)).obj K).obj L) ≅
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L) := by
  let R := ring J A
  let H := F.mapDerivedCategory
  obtain ⟨P, N, ⟨s⟩, ⟨p⟩, ⟨n⟩⟩ := constantRingTensorRepresentatives J A K L
  have hk : N.obj.IsKFlatForTotalTensor :=
    (ConstantScalarRestriction.kflat_iff J A N.obj).2.1.mp N.property.1
  have hf (i : ℤ) : ObjectProperty.flat (N.obj.X i) := by
    apply (ConstantScalarRestriction.rightFlat_iff _).2
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (N.obj.X i)) (N.property.2 i)
  let i := (nativeCochainTensorComparison F P.obj N.obj hk hf).some
  exact ⟨H.mapIso s ≪≫ i ≪≫
    tensorIso (H.mapIso p) (H.mapIso n)⟩

end CategoryTheory.ConstantScalarRestriction
