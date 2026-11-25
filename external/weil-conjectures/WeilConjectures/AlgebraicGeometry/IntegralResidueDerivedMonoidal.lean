/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Strong monoidality of exact derived pullback

Source: derivation of the tensor comparison on flat resolutions; compare the proved
Etale.Derived.UpperStarMonoidal construction in the source library.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u u₁ u₂
open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

@[instance_reducible] noncomputable def residueDerivedOplax : F.leftDerivedFunctor.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    (F.leftDerivedTensorComparison_app_app_comp_tensorHom)
    F.kFlatMap (exists_kFlatMap_iso F)
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

theorem residueDerivedOplax_isIso_δ (X Y : DerivedCategory C) :
    letI := residueDerivedOplax F
    IsIso (OplaxMonoidal.δ F.leftDerivedFunctor X Y) :=
  inferInstanceAs (IsIso ((F.leftDerivedTensorComparison.app X).app Y))

theorem residueDerivedOplax_isIso_η :
    letI := residueDerivedOplax F
    IsIso (OplaxMonoidal.η F.leftDerivedFunctor) := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have : IsIso (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [mapHomotopyCategory_η]
    infer_instance
  exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map (LaxMonoidal.ε Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
        CategoryTheory.inv (LaxMonoidal.ε Qh)))

/-- The canonical strong monoidal structure obtained by deriving the ordinary
strong monoidal comparison. All coherence laws are descended on flat resolutions. -/
@[instance_reducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  -- through the inverse tensor isomorphisms of CoreMonoidal.
  exact { (CoreMonoidal.ofOplaxMonoidal _).toMonoidal with
    toOplaxMonoidal := residueDerivedOplax F }

/-- The derived tensorator satisfies the defining tensor/counit square.
Source: the defining comparison equation of the exact left derived tensor functor.
(auxiliary; not a blueprint node) -/
theorem residueDerivedMonoidal_counit (P Q : HomotopyCategory C (.up ℤ)) :
    letI := residueDerivedMonoidal F
    OplaxMonoidal.δ F.leftDerivedFunctor (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Q) ≫
      (F.leftDerivedFunctorCounit.app P ⊗ₘ F.leftDerivedFunctorCounit.app Q) ≫
      LaxMonoidal.μ DerivedCategory.Qh
        ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
    F.leftDerivedFunctor.map (LaxMonoidal.μ DerivedCategory.Qh P Q) ≫
      F.leftDerivedFunctorCounit.app (P ⊗ Q) ≫
      DerivedCategory.Qh.map
        (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q) := by
  exact F.leftDerivedTensorComparison_app_app_comp_tensorHom P Q

end CategoryTheory.Functor

universe v

open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_integralResidueDerivedMonoidal
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

section CanonicalPullback

-- Keep the ordinary module tensor data identical to the presentation interface.
attribute [local instance 20000] sheafBraidedCategory

/-- A named copy of the existing integral derived monoidal structure.
This keeps repeated occurrences of the large internal-module instance compact;
its data are exactly the existing derived monoidal instance. -/
@[instance_reducible] noncomputable def residueExchangeIntegralDerivedMonoidal (T : Scheme.{u}) :
    MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
  inferInstance

/-- The actual derived module pullback with the strong monoidal structure induced
from an ordinary pullback structure and preservation of flat modules. -/
@[instance_reducible] noncomputable def residueExchangePullMonoidal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal := by
  letI := m
  letI := hFlat
  unfold residueExchangeUpperStar
  exact (f)^*⟦integralCoeff ℓ E⟧.residueDerivedMonoidal

end CanonicalPullback

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical derived tensor structure on modules with condensed coefficients.
This alias caches the existing instance without changing its data or registering an instance. -/
@[instance_reducible]
noncomputable def projectionDerivedMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing

/-! These caches select the existing internal-module structures and the existing tensor
colimit instances from `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory` and
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`. They introduce no new
choices and are registered only locally by their users. -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The existing abelian structure on module objects, cached at the coefficient ring. -/
@[instance_reducible]
noncomputable def projectionModuleAbelian (X : Scheme.{u}) :
    Abelian (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  inferInstance

/-- The existing relative tensor structure on module objects, cached at the coefficient ring. -/
@[instance_reducible]
noncomputable def projectionModuleMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

/-- The existing derived-category model on module objects, cached at the coefficient ring. -/
@[instance_reducible]
noncomputable def projectionModuleHasDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The existing tensor on abelian pro-étale sheaves. -/
@[instance_reducible]
noncomputable def projectionSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- The existing transported multiplication on condensed coefficient objects. -/
@[instance_reducible]
noncomputable def projectionCoefficientMonObj (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  inferInstance

/-- The existing category of internal modules. -/
@[instance_reducible]
noncomputable def projectionModuleCategory (X : Scheme.{u}) :
    Category.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
