/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Normalized ordinary and derived scalar models

Source: Stacks 03D7, 06YY, 0FND and 09T5; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Exactness of scalar restriction, with no flatness of the ring map.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-scalar-model).
Proof: the underlying abelian sheaf and all its maps are unchanged. Kernels and
sheafified cokernels therefore coincide with those before restriction. -/
theorem systemScalarRestriction_exact {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ∧
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) := by
  let R' := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let S' := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S
  let F := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  have : PreservesFiniteColimits (toSheaf.{w} R') :=
    inferInstance
  have : PreservesFiniteColimits (toSheaf.{w} S') :=
    inferInstance
  have : PreservesFiniteLimits (F ⋙ toSheaf R') := by
    change PreservesFiniteLimits (toSheaf S')
    infer_instance
  have : PreservesFiniteColimits (F ⋙ toSheaf R') := by
    change PreservesFiniteColimits (toSheaf S')
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf R')⟩

/-- Exact restriction preserves finite limits. Source: Stacks 03DA
(blueprint: lem-pur-system-scalar-model). -/
instance systemScalarRestrictionLimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).1
/-- Exact restriction preserves finite colimits. Source: Stacks 03DA
(blueprint: lem-pur-system-scalar-model). -/
instance systemScalarRestrictionColimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).2

/-- Standard localization at a coefficient level; no restriction on cohomological bounds.
Source: Stacks 05RU (blueprint: lem-pur-system-scalar-model). -/
instance systemRingHasDerived (R : Sheaf J CommRingCat.{w}) :
    HasDerivedCategory (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :=
  HasDerivedCategory.standard _
variable [EssentiallySmall.{w} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local pure tensor in the ordinary functor of the recorded derived-change model.
The scalar is first, as in the project's change-of-rings construction.
Source: Stacks 03EK and 03D7 (blueprint: lem-pur-system-scalar-model). -/
def systemModelTmul {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (D : DerivedChangeOfRingsCochainModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : S.obj.obj U) (x : P.val.obj U) : (D.E.obj P).val.obj U :=
  c • (eqToHom (D.obj_eq P).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ P).presheaf).app U
      (((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (P.val.obj U)) x))

/-- The recorded derived-change-of-rings model together with its actual scalar
adjunctions. The ordinary unit is fixed on local generators and the derived transpose
is fixed by the universal counit on complexes.
Source: Stacks 03D7, 06YY, 0FND and 09T5
(blueprint: lem-pur-system-scalar-model). -/
structure SystemScalarModel {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) where
  model : DerivedChangeOfRingsCochainModel φ
  ordinaryAdj : model.E ⊣ restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  unit_normalized : ∀ P U (x : P.val.obj U),
    (ordinaryAdj.unit.app P).val.app U x = systemModelTmul model P U 1 x
  adjunction : model.T ⊣ (restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategory
  transpose : ∀ P K (f : (model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (model.ε.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (restrictScalars.{w} ((sheafCompose J
          (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategoryFactors.inv.app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual coefficient map has a scalar model with normalized ordinary and derived
adjunctions. Source: Stacks 03D7, 06YY and 0FND
(blueprint: lem-pur-system-scalar-model).
Proof: use the existing cochain derived-change-of-rings universal pair. Descend its
comparison through the homotopy quotient and transfer its universal property. The ordinary
coefficient adjunction fixes the unit on local generators. The existing derived Hom
comparison gives the normalized derived adjunction on homotopy representatives; transporting
its equation back to complexes gives the required equation for every complex and chain map.
No flatness of the coefficient map or of the complex is required. -/
theorem nonempty_systemScalarModel {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    Nonempty (SystemScalarModel φ) := by
  classical
  obtain ⟨D⟩ := nonempty_derivedChangeOfRingsCochainModel φ
  obtain ⟨ε, hε, hεP⟩ :=
    exists_homotopy_leftDerived_comparison D.E D.T D.ε D.universal
  obtain ⟨_, _, ho⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, ha⟩ := ho D.E D.obj_eq D.map_eq
  obtain ⟨d, hd⟩ := sheafRingDerivedHomComparison φ D.E D.obj_eq D.map_eq a D.T ε hε
  refine ⟨{ model := D
            ordinaryAdj := a
            unit_normalized := ?_
            adjunction := d
            transpose := adjunction_cochain_transpose D.E _ a D.T D.ε ε
              (fun P ↦ by
                apply (Iso.eq_comp_inv ((DerivedCategory.quotientCompQhIso
                  (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))).app
                    ((D.E.mapHomologicalComplex (.up ℤ)).obj P))).1
                simpa only [Iso.app_inv, Category.assoc] using hεP P) d hd }⟩
  intro P U x
  have hu := ha P (D.E.obj P) (eqToHom (D.obj_eq P).symm) U x
  dsimp only [systemModelTmul]
  rw [one_smul]
  have ht : ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
      (P.val.obj U)) x =
        (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x := rfl
  rw [ht]
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
  exact hu

end SheafOfModules
