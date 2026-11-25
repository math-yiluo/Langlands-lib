/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Algebraic inverse image recovered from module-operation transport

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7.
(blueprint: lem-weil-pbc-algebraic-inverse-image-of-module-transport)
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The explicit operation-transport witnesses determine an algebraic inverse-image lift.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7.
(blueprint: lem-weil-pbc-algebraic-inverse-image-of-module-transport)
Proof: evaluate the binary-operation transport equations on a generalized pair to obtain
preservation of addition and scalar multiplication on all generalized sections. For the
regular module R, the underlying set sheaf is R itself. Let v be the inverse image of its
constant section 1 over a test sheaf Z. Product preservation lifts any pair consisting of
an inverse-image section of Z and a section a of A. Apply the transported identity r * 1 = r:
scalar multiplication a mapped to a • v is the composite of the two underlying set
isomorphisms A to L(R) to I(R), hence is injective. Apply transported module addition to
x + y and scalar multiplication to x * y in the regular module. Cancellation against v
then proves that eR transports ring addition and multiplication. The identities z = z + z
and 1 • v = v give preservation of zero and one. The same additive identity gives module
zero. All remaining data are exactly I, eI and eR.symm; the displayed equalities fix them. -/
theorem algebraicInverseImage_of_module_transport
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u})
    (eR : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ≅
      L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R))
    (I : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A))
    (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ L)
    (hI : ∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ∃ (addM : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
            CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
            AddCommGrpCat.{u})).obj M))
            (muM : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj M))
            (addI : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M)))
            (muI : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M))),
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose
        J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
        AddCommGrpCat.{u})).obj M)).obj.obj W),
        addM.hom.app W x = @Add.add (M.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          M)).hom.app W x) : M.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).obj.obj W),
        muM.hom.app W x = @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        addI.hom.app W x = @Add.add ((I.obj M).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M))).hom.app W x) : (I.obj M).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) :
          (I.obj M).val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        muI.hom.app W x = @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) : A.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) : (I.obj M).val.obj W)) ∧
          L.map addM = prodComparison L ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
            ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose
            J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M ∧
          L.map muM = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
            R) ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M) :
    ∃ AI : AlgebraicInverseImage L R A, AI.modules = I ∧
      AI.ringUnderlying = eR.symm ∧ HEq AI.moduleUnderlying eI := by
  classical
  let U := toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  let RR := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
  let M₀ := SheafOfModules.unit ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have hAdd (M : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (Z : Sheaf J (Type u)) :
      ∀ (a b z : Z ⟶ U.obj M),
        (∀ W t, @Eq (M.val.obj W) (z.hom.app W t)
          (@Add.add (M.val.obj W) inferInstance (a.hom.app W t) (b.hom.app W t))) →
        ∀ W t, @Eq ((I.obj M).val.obj W)
          ((L.map z ≫ eI.inv.app M).hom.app W t)
          (@Add.add ((I.obj M).val.obj W) inferInstance
            ((L.map a ≫ eI.inv.app M).hom.app W t)
            ((L.map b ≫ eI.inv.app M).hom.app W t)) := by
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections (T := Z) L (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun W x y ↦ @Add.add (M.val.obj W) inferInstance x y)
      (fun W x y ↦ @Add.add ((I.obj M).val.obj W) inferInstance x y) haM haI
  have hSmul (M : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (Z : Sheaf J (Type u)) :
      ∀ (a : Z ⟶ RR) (b z : Z ⟶ U.obj M),
        (∀ W t, @Eq (M.val.obj W) (z.hom.app W t)
          (@SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance
            (a.hom.app W t) (b.hom.app W t))) →
        ∀ W t, @Eq ((I.obj M).val.obj W)
          ((L.map z ≫ eI.inv.app M).hom.app W t)
          (@SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance
            ((L.map a ≫ eR.inv).hom.app W t)
            ((L.map b ≫ eI.inv.app M).hom.app W t)) := by
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections (T := Z) L eR (eI.app M) (eI.app M) muM muI hesI
      (fun W x y ↦ @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance x y)
      (fun W x y ↦ @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance x y)
      hsM hsI
  let one (Z : Sheaf J (Type u)) : Z ⟶ RR :=
    ⟨{ app := fun W ↦ ↾fun _ ↦ (1 : R.obj.obj W)
       naturality := by intro W W' f; ext t; exact (map_one (R.obj.map f).hom).symm }⟩
  let theta (W : Dᵒᵖ) (a : A.obj.obj W) : (I.obj M₀).val.obj W :=
    (eI.inv.app M₀).hom.app W (eR.hom.hom.app W a)
  have htheta (Z : Sheaf J (Type u)) (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W)
      (a : A.obj.obj W) :
      theta W a = a • (show (I.obj M₀).val.obj W from
        (L.map (one Z) ≫ eI.inv.app M₀).hom.app W t) := by
    let ev := sheafToPresheaf K (Type u) ⋙ (CategoryTheory.evaluation Dᵒᵖ (Type u)).obj W
    let F := L ⋙ ev
    let pairMap := prodComparison F Z RR ≫ (Types.binaryProductIso (F.obj Z) (F.obj RR)).hom
    obtain ⟨p, hp⟩ := surjective_of_epi pairMap (t, eR.hom.hom.app W a)
    have hp₁ : F.map (prod.fst : Z ⨯ RR ⟶ Z) p = t := by
      have hf : pairMap ≫ ↾_root_.Prod.fst = F.map prod.fst := by
        dsimp only [pairMap]
        rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
      rw [← hf]
      exact congrArg _root_.Prod.fst hp
    have hp₂ : F.map (prod.snd : Z ⨯ RR ⟶ RR) p = eR.hom.hom.app W a := by
      have hs : pairMap ≫ ↾_root_.Prod.snd = F.map prod.snd := by
        dsimp only [pairMap]
        rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
      rw [← hs]
      exact congrArg _root_.Prod.snd hp
    change (L.map (prod.fst : Z ⨯ RR ⟶ Z)).hom.app W p = t at hp₁
    change (L.map (prod.snd : Z ⨯ RR ⟶ RR)).hom.app W p = _ at hp₂
    have h := hSmul M₀ (Z ⨯ RR) prod.snd (prod.fst ≫ one Z) prod.snd (by
      intro V s
      change @Eq (R.obj.obj V) ((prod.snd : Z ⨯ RR ⟶ RR).hom.app V s)
        ((show R.obj.obj V from (prod.snd : Z ⨯ RR ⟶ RR).hom.app V s) * 1)
      exact (mul_one _).symm) W p
    simp only [L.map_comp] at h
    change (eI.inv.app M₀).hom.app W
        ((L.map (prod.snd : Z ⨯ RR ⟶ RR)).hom.app W p) =
      (show A.obj.obj W from eR.inv.hom.app W
        ((L.map (prod.snd : Z ⨯ RR ⟶ RR)).hom.app W p)) •
      (show (I.obj M₀).val.obj W from (eI.inv.app M₀).hom.app W
        ((L.map (one Z)).hom.app W
          ((L.map (prod.fst : Z ⨯ RR ⟶ Z)).hom.app W p))) at h
    rw [hp₁, hp₂] at h
    have hi : eR.inv.hom.app W (eR.hom.hom.app W a) = a :=
      congrArg (fun f ↦ f.hom.app W a) eR.hom_inv_id
    rw [hi] at h
    exact h
  have theta_injective (W : Dᵒᵖ) : Function.Injective (theta W) := by
    intro a b hab
    have h := congrArg (fun v ↦ eR.inv.hom.app W ((eI.hom.app M₀).hom.app W v)) hab
    have hi (a : A.obj.obj W) :
        eR.inv.hom.app W ((eI.hom.app M₀).hom.app W (theta W a)) = a := by
      have hi₁ := congrArg (fun f ↦ f.hom.app W (eR.hom.hom.app W a))
        (eI.app M₀).inv_hom_id
      have hi₂ := congrArg (fun f ↦ f.hom.app W a) eR.hom_inv_id
      change (eI.hom.app M₀).hom.app W (theta W a) = eR.hom.hom.app W a at hi₁
      rw [hi₁]
      exact hi₂
    simpa only [hi] using h
  have heval (Z : Sheaf J (Type u)) (a : Z ⟶ RR)
      (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W) :
      (L.map a ≫ eI.inv.app M₀).hom.app W t =
        (show A.obj.obj W from (L.map a ≫ eR.inv).hom.app W t) •
        (show (I.obj M₀).val.obj W from (L.map (one Z) ≫ eI.inv.app M₀).hom.app W t) := by
    rw [← htheta Z W t]
    change (eI.inv.app M₀).hom.app W ((L.map a).hom.app W t) =
      (eI.inv.app M₀).hom.app W
        (eR.hom.hom.app W (eR.inv.hom.app W ((L.map a).hom.app W t)))
    have hi := congrArg (fun f ↦ f.hom.app W ((L.map a).hom.app W t)) eR.inv_hom_id
    change eR.hom.hom.app W (eR.inv.hom.app W ((L.map a).hom.app W t)) = _ at hi
    rw [hi]
    rfl
  have hfaithful (Z : Sheaf J (Type u)) (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W)
      (a b : A.obj.obj W)
      (h : a • (show (I.obj M₀).val.obj W from
        (L.map (one Z) ≫ eI.inv.app M₀).hom.app W t) =
        b • (show (I.obj M₀).val.obj W from
          (L.map (one Z) ≫ eI.inv.app M₀).hom.app W t)) : a = b := by
    apply theta_injective W
    rw [htheta Z W t, htheta Z W t]
    exact h
  have hRingAdd (Z : Sheaf J (Type u)) (a b z : Z ⟶ RR)
      (hz : ∀ V s, @Eq (R.obj.obj V) (z.hom.app V s)
        (@Add.add (R.obj.obj V) inferInstance (a.hom.app V s) (b.hom.app V s))) :
      ∀ W t, @Eq (A.obj.obj W) ((L.map z ≫ eR.inv).hom.app W t)
        (@Add.add (A.obj.obj W) inferInstance
          ((L.map a ≫ eR.inv).hom.app W t) ((L.map b ≫ eR.inv).hom.app W t)) := by
    intro W t
    apply hfaithful Z W t
    have h := hAdd M₀ Z a b z hz W t
    rw [heval Z z W t, heval Z a W t, heval Z b W t] at h
    exact h.trans (add_smul _ _ _).symm
  have hRingMul (Z : Sheaf J (Type u)) (a b z : Z ⟶ RR)
      (hz : ∀ V s, @Eq (R.obj.obj V) (z.hom.app V s)
        (@Mul.mul (R.obj.obj V) inferInstance (a.hom.app V s) (b.hom.app V s))) :
      ∀ W t, @Eq (A.obj.obj W) ((L.map z ≫ eR.inv).hom.app W t)
        (@Mul.mul (A.obj.obj W) inferInstance
          ((L.map a ≫ eR.inv).hom.app W t) ((L.map b ≫ eR.inv).hom.app W t)) := by
    intro W t
    apply hfaithful Z W t
    have h := hSmul M₀ Z a b z hz W t
    rw [heval Z z W t, heval Z b W t] at h
    exact h.trans (mul_smul _ _ _).symm
  refine ⟨{
    ringUnderlying := eR.symm
    ringAdd := hRingAdd
    ringMul := hRingMul
    ringZero := ?_
    ringOne := ?_
    modules := I
    moduleUnderlying := eI
    moduleAdd := hAdd
    moduleZero := ?_
    moduleSMul := hSmul
  }, rfl, rfl, HEq.rfl⟩
  · intro Z a ha W t
    have h := hRingAdd Z a a a (by
      intro V s
      have hz : @Eq (R.obj.obj V) (a.hom.app V s) 0 := ha V s
      exact hz.trans ((zero_add (0 : R.obj.obj V)).symm.trans
        (congrArg₂ (fun a b : R.obj.obj V ↦ a + b) hz.symm hz.symm))) W t
    exact add_eq_left.mp h.symm
  · intro Z a ha W t
    have hsame : a = one Z := by
      ext V s
      exact ha V s
    subst a
    apply hfaithful Z W t
    have h := heval Z (one Z) W t
    exact h.symm.trans (one_smul (A.obj.obj W)
      (show (I.obj M₀).val.obj W from
        (L.map (one Z) ≫ eI.inv.app M₀).hom.app W t)).symm
  · intro M Z a ha W t
    have h := hAdd M Z a a a (by
      intro V s
      have hz : @Eq (M.val.obj V) (a.hom.app V s) 0 := ha V s
      exact hz.trans ((zero_add (0 : M.val.obj V)).symm.trans
        (congrArg₂ (fun a b : M.val.obj V ↦ a + b) hz.symm hz.symm))) W t
    exact add_eq_left.mp h.symm

end SheafOfModules
