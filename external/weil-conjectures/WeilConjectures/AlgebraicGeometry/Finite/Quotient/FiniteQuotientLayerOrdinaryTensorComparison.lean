/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels

public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexesChartHomology
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantRealizationScalarRestriction
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientConstantTensorComparison

/-! # Ordinary constant tensor compatibility for the finite coefficient layer

Source: Stacks Project, Tags 03EK, 03EL and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t uC vC uD vD uE vE uH vH
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

open MonoidalCategory
open scoped TensorProduct
attribute [local instance] ULift.algebra'
attribute [local irreducible] completedAdicChangeData
  SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

@[irreducible] private def layerCoefficientRestriction (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ) :
    finiteCoefficientConstantFunctor X D φD ⋙ SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ) ≅
      ModuleCat.restrictScalars f ⋙ finiteCoefficientConstantFunctor X B φB := by
  let H := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map φB)
  have : G.IsEquivalence := restrictionIsEquivalence X (H.mapIso (asIso φB))
  have hh : H.map φB ≫ H.map ψ = adicModuleMap X f ≫ H.map φD := by
    change H.map φB ≫ H.map ψ = H.map (adicConstantMap X f) ≫ H.map φD
    rw [← H.map_comp, ← H.map_comp, h]
  let e : finiteCoefficientConstantFunctor X D φD ⋙
        SheafOfModules.restrictScalars (H.map ψ) ⋙ G ≅
      ModuleCat.restrictScalars f ⋙ finiteCoefficientConstantFunctor X B φB ⋙ G :=
    Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (restrictionCompIso X (H.map φB) (H.map ψ)).symm ≪≫
      Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) hh)) ≪≫
      Functor.isoWhiskerLeft (finiteCoefficientConstantFunctor X D φD)
        (restrictionCompIso X (adicModuleMap X f) (H.map φD)) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (baseConstantFunctor X D) (changeUnitIso X φD).symm)
        (SheafOfModules.restrictScalars (adicModuleMap X f)) ≪≫
      (constantRealization_restrictScalars X f).some.symm ≪≫
      Functor.isoWhiskerLeft (ModuleCat.restrictScalars f ⋙ baseConstantFunctor X B)
        (changeUnitIso X φB)
  exact Functor.fullyFaithfulCancelRight G e

private theorem layerTensor_eq {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    finiteQuotientLayerTensor I n =
      tensorLeft (finiteQuotientLayerModule I n) ⋙ ModuleCat.restrictScalars
        (adicQuotientMap I (n + 1 + 1) (0 + 1)
          (Nat.succ_le_succ (Nat.zero_le (n + 1)))) := rfl

private theorem tensorRestrictionComparison
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    {E : Type uE} [Category.{vE} E] {H : Type uH} [Category.{vH} H]
    (F : C ⥤ D) (G : D ⥤ E) (U : C ⥤ H) (V : H ⥤ E) (L : C)
    (eT : F ⋙ tensorRight (F.obj L) ≅ tensorRight L ⋙ F)
    (eR : F ⋙ G ≅ U ⋙ V) :
    Nonempty (F ⋙ tensorRight (F.obj L) ⋙ G ≅ tensorLeft L ⋙ U ⋙ V) := by
  let s : tensorRight L ≅ tensorLeft L :=
    NatIso.ofComponents (fun M ↦ (β_ M L)) (by
      intro M N f
      exact BraidedCategory.braiding_naturality_left f L)
  exact ⟨Functor.isoWhiskerRight eT G ≪≫
    Functor.isoWhiskerLeft (tensorRight L) eR ≪≫ Functor.isoWhiskerRight s (U ⋙ V)⟩

/-- Ordinary tensor with the constant residue layer agrees with constant
realization of the explicit algebraic layer tensor, retaining the successor action.

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL; Cohomology on Sites,
Tag 094I, the ordinary constant ideal-layer tensor calculation.
(blueprint: lem-weil-pbc-finite-quotient-layer-ordinary-tensor-comparison).

Proof: constant module sheafification preserves tensor products. Lifting modules
by ULift commutes with tensor by the canonical lifted pure-tensor equivalence;
extension along phi_0 also preserves tensor by balanced scalar extension.
These comparisons identify C(P) tensor C(L) with C(P tensor L), naturally in P.
Apply the symmetry to obtain C(L tensor P). Restriction along the successor to
residue coefficient map agrees with constant realization after the algebraic
quotient B -> C: cancel the constant quotient map from A in hc.2 to obtain this
coefficient square. Extension along the isomorphism phi_(n+1) transports the
square to the actual successor coefficient sheaf. These maps commute with all
module morphisms since on local constant generators they send x tensor l to
l tensor x; local tensor generation and sheafification determine the maps.
No flatness, projectivity, boundedness or finiteness assumption on P or L is
used. Zero layers, zero rings and empty sites use the same universal properties. -/
theorem finiteQuotient_layer_ordinary_tensor_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ k : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (k + 1)) ⟶
      completedAdicFiniteCommRing X d k)
    (hφ : ∀ k : ℕ, IsIso (φ k))
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory (completedAdicFiniteCommRing X d 0)
    Nonempty
      (finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0) ⋙
          MonoidalCategory.tensorRight
            ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0)).obj
              (finiteQuotientLayerModule d.ideal n)) ⋙
          SheafOfModules.restrictScalars.{t + 1}
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
                (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _))) ≅
        finiteQuotientLayerTensor d.ideal n ⋙
          finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1)))  := by
  let := SheafOfModules.monoidalCategory (completedAdicFiniteCommRing X d 0)
  let (k : ℕ) : IsIso (φ k) := hφ k
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let D := A ⧸ d.ideal ^ (0 + 1)
  let L := finiteQuotientLayerModule d.ideal n
  let q : B →+* D := adicQuotientMap d.ideal (n + 1 + 1) (0 + 1)
    (Nat.succ_le_succ (Nat.zero_le (n + 1)))
  let ψ := completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _)
  let T := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)
  have e : finiteCoefficientConstantFunctor X D (φ 0) ⋙ T ≅
      ModuleCat.restrictScalars q ⋙ finiteCoefficientConstantFunctor X B (φ (n + 1)) :=
    layerCoefficientRestriction X (φ (n + 1)) (φ 0) q ψ
      (residueCoefficient_square X d φ hc (n + 1))
  rw [layerTensor_eq]
  exact tensorRestrictionComparison
    (finiteCoefficientConstantFunctor X D (φ 0)) T
    (ModuleCat.restrictScalars q) (finiteCoefficientConstantFunctor X B (φ (n + 1))) L
    (finiteCoefficient_constant_tensor_comparison X D (φ 0) L).some e

end AlgebraicGeometry.Scheme
