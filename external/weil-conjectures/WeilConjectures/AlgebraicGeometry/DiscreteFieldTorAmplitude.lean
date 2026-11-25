/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.AlgebraicGeometry.IntegralResidueModelComparison

/-! # Finite Tor amplitude over a discrete field

Over the pulled-back discrete ring of a field, every internal module is flat, so every bounded
complex has finite Tor amplitude.

Source: Stacks Project, Tags 03ER, 08FC and 0651; Bhatt--Scholze, Remark 6.3.2.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Over the pulled-back discrete ring of a field, every internal module is flat.
Source: Stacks Project, Tags 03ER and 08FC (auxiliary; not a blueprint node).

Proof: the discrete coefficient model `discrete_coefficient_model` is a monoidal equivalence
onto module sheaves over a constant field sheaf, where every module is flat by
`SheafOfModules.isFlat_constantFieldModule`. Right tensoring with `M` followed by the
equivalence is right tensoring with the image of `M` after the equivalence, so it is exact, and
the equivalence reflects exactness. -/
theorem flat_of_discreteField (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [Field A]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X)) :
    ObjectProperty.flat M := by
  obtain ⟨c, -, ⟨hm⟩, -⟩ :=
    discrete_coefficient_model X A (ULift.{u + 1} A) (RingEquiv.refl _)
  let F := discreteCoefficientModel X A (ULift.{u + 1} A) c
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let R := ConstantCompletion.constant J (ULift.{u + 1} A)
  let := SheafOfModules.monoidalCategory R
  have hN : exactFunctor _ _ (MonoidalCategory.tensorRight (F.obj M)) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (F.obj M))
      (SheafOfModules.isFlat_constantFieldModule J (ULift.{u + 1} A) (F.obj M))
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (F.obj M)) := hN.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M ⋙ F) :=
    preservesFiniteLimits_of_natIso (Functor.Monoidal.commTensorRight F M)
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M) :=
    preservesFiniteLimits_of_reflects_of_preserves _ F
  exact (ObjectProperty.flat_iff_preservesFiniteLimits M).mpr
    (preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm)

/-- Over the pulled-back discrete ring of a field, a bounded complex has finite Tor amplitude.
Source: Stacks Project, Tags 0651 and 08FC; Bhatt--Scholze, Remark 6.3.2
(auxiliary; not a blueprint node).

Proof: a complex with homology in `[a, b]` is represented by a complex concentrated in
degrees `[a, b]`, whose terms are flat by `flat_of_discreteField`, so it has Tor amplitude in
`[a, b]` by `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`. -/
theorem finiteTorAmplitude_of_discreteField (X : Scheme.{u}) [IsNoetherian X]
    (A : Type u) [Field A]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X))}
    (hK : DerivedCategory.TStructure.t.bounded K) :
    DerivedCategory.finiteTorAmplitude _ K := by
  have := residueFlatResolution X (condensedRingObj (discreteObj A) X)
  obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hK
  obtain ⟨P, _, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE K a b
  exact ⟨a, b, (DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).mpr
    ⟨P, inferInstance, inferInstance, fun n ↦ flat_of_discreteField X A (P.X n),
      ⟨e.symm⟩⟩⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
