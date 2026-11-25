/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Perfect scalar models under arbitrary coefficient change

The scalar ring and constant-sheaf extension are the existing local-model API.
Finite projectivity is expressed by a splitting off a finite free scalar module,
including rank zero. The derived functor is ordinary and uncompleted.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance 0] CompleteLattice.hasFiniteColimits_of_semilatticeSup_orderBot
  Preorder.instHasColimitsOfShape

attribute [local instance 2000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint pointUpperStar
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
/-- The termwise scalar model, using the canonical constant-to-coefficient map. -/
noncomputable def sfbScalarModelComplex (X : Scheme.{u})
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ) :
    CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ :=
  letI : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits (scalarConstant X) :=
    inferInstanceAs (PreservesFiniteColimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
        (pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X))))
  letI : PreservesFiniteColimits (finiteConstantScalarExtension Λ X) :=
    inferInstanceAs (PreservesFiniteColimits
      ((scalarConstant X).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars (scalarCoefficientHom Λ X)))
  ((finiteConstantScalarExtension Λ X).mapHomologicalComplex (.up ℤ)).obj C

private instance scalarConstant_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (scalarConstant X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold scalarConstant upperStarFromPoint
  infer_instance

private instance scalarExtension_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteConstantScalarExtension Λ X) := by
  unfold finiteConstantScalarExtension
  infer_instance

private instance scalarExtension_additive (X : Scheme.{u}) :
    (finiteConstantScalarExtension Λ X).Additive := by
  have : PreservesBinaryBiproducts (finiteConstantScalarExtension Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def scalarFreeIso (X : Scheme.{u}) (n : ℕ) :
    (finiteConstantScalarExtension Λ X).obj (Mod.finiteFree (scalarRingObj Λ) n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  (finiteConstantScalarExtension Λ X).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular (scalarRingObj Λ)) ≪≫
    biproduct.mapIso (fun _ ↦
      (Mod.extendScalars (scalarCoefficientHom Λ X)).mapIso
        (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
      Mod.regularExtensionIso (scalarCoefficientHom Λ X))

attribute [local irreducible] Mod.extendScalars scalarConstant finiteConstantScalarExtension
attribute [local irreducible] ObjectProperty.flat HomologicalComplex.quasiIso
  MorphismProperty.kFlat

private noncomputable def scalarRightAdjoint (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar) ⋙
    (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (Opposite.op (Profinite.of PUnit.{u + 1}))

private noncomputable def scalarAdjunction (X : Scheme.{u}) :
    scalarConstant X ⊣ scalarRightAdjoint X := by
  simpa only [scalarConstant, upperStarFromPoint, scalarRightAdjoint] using
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).comp (pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)))

end AlgebraicGeometry.ProEtale
