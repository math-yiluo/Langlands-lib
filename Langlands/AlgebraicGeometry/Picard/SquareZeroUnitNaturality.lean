import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitCohomology
import Langlands.AlgebraicGeometry.Modules.AbelianSheafCohomologyNaturality

/-! # Actual unit boundaries for nested square-zero thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroUnitNaturality

open NilpotentUnitReduction SquareZeroUnitKernels StructureKernelModule
open SquareZeroUnitExactSequence SquareZeroUnitCohomology
open Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y)

/-- The actual structure map between the two ring sheaves pushed to `X`. -/
def quotientStructureMap :
    (Opens.map i.base).op ⋙ Y.presheaf ⟶
      (Opens.map (j ≫ i).base).op ⋙ Z.presheaf :=
  Functor.whiskerLeft (Opens.map i.base).op j.c

/-- Inclusion of actual section kernels under further restriction. -/
def kernelModuleMap : kernelModule i ⟶ kernelModule (j ≫ i) :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun a ↦ ⟨a.val, by
            change (j.app ((Opens.map i.base).obj U.unop)).hom
              ((i.app U.unop).hom a.val) = 0
            erw [a.property, map_zero]⟩
          map_zero' := by rfl
          map_add' := by intros; rfl }
      naturality := by
        intros
        ext a
        rfl }
    (by
      intros
      rfl)⟩

@[simp]
lemma kernelModuleMap_app (U : X.Opens) (a : Γ(kernelModule i, U)) :
    ((kernelModuleMap i j).app U a).val = a.val := rfl

/-- Cohomology of the actual inclusion of kernel modules on `X`. -/
def idealCohomologyMap (n : ℕ) : idealCohomology i n →+ idealCohomology (j ≫ i) n :=
  ((Modules.DerivedSections.cohomology X n).map (kernelModuleMap i j)).hom.toAddMonoidHom

variable [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)]

/-- The actual unit map between the quotient ring sheaves pushed to `X`. -/
def quotientUnitsMap :
    unitsSheaf ((Opens.map i.base).op ⋙ Y.presheaf)
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property) ⟶
      unitsSheaf ((Opens.map (j ≫ i).base).op ⋙ Z.presheaf)
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf (j ≫ i).base Z.sheaf.property) :=
  unitsSheafMap (quotientStructureMap i j) _ _

omit [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)] in
@[reassoc]
lemma unitsReduction_comp :
    unitsReduction i ≫ quotientUnitsMap i j = unitsReduction (j ≫ i) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  rfl

variable (hi : i.ker ^ 2 = ⊥) (hji : (j ≫ i).ker ^ 2 = ⊥)

@[reassoc]
lemma kernelModuleMap_oneAdd :
    (toAbSheaf X).map (kernelModuleMap i j) ≫ schemeOneAdd (j ≫ i) hji =
      schemeOneAdd i hi := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/-- The kernel inclusion, with the exact unit-sequence endpoints. -/
def sequenceKernelMap :
    (schemeUnitSequence i hi).X₁ ⟶ (schemeUnitSequence (j ≫ i) hji).X₁ :=
  (toAbSheaf X).map (kernelModuleMap i j)

/-- The quotient-unit map, with the exact unit-sequence endpoints. -/
def sequenceQuotientMap :
    (schemeUnitSequence i hi).X₃ ⟶ (schemeUnitSequence (j ≫ i) hji).X₃ :=
  quotientUnitsMap i j

/-- The identity on ambient units, given through the common explicit sheaf. -/
def sequenceMiddleMap :
    (schemeUnitSequence i hi).X₂ ⟶ (schemeUnitSequence (j ≫ i) hji).X₂ :=
  𝟙 (unitsSheaf X.presheaf X.sheaf.property)

lemma sequenceKernelMap_comm :
    sequenceKernelMap i j hi hji ≫ (schemeUnitSequence (j ≫ i) hji).f =
      (schemeUnitSequence i hi).f ≫ sequenceMiddleMap i j hi hji := by
  dsimp only [schemeUnitSequence, sequenceKernelMap, sequenceMiddleMap]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.toMul.injective
  apply Units.ext
  rfl

lemma sequenceQuotientMap_comm :
    sequenceMiddleMap i j hi hji ≫ (schemeUnitSequence (j ≫ i) hji).g =
      (schemeUnitSequence i hi).g ≫ sequenceQuotientMap i j hi hji := by
  dsimp only [schemeUnitSequence, sequenceQuotientMap, sequenceMiddleMap]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  rfl

/-- The actual morphism of square-zero unit sequences on the common ambient scheme. -/
def unitSequenceMap : schemeUnitSequence i hi ⟶ schemeUnitSequence (j ≫ i) hji :=
  ShortComplex.homMk (S₁ := schemeUnitSequence i hi)
    (S₂ := schemeUnitSequence (j ≫ i) hji) (sequenceKernelMap i j hi hji) (sequenceMiddleMap i j hi hji)
    (sequenceQuotientMap i j hi hji)
    (sequenceKernelMap_comm i j hi hji) (sequenceQuotientMap_comm i j hi hji)

/-- Naturality of Mathlib's actual connecting map for these unit sequences. -/
lemma delta_naturality (n : ℕ)
    (a : Sheaf.H.{u} (schemeUnitSequence i hi).X₃ n) :
    Sheaf.H.δ (schemeUnitSequence_shortExact (j ≫ i) hji) n (n + 1) rfl
        (Sheaf.H.map (quotientUnitsMap i j) n a) =
      Sheaf.H.map ((toAbSheaf X).map (kernelModuleMap i j)) (n + 1)
        (Sheaf.H.δ (schemeUnitSequence_shortExact i hi) n (n + 1) rfl a) :=
  Sheaf.H.δ_naturality n (n + 1) rfl
    (schemeUnitSequence_shortExact i hi) (schemeUnitSequence_shortExact (j ≫ i) hji)
    (unitSequenceMap i j hi hji) a

/-- The actual connecting map on the ambient space, with target module cohomology. -/
def pushedBoundaryMap (n : ℕ) :
    Sheaf.H.{u} (schemeUnitSequence i hi).X₃ n →+ idealCohomology i (n + 1) :=
  (idealCohomologyAddEquiv i (n + 1)).toAddMonoidHom.comp
    (Sheaf.H.δ (schemeUnitSequence_shortExact i hi) n (n + 1) rfl)

/-- The actual ambient-space boundary commutes with the actual ideal-module map. -/
lemma pushedBoundaryMap_naturality (n : ℕ)
    (a : Sheaf.H.{u} (schemeUnitSequence i hi).X₃ n) :
    pushedBoundaryMap (j ≫ i) hji n (Sheaf.H.map (quotientUnitsMap i j) n a) =
      idealCohomologyMap i j (n + 1) (pushedBoundaryMap i hi n a) := by
  change idealCohomologyAddEquiv (j ≫ i) (n + 1)
      (Sheaf.H.δ (schemeUnitSequence_shortExact (j ≫ i) hji) n (n + 1) rfl
        (Sheaf.H.map (quotientUnitsMap i j) n a)) =
    (Modules.DerivedSections.cohomology X (n + 1)).map (kernelModuleMap i j)
      (idealCohomologyAddEquiv i (n + 1)
        (Sheaf.H.δ (schemeUnitSequence_shortExact i hi) n (n + 1) rfl a))
  rw [delta_naturality i j hi hji]
  exact Modules.AbelianSheafComparison.HAddEquiv_naturality X
    (kernelModuleMap i j) (n + 1) _

/-- The quotient-unit cohomology map transported through the existing pushforward
comparisons on the common ambient space `X`. -/
def quotientUnitCohomologyMap (n : ℕ) : unitCohomology Y n →+ unitCohomology Z n :=
  (UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
      (j ≫ i) ⟨2, hji⟩ n).toAddMonoidHom.comp
    ((Sheaf.H.map (quotientUnitsMap i j) n).comp
      (UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
        i ⟨2, hi⟩ n).symm.toAddMonoidHom)

/-- Naturality of the existing square-zero boundary in actual ideal-module cohomology. -/
lemma boundaryMap_naturality (n : ℕ) (y : unitCohomology Y n) :
    boundaryMap (j ≫ i) hji n (quotientUnitCohomologyMap i j hi hji n y) =
      idealCohomologyMap i j (n + 1) (boundaryMap i hi n y) := by
  change idealCohomologyAddEquiv (j ≫ i) (n + 1)
      (Sheaf.H.δ (schemeUnitSequence_shortExact (j ≫ i) hji) n (n + 1) rfl
        ((UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
          (j ≫ i) ⟨2, hji⟩ n).symm
          ((UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
            (j ≫ i) ⟨2, hji⟩ n)
            (Sheaf.H.map (quotientUnitsMap i j) n
              ((UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
                i ⟨2, hi⟩ n).symm y))))) = _
  rw [AddEquiv.symm_apply_apply]
  exact pushedBoundaryMap_naturality i j hi hji n _

/-- The transported quotient map commutes with actual ambient unit reduction. -/
lemma quotientUnitCohomologyMap_reductionMap (n : ℕ) (x : unitCohomology X n) :
    quotientUnitCohomologyMap i j hi hji n (reductionMap i hi n x) =
      reductionMap (j ≫ i) hji n x := by
  change (UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
      (j ≫ i) ⟨2, hji⟩ n)
      (Sheaf.H.map (quotientUnitsMap i j) n
        ((UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
          i ⟨2, hi⟩ n).symm
          ((UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
            i ⟨2, hi⟩ n) (Sheaf.H.map (unitsReduction i) n x)))) =
    (UnitSheafPushforward.nilpotentUnitsCohomologyPushforwardEquiv
      (j ≫ i) ⟨2, hji⟩ n) (Sheaf.H.map (unitsReduction (j ≫ i)) n x)
  rw [AddEquiv.symm_apply_apply, ← Sheaf.H.map_comp_apply, unitsReduction_comp]

/-- Naturality of the actual `1+a` cohomology maps under enlargement of the ideal. -/
lemma oneAddMap_naturality (n : ℕ) (a : idealCohomology i n) :
    oneAddMap (j ≫ i) hji n (idealCohomologyMap i j n a) = oneAddMap i hi n a := by
  change Sheaf.H.map (schemeOneAdd (j ≫ i) hji) n
      ((Modules.AbelianSheafComparison.HAddEquiv X (kernelModule (j ≫ i)) n).symm
        ((Modules.DerivedSections.cohomology X n).map (kernelModuleMap i j) a)) =
    Sheaf.H.map (schemeOneAdd i hi) n
      ((Modules.AbelianSheafComparison.HAddEquiv X (kernelModule i) n).symm a)
  rw [Modules.AbelianSheafComparison.HAddEquiv_symm_naturality]
  erw [← Sheaf.H.map_comp_apply, kernelModuleMap_oneAdd i j hi hji]
  rfl

end Langlands.AlgebraicGeometry.Picard.SquareZeroUnitNaturality
