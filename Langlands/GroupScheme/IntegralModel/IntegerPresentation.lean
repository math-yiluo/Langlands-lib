import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.Iso

/-! # The given and norm-defined presentations of local-field integers -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

private def subringModel {K : Type u} [Field K] {S T : Subring K}
    [IsFractionRing S K] [IsFractionRing T K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (h : S = T)
    (M : IntegralModel S K G) : IntegralModel T K G := by
  subst T
  exact M

private theorem subringModel_smooth {K : Type u} [Field K] {S T : Subring K}
    [IsFractionRing S K] [IsFractionRing T K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (h : S = T)
    (M : IntegralModel S K G) (hM : M.IsSmooth) :
    (subringModel h M).IsSmooth := by
  subst T
  exact hM

private theorem subringModel_baseChange {K : Type u} [Field K] {S T : Subring K}
    [sFrac : IsFractionRing S K] [tFrac : IsFractionRing T K]
    {A L : Type u} [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [IsFractionRing A L] [Algebra K L]
    [aS : Algebra S A] [aT : Algebra T A] [lS : Algebra S L] [lT : Algebra T L]
    [tSA : IsScalarTower S A L] [tTA : IsScalarTower T A L]
    [tSK : IsScalarTower S K L] [tTK : IsScalarTower T K L]
    {G : GroupScheme (Spec (CommRingCat.of K))} (h : S = T)
    (ha : ∀ (x : S) (y : T), (x : K) = (y : K) → algebraMap S A x = algebraMap T A y)
    (hl : ∀ (x : S) (y : T), (x : K) = (y : K) → algebraMap S L x = algebraMap T L y)
    (M : IntegralModel S K G) :
    (subringModel h M).baseChange A L = M.baseChange A L := by
  subst T
  have ha' : aS = aT := Algebra.algebra_ext aS aT (fun x => ha x x rfl)
  subst aT
  have hl' : lS = lT := Algebra.algebra_ext lS lT (fun x => hl x x rfl)
  subst lT
  rfl

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
local instance presentationNormedField : NontriviallyNormedField F := localNormedField F
local instance presentationUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance presentationComplete : CompleteSpace F := localNormedField_complete F
variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Transport a model across the proved equality of the integer subrings. -/
def givenIntegerModel (M : IntegralModel (baseIntegers F) F G) : IntegralModel ↥𝒪[F] F G :=
  subringModel (localNormedField_integer F) M

theorem givenIntegerModel_smooth (M : IntegralModel (baseIntegers F) F G) (hM : M.IsSmooth) :
    (givenIntegerModel F M).IsSmooth :=
  subringModel_smooth (localNormedField_integer F) M hM

local instance presentationActualIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance presentationActualIntegralTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance presentationNormIntegerAlgebra : Algebra (baseIntegers F) (fixedFieldIntegers F) :=
  ((integerToFixedField F).comp (RingEquiv.subringCongr (localNormedField_integer F)).toRingHom).toAlgebra
local instance presentationNormGenericAlgebra : Algebra (baseIntegers F) (inertiaFixedField F) :=
  ((algebraMap F (inertiaFixedField F)).comp (algebraMap (baseIntegers F) F)).toAlgebra
local instance presentationNormGenericTower : IsScalarTower (baseIntegers F) F (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance presentationNormIntegralTower :
    IsScalarTower (baseIntegers F) (fixedFieldIntegers F) (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The presentation transport preserves the entire prescribed unramified
coefficient model, including its generic identification. -/
theorem givenIntegerModel_unramified_eq (M : IntegralModel (baseIntegers F) F G) :
    (givenIntegerModel F M).baseChangeUnramified =
      M.baseChange (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply subringModel_baseChange
    (sFrac := inferInstanceAs (IsFractionRing (baseIntegers F) F))
    (tFrac := inferInstanceAs (IsFractionRing ↥𝒪[F] F))
    (aS := presentationNormIntegerAlgebra F) (aT := presentationActualIntegerAlgebra F)
    (lS := presentationNormGenericAlgebra F)
    (tSA := presentationNormIntegralTower F) (tTA := presentationActualIntegralTower F)
    (tSK := presentationNormGenericTower F)
    (localNormedField_integer F) _ _ M
  · intro x y h
    apply Subtype.ext
    exact congrArg (algebraMap F (inertiaFixedField F)) h
  · intro x y h
    exact congrArg (algebraMap F (inertiaFixedField F)) h

/-- Presentation transport retains any supplied compatible upstairs model
isomorphism over its original prescribed generic map. -/
def givenIntegerModelIso (M : IntegralModel (baseIntegers F) F G)
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    {P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H}
    {f : GaloisPointComparison.baseChanged F (inertiaFixedField F) G ≅ H}
    (e : (M.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).Iso P f) :
    (givenIntegerModel F M).baseChangeUnramified.Iso P f := by
  rw [givenIntegerModel_unramified_eq]
  exact e

end Langlands.GroupScheme.IntegralModel
