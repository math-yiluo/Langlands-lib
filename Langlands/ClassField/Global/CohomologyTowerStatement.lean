import Langlands.ClassField.Global.CohomologyMaps

/-! # Tower identities for actual idele-class cohomology -/

namespace Langlands.ClassField.Global

universe u

/-- Restriction through two successive base fields equals direct restriction. -/
def IdeleClassRestrictionTransitivity : Prop :=
  ∀ (F K L E : Type u) [Field F] [Field K] [Field L] [Field E]
    [NumberField F] [NumberField K] [NumberField L] [NumberField E]
    [Algebra F K] [Algebra F L] [Algebra F E]
    [Algebra K L] [Algebra K E] [Algebra L E]
    [IsScalarTower F K L] [IsScalarTower F K E]
    [IsScalarTower F L E] [IsScalarTower K L E]
    [IsGalois F E] (n : ℕ) (a : relativeIdeleClassCohomology F E n),
    relativeIdeleClassRestriction K L E n (relativeIdeleClassRestriction F K E n a) =
      relativeIdeleClassRestriction F L E n a

/-- Inflation through two successive upper fields equals direct inflation. -/
def IdeleClassInflationTransitivity : Prop :=
  ∀ (F E L M : Type u) [Field F] [Field E] [Field L] [Field M]
    [NumberField F] [NumberField E] [NumberField L] [NumberField M]
    [Algebra F E] [Algebra F L] [Algebra F M]
    [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower F E L] [IsScalarTower F E M]
    [IsScalarTower F L M] [IsScalarTower E L M]
    [IsGalois F E] [IsGalois F L] [IsGalois F M]
    (n : ℕ) (a : relativeIdeleClassCohomology F E n),
    relativeIdeleClassInflation F L M n (relativeIdeleClassInflation F E L n a) =
      relativeIdeleClassInflation F E M n a

/-- Inflation and restriction commute for a compatible four-field tower. -/
def IdeleClassInflationRestrictionCompatibility : Prop :=
  ∀ (F K E L : Type u) [Field F] [Field K] [Field E] [Field L]
    [NumberField F] [NumberField K] [NumberField E] [NumberField L]
    [Algebra F K] [Algebra F E] [Algebra F L]
    [Algebra K E] [Algebra K L] [Algebra E L]
    [IsScalarTower F K E] [IsScalarTower F K L]
    [IsScalarTower F E L] [IsScalarTower K E L]
    [IsGalois F E] [IsGalois F L],
    haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
    ∀ (n : ℕ) (a : relativeIdeleClassCohomology F E n),
      relativeIdeleClassRestriction F K L n (relativeIdeleClassInflation F E L n a) =
        relativeIdeleClassInflation K E L n (relativeIdeleClassRestriction F K E n a)

/-- The three functorial tower laws needed for the global invariant construction. -/
def IdeleClassCohomologyTowerLaws : Prop :=
  IdeleClassRestrictionTransitivity.{u} ∧ IdeleClassInflationTransitivity.{u} ∧
    IdeleClassInflationRestrictionCompatibility.{u}

end Langlands.ClassField.Global
