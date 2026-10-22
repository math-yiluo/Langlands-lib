import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.FieldTheory.Galois.Basic

/-!
# Arithmetic propositions for the constructed Herbrand functions

These are proposition definitions, not proofs or assumptions used in the
construction. All maps are actual scalar restriction or normal restriction.
-/

noncomputable section

namespace Langlands.Ramification.Padic

universe uK uE uL

variable {p : ℕ} [Fact p.Prime]
  (K : PadicField.{uK} p) (L : PadicField.{uL} p)
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]

/-- The intrinsic p-adic scalar tower through the actual fixed field. -/
instance fixedFieldPadicScalarTower (H : Subgroup Gal(L.Carrier/K.Carrier)) :
    IsScalarTower (Padic p) (IntermediateField.fixedField H) L.Carrier :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual fixed intermediate field, packaged without changing its
carrier, field operations, or embeddings. -/
abbrev fixedPadicField (H : Subgroup Gal(L.Carrier/K.Carrier)) : PadicField.{uL} p := by
  letI : FiniteDimensional K.Carrier L.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier L.Carrier
  letI := FiniteDimensional.trans (Padic p) K.Carrier (IntermediateField.fixedField H)
  exact { Carrier := IntermediateField.fixedField H }

/-- Lower numbering is compatible with an actual subgroup and its fixed field.
The image is taken under the actual forgetful map on field automorphisms. -/
def LowerSubgroupCompatibility [IsGalois K.Carrier L.Carrier]
    (T : L.TopologicalData) : Prop :=
  ∀ (H : Subgroup Gal(L.Carrier/K.Carrier)) (u : ℝ), -1 ≤ u →
    (lowerRamificationGroupReal T (IntermediateField.fixedField H) u).map
        (AlgEquiv.restrictScalarsHom K.Carrier) =
      lowerRamificationGroupReal T K.Carrier u ⊓ H

/-- Herbrand's theorem in lower numbering, for a normal subgroup and its
actual fixed field. The index changes by phi for `L / fixedField H`. -/
def HerbrandNormalSubgroup [IsGalois K.Carrier L.Carrier]
    (T : L.TopologicalData) : Prop :=
  ∀ (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (fixedPadicField K L H).TopologicalData) (u : ℝ), -1 ≤ u →
    (lowerRamificationGroupReal T K.Carrier u).map
        (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier)
          (IntermediateField.fixedField H)) =
      lowerRamificationGroupReal S K.Carrier
        (herbrandPhi T (IntermediateField.fixedField H) u)

/-- Upper groups pass to the actual normal fixed-field quotient with
unchanged real index. -/
def UpperQuotientCompatibility [IsGalois K.Carrier L.Carrier]
    (T : L.TopologicalData) : Prop :=
  ∀ (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (fixedPadicField K L H).TopologicalData) (v : ℝ), -1 ≤ v →
    (upperRamificationGroup T K.Carrier v).map
        (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier)
          (IntermediateField.fixedField H)) =
      upperRamificationGroup S K.Carrier v

/-- The inverse Herbrand map takes every nonnegative integer to an integer. -/
def HerbrandPsiIntegral [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, herbrandPsi T K.Carrier n = m

/-- Hasse--Arf at the actual finite lower breaks. Commutativity is a condition
on the actual Galois group, not on a replacement quotient. -/
def HasseArfIntegrality [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) : Prop :=
  IsMulCommutative Gal(L.Carrier/K.Carrier) →
    ∀ i : ℕ, lowerRamificationGroup T K.Carrier i ≠
        lowerRamificationGroup T K.Carrier (i + 1) →
      ∃ n : ℤ, herbrandPhi T K.Carrier i = n

variable (E : PadicField.{uE} p)
  [Algebra K.Carrier E.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier]

/-- The phi tower law, with the outer map belonging to `E/K`. -/
def HerbrandPhiTower [IsScalarTower K.Carrier E.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] (T : L.TopologicalData) (S : E.TopologicalData) : Prop :=
  ∀ u : ℝ, -1 ≤ u →
    herbrandPhi T K.Carrier u =
      herbrandPhi S K.Carrier (herbrandPhi T E.Carrier u)

/-- The inverse tower law, with the outer map belonging to `L/E`. -/
def HerbrandPsiTower [IsScalarTower K.Carrier E.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
    [IsGalois E.Carrier L.Carrier] (T : L.TopologicalData) (S : E.TopologicalData) : Prop :=
  ∀ v : ℝ, -1 ≤ v →
    herbrandPsi T K.Carrier v =
      herbrandPsi T E.Carrier (herbrandPsi S K.Carrier v)

/-- The quotient formula for independently presented compatible carriers,
under the actual normal restriction homomorphism. -/
def UpperRestrictionCompatibility [IsScalarTower K.Carrier E.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier]
    [IsGalois K.Carrier E.Carrier] [IsGalois E.Carrier L.Carrier]
    (T : L.TopologicalData) (S : E.TopologicalData) : Prop :=
  ∀ v : ℝ, -1 ≤ v →
    (upperRamificationGroup T K.Carrier v).map
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier) =
        upperRamificationGroup S K.Carrier v

/-- Substantial arithmetic target family. Each clause also has its own
named proposition for later independent proof tasks. -/
def FiniteHerbrandArithmetic [IsScalarTower K.Carrier E.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier]
    [IsGalois K.Carrier E.Carrier] [IsGalois E.Carrier L.Carrier] : Prop :=
  ∀ (T : L.TopologicalData) (S : E.TopologicalData),
    LowerSubgroupCompatibility K L T ∧
    HerbrandNormalSubgroup K L T ∧
    UpperQuotientCompatibility K L T ∧
    HerbrandPsiIntegral K L T ∧
    HasseArfIntegrality K L T ∧
    HerbrandPhiTower K L E T S ∧
    HerbrandPsiTower K L E T S ∧
    UpperRestrictionCompatibility K L E T S

end Langlands.Ramification.Padic
