import Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite
import Mathlib.FieldTheory.Galois.Basic

/-!
# Herbrand's theorem for quotients and the tower laws in any characteristic

Proposition definitions for the general finite-level lower and upper groups and
Herbrand functions of `Herbrand.GeneralFinite`. The base `K₀` carries only the
structure required by `LocalField.TopologicalData`; no characteristic hypothesis
occurs. These are statements for later proofs, not assumptions.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u₀ uK uE uL

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (L : Type uL) [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
  [Algebra K L] [IsScalarTower K₀ K L]

/-- The scalar tower `K₀ → fixedField H → L` through the actual fixed field. -/
instance fixedFieldScalarTower (H : Subgroup (L ≃ₐ[K] L)) :
    IsScalarTower K₀ (IntermediateField.fixedField H) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual fixed field of a subgroup of `Gal(L/K)` is finite over the base `K₀`,
because it is a `K₀`-subspace of the finite-dimensional `L`. -/
instance fixedField_finiteDimensional (H : Subgroup (L ≃ₐ[K] L)) :
    FiniteDimensional K₀ (IntermediateField.fixedField H) :=
  FiniteDimensional.finiteDimensional_submodule
    ((IntermediateField.fixedField H).toSubalgebra.restrictScalars K₀).toSubmodule

/-- Lower numbering is compatible with an actual subgroup and its fixed field.
The image is taken under the actual forgetful map on field automorphisms. -/
def LowerSubgroupCompatibility [IsGalois K L]
    (T : LocalField.TopologicalData K₀ L) : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[K] L)) (u : ℝ), -1 ≤ u →
    (lowerRamificationGroupReal T (IntermediateField.fixedField H) u).map
        (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroupReal T K u ⊓ H

/-- Herbrand's theorem in lower numbering, for a normal subgroup and its
actual fixed field with any local-field realization over `K₀`. The index
changes by phi for `L / fixedField H`. -/
def HerbrandNormalSubgroup [IsGalois K L]
    (T : LocalField.TopologicalData K₀ L) : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) (u : ℝ), -1 ≤ u →
    (lowerRamificationGroupReal T K u).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L)
          (IntermediateField.fixedField H)) =
      lowerRamificationGroupReal S K
        (herbrandPhi T (IntermediateField.fixedField H) u)

/-- Upper groups pass to the actual normal fixed-field quotient with
unchanged real index. -/
def UpperQuotientCompatibility [IsGalois K L]
    (T : LocalField.TopologicalData K₀ L) : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) (v : ℝ), -1 ≤ v →
    (upperRamificationGroup T K v).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L)
          (IntermediateField.fixedField H)) =
      upperRamificationGroup S K v

variable (E : Type uE) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E]
  [Algebra K E] [Algebra E L]
  [IsScalarTower K₀ K E] [IsScalarTower K₀ E L]

/-- The phi tower law at every real index, with the outer map belonging to `E/K`. -/
def HerbrandPhiTower [IsScalarTower K E L]
    [IsGalois K L] [IsGalois K E] [IsGalois E L]
    (T : LocalField.TopologicalData K₀ L) (S : LocalField.TopologicalData K₀ E) : Prop :=
  ∀ u : ℝ,
    herbrandPhi T K u = herbrandPhi S K (herbrandPhi T E u)

/-- The inverse tower law at every real index, with the outer map belonging to `L/E`. -/
def HerbrandPsiTower [IsScalarTower K E L]
    [IsGalois K L] [IsGalois K E] [IsGalois E L]
    (T : LocalField.TopologicalData K₀ L) (S : LocalField.TopologicalData K₀ E) : Prop :=
  ∀ v : ℝ,
    herbrandPsi T K v = herbrandPsi T E (herbrandPsi S K v)

/-- The quotient formula for independently presented compatible carriers,
under the actual normal restriction homomorphism. -/
def UpperRestrictionCompatibility [IsScalarTower K E L]
    [IsGalois K L] [IsGalois K E] [IsGalois E L]
    (T : LocalField.TopologicalData K₀ L) (S : LocalField.TopologicalData K₀ E) : Prop :=
  ∀ v : ℝ, -1 ≤ v →
    (upperRamificationGroup T K v).map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E) =
        upperRamificationGroup S K v

variable (K₀) in
/-- The six quotient and tower statements for every realization `T` of `L`
and `S` of `E` over the base `K₀`. -/
def FiniteHerbrandQuotientTower [IsScalarTower K E L]
    [IsGalois K L] [IsGalois K E] [IsGalois E L] : Prop :=
  ∀ (T : LocalField.TopologicalData K₀ L) (S : LocalField.TopologicalData K₀ E),
    LowerSubgroupCompatibility K L T ∧
    HerbrandNormalSubgroup K L T ∧
    UpperQuotientCompatibility K L T ∧
    HerbrandPhiTower K L E T S ∧
    HerbrandPsiTower K L E T S ∧
    UpperRestrictionCompatibility K L E T S

end Langlands.Ramification.Local
