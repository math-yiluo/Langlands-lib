import Langlands.LocalField.Definitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Auxiliary local characters with an exact unit-norm stabilizer

Actual local-field norm and Galois-action statements underlying Henniart
2000, Section 3.4, condition 3, and Harris 1998, Lemma 4.7 and (4.12)--(4.13).
The unproved existence assertion remains a proposition definition.
-/

noncomputable section

universe u v

namespace Langlands.Global

/-- The stabilizer of the norm pullback on valuation units is exactly the
subgroup fixing the intermediate field. The norm is Mathlib's determinant
norm, and automorphisms act on actual units through `Units.map`. -/
def HasExactUnitNormStabilizer
    {F : Type u} {M : Type v} [Field F] [NormedField M]
    [Algebra F M] [FiniteDimensional F M]
    (L : IntermediateField F M) (χ : Lˣ →* ℂˣ) : Prop :=
  ∀ σ : M ≃ₐ[F] M,
    (∀ z : Mˣ, ‖(z : M)‖ = 1 →
      χ (Units.map (Algebra.norm L)
        (Units.map σ.toRingEquiv.toMonoidHom z)) =
      χ (Units.map (Algebra.norm L) z)) ↔
    σ ∈ L.fixingSubgroup

/-- Finite-order auxiliary characters exist at every prescribed depth,
with exact norm-pullback stabilizer already on valuation units.

The canonical base-extending norm is installed only locally. The depth
condition means nontriviality arbitrarily close to one; it does not use a
residue-cardinality normalization or assume an external conductor function. -/
def AuxiliaryCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier]
    [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier]
    [IsGalois F.Carrier M.Carrier],
    letI := M.canonicalNormedField
    ∀ (L : IntermediateField F.Carrier M.Carrier) (r : ℕ),
      ∃ χ : Lˣ →ₜ* ℂˣ,
        (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) ∧
        (∃ x : Lˣ,
          ‖((x : L) : M.Carrier) - 1‖ < (p : ℝ) ^ (-(r : ℤ)) ∧ χ x ≠ 1) ∧
        HasExactUnitNormStabilizer L χ.toMonoidHom

end Langlands.Global
