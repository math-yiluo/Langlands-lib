import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorFiniteField
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.FieldTheory.Galois.Infinite

/-! # The finite separable stabilizer field of an actual almost-simple factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom] in
/-- An almost-simple ground-field group has at least one factor after any field
extension admitting an actual product presentation. -/
theorem nonempty_index_of_almostSimple (hG : IsAlmostSimple G) : Nonempty D.Index := by
  by_contra h
  apply hG.noncommutative
  intro T x y
  apply (commute_iff_eq _ _).mpr
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k L
  let : Surjective (algebraBaseMap k L) := hs
  let : Flat (algebraBaseMap k L) := hf
  let : QuasiCompact (algebraBaseMap k L) := hq
  apply (Over.pullback (algebraBaseMap k L)).map_injective
  apply D.points_ext
  intro i
  exact (h ⟨i⟩).elim

/-- The subgroup fixing the index of one actual product factor. -/
def galoisFactorStabilizer (i : D.Index) : Subgroup (L ≃ₐ[k] L) where
  carrier := {σ | D.galoisFactorIndex σ i = i}
  one_mem' := D.galoisFactorIndex_one i
  mul_mem' := by
    intro σ τ hσ hτ
    change D.galoisFactorIndex (σ * τ) i = i
    rw [D.galoisFactorIndex_mul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    change D.galoisFactorIndex σ⁻¹ i = i
    calc
      _ = D.galoisFactorIndex σ⁻¹ (D.galoisFactorIndex σ i) := by rw [hσ]
      _ = D.galoisFactorIndex (σ⁻¹ * σ) i := (D.galoisFactorIndex_mul _ _ _).symm
      _ = i := by rw [inv_mul_cancel, D.galoisFactorIndex_one]

@[simp] theorem mem_galoisFactorStabilizer (i : D.Index) (σ : L ≃ₐ[k] L) :
    σ ∈ D.galoisFactorStabilizer i ↔ D.galoisFactorIndex σ i = i := Iff.rfl

/-- The actual intermediate field fixed by the factor stabilizer. -/
def factorStabilizerField (i : D.Index) : IntermediateField k L :=
  IntermediateField.fixedField (D.galoisFactorStabilizer i)

variable [IsGalois k L]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- The finite endomorphism-model field has a pointwise fixer contained in the
actual factor stabilizer. -/
theorem fixingSubgroup_factorFieldOfDefinition_le (i : D.Index) :
    (D.factorFieldOfDefinition i).1.fixingSubgroup ≤ D.galoisFactorStabilizer i := by
  intro σ hσ
  exact D.galoisFactorIndex_eq_of_fixes i σ
    ((mem_fixingSubgroup_iff (L ≃ₐ[k] L)).mp hσ)

/-- The stabilizer is open for the Krull topology. -/
theorem isOpen_galoisFactorStabilizer (i : D.Index) :
    IsOpen (D.galoisFactorStabilizer i : Set (L ≃ₐ[k] L)) := by
  let : FiniteDimensional k (D.factorFieldOfDefinition i).1 :=
    (D.factorFieldOfDefinition i).2
  exact Subgroup.isOpen_mono (D.fixingSubgroup_factorFieldOfDefinition_le i)
    (IntermediateField.fixingSubgroup_isOpen (D.factorFieldOfDefinition i).1)

/-- The stabilizer is closed, as every open subgroup of a topological group is. -/
theorem isClosed_galoisFactorStabilizer (i : D.Index) :
    IsClosed (D.galoisFactorStabilizer i : Set (L ≃ₐ[k] L)) :=
  (D.galoisFactorStabilizer i).isClosed_of_isOpen (D.isOpen_galoisFactorStabilizer i)

/-- Infinite Galois correspondence recovers exactly the selected-factor stabilizer. -/
theorem fixingSubgroup_factorStabilizerField (i : D.Index) :
    (D.factorStabilizerField i).fixingSubgroup = D.galoisFactorStabilizer i :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨D.galoisFactorStabilizer i, D.isClosed_galoisFactorStabilizer i⟩

/-- The stabilizer fixed field is finite over the original field. -/
instance finiteDimensional_factorStabilizerField (i : D.Index) :
    FiniteDimensional k (D.factorStabilizerField i) := by
  apply (InfiniteGalois.isOpen_iff_finite (D.factorStabilizerField i)).mp
  rw [D.fixingSubgroup_factorStabilizerField i]
  exact D.isOpen_galoisFactorStabilizer i

/-- The stabilizer fixed field is separable over the original field. -/
instance isSeparable_factorStabilizerField (i : D.Index) :
    Algebra.IsSeparable k (D.factorStabilizerField i) := inferInstance

/-- Fixing the stabilizer field pointwise is equivalent to fixing the actual
factor index. -/
theorem fixes_factorStabilizerField_iff (i : D.Index) (σ : L ≃ₐ[k] L) :
    (∀ x ∈ D.factorStabilizerField i, σ x = x) ↔ D.galoisFactorIndex σ i = i := by
  rw [← mem_galoisFactorStabilizer, ← D.fixingSubgroup_factorStabilizerField]
  exact (mem_fixingSubgroup_iff (L ≃ₐ[k] L)).symm

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
