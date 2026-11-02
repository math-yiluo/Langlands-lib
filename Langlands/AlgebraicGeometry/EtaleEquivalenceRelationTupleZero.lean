import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossQuotient

/-! # One-entry symmetric tuples recover the original relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

@[simp]
theorem tupleDistinctOpen_zero : E.tupleDistinctOpen 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [E.mem_tupleDistinctOpen]
  intro i j hij
  exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim

/-- An ordered distinct tuple with one entry is just an object. -/
def tupleDistinctZeroIso : E.tupleDistinctScheme 0 ≅ E.U :=
  (E.tupleScheme 0).isoOfEq (E.tupleDistinctOpen_zero) ≪≫ (E.tupleScheme 0).topIso

@[simp]
theorem tupleDistinctZeroIso_hom :
    E.tupleDistinctZeroIso.hom = E.tupleDistinctProjection 0 0 := by
  exact (Scheme.isoOfEq_hom_ι (E.tupleScheme 0) E.tupleDistinctOpen_zero).trans
    (Category.comp_id _).symm

@[reassoc (attr := simp)]
theorem tupleDistinctZeroIso_inv_projection :
    E.tupleDistinctZeroIso.inv ≫ E.tupleDistinctProjection 0 0 = 𝟙 E.U := by
  rw [← E.tupleDistinctZeroIso_hom]
  exact E.tupleDistinctZeroIso.inv_hom_id

@[reassoc (attr := simp)]
theorem tupleDistinctZeroIso_projection_inv :
    E.tupleDistinctProjection 0 0 ≫ E.tupleDistinctZeroIso.inv =
      𝟙 (E.tupleDistinctScheme 0) :=
  (congrArg (· ≫ E.tupleDistinctZeroIso.inv) E.tupleDistinctZeroIso_hom.symm).trans
    E.tupleDistinctZeroIso.hom_inv_id

section Affine

variable [IsAffine E.U] [IsAffine E.R]

/-- The unique coordinate of an unordered one-entry tuple. -/
def tupleSymmetricZeroProjection : E.tupleSymmetricScheme 0 ⟶ E.U :=
  E.tupleSymmetricDesc 0 (E.tupleDistinctProjection 0 0) (by
    intro g
    rw [E.tupleDistinctReindexIso_hom_projection, Fin.eq_zero (g 0)])

@[reassoc (attr := simp)]
theorem tupleSymmetricMap_zeroProjection :
    E.tupleSymmetricMap 0 ≫ E.tupleSymmetricZeroProjection =
      E.tupleDistinctProjection 0 0 :=
  E.tupleSymmetricMap_desc 0 _ _

/-- An unordered distinct tuple with one entry is just an object. -/
def tupleSymmetricZeroIso : E.tupleSymmetricScheme 0 ≅ E.U where
  hom := E.tupleSymmetricZeroProjection
  inv := E.tupleDistinctZeroIso.inv ≫ E.tupleSymmetricMap 0
  hom_inv_id := by
    apply E.tupleSymmetric_hom_ext 0
    rw [E.tupleSymmetricMap_zeroProjection_assoc, Category.comp_id]
    simpa only [tupleDistinctProjection, Category.assoc] using
      E.tupleDistinctZeroIso_projection_inv_assoc (E.tupleSymmetricMap 0)
  inv_hom_id := by simp

@[reassoc (attr := simp)]
theorem tupleSymmetricMap_zeroIso_hom :
    E.tupleSymmetricMap 0 ≫ E.tupleSymmetricZeroIso.hom =
      E.tupleDistinctProjection 0 0 :=
  E.tupleSymmetricMap_zeroProjection

/-- Recover the relation arrow from two unordered one-entry tuples. -/
def tupleSymmetricCrossZeroProjection : E.tupleSymmetricCrossScheme 0 0 ⟶ E.R :=
  (E.tupleCrossQuotient 0 0).desc (E.tupleCrossMap 0 0) (by
    intro g
    have : Subsingleton (Fin (0 + 1)) :=
      ⟨fun i j => (Fin.eq_zero i).trans (Fin.eq_zero j).symm⟩
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg, (E.tupleCrossPermutationAction 0 0).one]
    simp)

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossMap_zeroProjection :
    E.tupleSymmetricCrossMap 0 0 ≫ E.tupleSymmetricCrossZeroProjection =
      E.tupleCrossMap 0 0 :=
  (E.tupleCrossQuotient 0 0).map_desc _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossZeroProjection_t :
    E.tupleSymmetricCrossZeroProjection ≫ E.t =
      E.tupleSymmetricCrossLeft 0 0 ≫ E.tupleSymmetricZeroIso.hom := by
  apply (E.tupleCrossQuotient 0 0).hom_ext
  simp only [E.tupleSymmetricCrossMap_zeroProjection_assoc,
    E.tupleSymmetricCrossMap_left_assoc,
    E.tupleSymmetricMap_zeroIso_hom]
  exact E.tupleCrossMap_t 0 0

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossZeroProjection_s :
    E.tupleSymmetricCrossZeroProjection ≫ E.s =
      E.tupleSymmetricCrossRight 0 0 ≫ E.tupleSymmetricZeroIso.hom := by
  apply (E.tupleCrossQuotient 0 0).hom_ext
  simp only [E.tupleSymmetricCrossMap_zeroProjection_assoc,
    E.tupleSymmetricCrossMap_right_assoc,
    E.tupleSymmetricMap_zeroIso_hom]
  exact E.tupleCrossMap_s 0 0

/-- Every original arrow gives a symmetric correspondence of one-entry tuples. -/
def tupleSymmetricCrossZeroSection : E.R ⟶ E.tupleSymmetricCrossScheme 0 0 :=
  E.tupleCrossLift 0 0 (E.t ≫ E.tupleDistinctZeroIso.inv)
    (E.s ≫ E.tupleDistinctZeroIso.inv) (𝟙 E.R) (by simp) (by simp) ≫
      E.tupleSymmetricCrossMap 0 0

@[reassoc (attr := simp)]
theorem tupleSymmetricCrossZeroSection_projection :
    E.tupleSymmetricCrossZeroSection ≫ E.tupleSymmetricCrossZeroProjection = 𝟙 E.R := by
  simp [tupleSymmetricCrossZeroSection]

/-- The original relation is recovered by the one-entry symmetric cross scheme. -/
def tupleSymmetricCrossZeroIso : E.tupleSymmetricCrossScheme 0 0 ≅ E.R where
  hom := E.tupleSymmetricCrossZeroProjection
  inv := E.tupleSymmetricCrossZeroSection
  hom_inv_id := by
    apply (E.tupleCrossQuotient 0 0).hom_ext
    have h : E.tupleCrossMap 0 0 ≫
        E.tupleCrossLift 0 0 (E.t ≫ E.tupleDistinctZeroIso.inv)
          (E.s ≫ E.tupleDistinctZeroIso.inv) (𝟙 E.R) (by simp) (by simp) =
        𝟙 (E.tupleCrossScheme 0 0) := by
      apply E.tupleCross_hom_ext 0 0
      · simp only [Category.assoc, E.tupleCrossLift_left, Category.id_comp,
          E.tupleCrossMap_t_assoc]
        simpa only [tupleDistinctProjection, Category.assoc, Category.comp_id] using
          congrArg (E.tupleCrossLeft 0 0 ≫ ·) E.tupleDistinctZeroIso_projection_inv
      · simp only [Category.assoc, E.tupleCrossLift_right, Category.id_comp,
          E.tupleCrossMap_s_assoc]
        simpa only [tupleDistinctProjection, Category.assoc, Category.comp_id] using
          congrArg (E.tupleCrossRight 0 0 ≫ ·) E.tupleDistinctZeroIso_projection_inv
    simpa only [tupleSymmetricCrossZeroSection, Category.assoc,
      E.tupleSymmetricCrossMap_zeroProjection_assoc, Category.comp_id,
      Category.id_comp] using
      congrArg (· ≫ E.tupleSymmetricCrossMap 0 0) h
  inv_hom_id := E.tupleSymmetricCrossZeroSection_projection

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
