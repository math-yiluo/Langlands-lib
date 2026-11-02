import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossLaws
import Langlands.AlgebraicGeometry.FiniteEtaleSourceUnramified
import Langlands.AlgebraicGeometry.FiniteSchemeRelation
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Actual finite presentations by symmetric tuple charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- A finite etale surjection on the source detects etaleness of a morphism
when its composite is etale. -/
theorem etale_of_finiteEtale_surjective_comp {W X S : Scheme.{u}}
    (p : W ⟶ X) (g : X ⟶ S) [IsFinite p] [Etale p] [Surjective p]
    [Etale (p ≫ g)] : Etale g := by
  have : Smooth g := smoothEtaleSourceDescent W X S p g
    inferInstance inferInstance inferInstance
  have : FormallyUnramified g := formallyUnramified_of_finiteEtale_comp p g
  exact Etale.of_formallyUnramified_of_flat g

namespace EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R]

instance tupleSymmetricCrossLeft_etale (m n : ℕ) :
    Etale (E.tupleSymmetricCrossLeft m n) := by
  have : Etale (E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossLeft m n) := by
    rw [E.tupleSymmetricCrossMap_left]
    infer_instance
  exact etale_of_finiteEtale_surjective_comp
    (E.tupleSymmetricCrossMap m n) (E.tupleSymmetricCrossLeft m n)

instance tupleSymmetricCrossRight_etale (m n : ℕ) :
    Etale (E.tupleSymmetricCrossRight m n) := by
  have : Etale (E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossRight m n) := by
    rw [E.tupleSymmetricCrossMap_right]
    infer_instance
  exact etale_of_finiteEtale_surjective_comp
    (E.tupleSymmetricCrossMap m n) (E.tupleSymmetricCrossRight m n)

variable [IsClosedImmersion (prod.lift E.t E.s)]

/-- Chartwise relation data for any indexed family of symmetric tuple charts.
The value `length i` denotes one less than the number of tuple entries. -/
def tupleChartRelation {I : Type} (length : I → ℕ) : FiniteSchemeRelation.{u} I where
  U i := E.tupleSymmetricScheme (length i)
  R i j := E.tupleSymmetricCrossScheme (length i) (length j)
  t i j := E.tupleSymmetricCrossLeft (length i) (length j)
  s i j := E.tupleSymmetricCrossRight (length i) (length j)
  closed_lift i j := inferInstance
  etale_t i j := inferInstance
  etale_s i j := inferInstance
  refl i T a := ⟨a ≫ E.tupleSymmetricCrossUnit (length i), by simp, by simp⟩
  symm i j T r :=
    ⟨r ≫ E.tupleSymmetricCrossSwap (length i) (length j), by simp, by simp⟩
  trans i j k T r r' h :=
    E.tupleSymmetricCross_transitive (length i) (length j) (length k) r r' h

/-- The actual affine etale equivalence relation for a finite family of
symmetric tuple charts and all of their cross-correspondences. -/
def tupleChartPresentation {I : Type} [Finite I] (length : I → ℕ) :
    EtaleEquivalenceRelation.{u} :=
  (E.tupleChartRelation length).toEtaleEquivalenceRelation

instance tupleChartPresentation_object_isAffine {I : Type} [Finite I] (length : I → ℕ) :
    IsAffine (E.tupleChartPresentation length).U := by
  change IsAffine (∐ fun i => E.tupleSymmetricScheme (length i))
  infer_instance

instance tupleChartPresentation_relation_isAffine {I : Type} [Finite I] (length : I → ℕ) :
    IsAffine (E.tupleChartPresentation length).R := by
  change IsAffine (∐ fun p : I × I =>
    E.tupleSymmetricCrossScheme (length p.1) (length p.2))
  infer_instance

instance tupleChartPresentation_joint_isClosedImmersion
    {I : Type} [Finite I] (length : I → ℕ) :
    IsClosedImmersion (prod.lift (E.tupleChartPresentation length).t
      (E.tupleChartPresentation length).s) :=
  (E.tupleChartRelation length).joint_isClosedImmersion

/-- The inclusion of an object chart in the finite presentation. -/
abbrev tupleChartObjectι {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleSymmetricScheme (length i) ⟶ (E.tupleChartPresentation length).U :=
  Sigma.ι (fun i => E.tupleSymmetricScheme (length i)) i

/-- The inclusion of a cross-correspondence in the finite presentation. -/
abbrev tupleChartRelationι {I : Type} [Finite I] (length : I → ℕ) (i j : I) :
    E.tupleSymmetricCrossScheme (length i) (length j) ⟶
      (E.tupleChartPresentation length).R :=
  Sigma.ι (fun p : I × I => E.tupleSymmetricCrossScheme (length p.1) (length p.2)) (i, j)

@[reassoc (attr := simp)]
theorem tupleChartRelationι_t {I : Type} [Finite I] (length : I → ℕ) (i j : I) :
    E.tupleChartRelationι length i j ≫ (E.tupleChartPresentation length).t =
      E.tupleSymmetricCrossLeft (length i) (length j) ≫ E.tupleChartObjectι length i := by
  exact (E.tupleChartRelation length).ι_first i j

@[reassoc (attr := simp)]
theorem tupleChartRelationι_s {I : Type} [Finite I] (length : I → ℕ) (i j : I) :
    E.tupleChartRelationι length i j ≫ (E.tupleChartPresentation length).s =
      E.tupleSymmetricCrossRight (length i) (length j) ≫ E.tupleChartObjectι length j := by
  exact (E.tupleChartRelation length).ι_second i j

/-- All symmetric tuple charts with one through `N+1` entries. -/
abbrev tupleFinitePresentation (N : ℕ) : EtaleEquivalenceRelation.{u} :=
  E.tupleChartPresentation (fun i : Fin (N + 1) => i.val)

/-- The finite tail consisting of charts with at least `p+1` entries. -/
abbrev tupleTailPresentation (N p : ℕ) : EtaleEquivalenceRelation.{u} :=
  E.tupleChartPresentation (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val)

end EtaleEquivalenceRelation
end Langlands.AlgebraicGeometry
