import Langlands.ClassFieldTheory.Local.UnramifiedH2Statement
import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.ClassFieldTheory.Local.AbsoluteH2InflationProof
import Langlands.ClassFieldTheory.Local.InertiaH2Proof
import Langlands.Cohomology.Continuous.ClosedSubgroupDescentProof
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.Galois.Local.AbsoluteProof
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-! # Exhaustion of actual absolute H2 by finite unramified extensions -/

noncomputable section

open Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

/-- A class restricts to zero on an open normal subgroup containing actual inertia. -/
private theorem exists_inertia_splitting_neighborhood
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (x : absoluteCohomology F.Carrier 2) :
    ∃ N : OpenNormalSubgroup (Field.absoluteGaloisGroup F.Carrier),
      F.absoluteInertia F.canonicalTopologicalData ≤ N.toSubgroup ∧
        (continuousRestriction (absoluteUnitDiscreteModule F.Carrier) N.toSubgroup 2).hom x = 0 := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let : TotallyDisconnectedSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let H : ClosedSubgroup (Field.absoluteGaloisGroup F.Carrier) :=
    ⟨F.absoluteInertia F.canonicalTopologicalData,
      F.absoluteInertia_isClosed F.canonicalTopologicalData⟩
  let : H.toSubgroup.Normal := F.absoluteInertia_normal F.canonicalTopologicalData
  have hzero : continuousRestriction (absoluteUnitDiscreteModule F.Carrier)
      H.toSubgroup 2 x = 0 := by
    let : Subsingleton (continuousCohomology 2
        ((absoluteUnitDiscreteModule F.Carrier).restrict H.toSubgroup).toTopRep) :=
      inertiaH2Vanishing p F
    exact Subsingleton.elim _ _
  exact closedNormalRestrictionZeroDetection IntegerScalars (Field.absoluteGaloisGroup F.Carrier)
    (absoluteUnitDiscreteModule F.Carrier) H 2 x hzero

/-- Every actual absolute H2 class is inflated from a finite unramified Galois
intermediate field, with the canonical ramification indices and existing map. -/
theorem unramifiedH2Exhaustion : UnramifiedH2Exhaustion.{u} := by
  intro p hp F x
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  obtain ⟨N, hIN, hNx⟩ := exists_inertia_splitting_neighborhood p F x
  let M := finiteStageFixedField F.Carrier N
  have hfix : M.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField (finiteStageClosedSubgroup F.Carrier N)
  let E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier :=
    ⟨M, inferInstance⟩
  let : IsGalois F.Carrier E.field := finiteStageFixedField_isGalois F.Carrier N
  refine ⟨E, inferInstance,
    (Langlands.PadicField.canonicalUnramifiedCriterion p F E).mpr ?_,
    ?_⟩
  · change F.absoluteInertia F.canonicalTopologicalData ≤ M.fixingSubgroup
    rw [hfix]
    exact hIN
  · rw [(AbsoluteH2Assembly.closureInflationExactness F.Carrier E.field).2]
    change (continuousRestriction (absoluteUnitDiscreteModule F.Carrier) M.fixingSubgroup 2).hom x = 0
    have zero_of_eq (S : Subgroup (Field.absoluteGaloisGroup F.Carrier))
        (hS : S = N.toSubgroup) :
        (continuousRestriction (absoluteUnitDiscreteModule F.Carrier) S 2).hom x = 0 := by
      subst S
      exact hNx
    exact zero_of_eq M.fixingSubgroup hfix

end Langlands.ClassFieldTheory.Local
