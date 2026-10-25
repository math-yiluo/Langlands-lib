import Langlands.ClassFieldTheory.Local.ResiduePolynomialUnramifiedLiftStatement
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdjoinRoot

/-! # Bounded unramified lifts of residue polynomial roots -/

noncomputable section

namespace Langlands.LocalClassField

open Polynomial PadicField.TopologicalData

universe u v

/-- Equal absolute ramification indices identify the relative residue degree
with the degree of the actual field extension. -/
theorem residueFinrank_eq_of_ramificationIndex_eq
    {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData)
    (he : S.ramificationIndex = T.ramificationIndex) :
    let := relativeResidueAlgebra T S
    Module.finrank T.ResidueField S.ResidueField = Module.finrank F.Carrier E.Carrier := by
  let := relativeResidueAlgebra T S
  let := T.finite_residueField
  let := S.finite_residueField
  have hcard : S.residueCardinality =
      T.residueCardinality ^ Module.finrank T.ResidueField S.ResidueField :=
    Module.natCard_eq_pow_finrank (K := T.ResidueField) (V := S.ResidueField)
  rw [S.residueCardinality_eq_pow, T.residueCardinality_eq_pow, ← pow_mul] at hcard
  have hf := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
  apply Nat.eq_of_mul_eq_mul_left T.residueDegree_pos
  apply Nat.eq_of_mul_eq_mul_left T.ramificationIndex_pos
  calc
    T.ramificationIndex *
        (T.residueDegree * Module.finrank T.ResidueField S.ResidueField) =
        S.ramificationIndex * S.residueDegree := by rw [he, hf]
    _ = Module.finrank (Padic p) E.Carrier := S.ramificationIndex_mul_residueDegree
    _ = Module.finrank (Padic p) F.Carrier * Module.finrank F.Carrier E.Carrier :=
      (Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier).symm
    _ = T.ramificationIndex * (T.residueDegree * Module.finrank F.Carrier E.Carrier) := by
      rw [← T.ramificationIndex_mul_residueDegree, mul_assoc]

/-- An irreducible polynomial has a root in a finite field extension of its degree,
with respect to the given algebra structure. -/
private theorem exists_root_of_finrank_eq
    {k : Type u} {l : Type v} [Field k] [Field l] [Algebra k l] [Finite l]
    (Q : Polynomial k) (hQ : Irreducible Q) (hd : Module.finrank k l = Q.natDegree) :
    ∃ z : l, (Q.map (algebraMap k l)).eval z = 0 := by
  let : Fact (Irreducible Q) := ⟨hQ⟩
  have hdim : Module.finrank k (AdjoinRoot Q) = Q.natDegree :=
    (AdjoinRoot.powerBasis hQ.ne_zero).finrank
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := k) (K := AdjoinRoot Q) (L := l) (by rw [hdim, hd])
  exact ⟨f (AdjoinRoot.root Q), by
    simpa only [Polynomial.eval_map, ← Polynomial.aeval_def] using
      AdjoinRoot.aeval_algHom_eq_zero Q f⟩

/-- Every nonconstant residue polynomial acquires a root in an unramified
Galois intermediate extension of degree bounded by its degree. -/
theorem residuePolynomialUnramifiedLift : ResiduePolynomialUnramifiedLift.{u} := by
  intro p _ F P hP
  obtain ⟨Q, hQ, hQP⟩ := WfDvdMonoid.exists_irreducible_factor
    (Polynomial.not_isUnit_of_natDegree_pos P hP) (Polynomial.ne_zero_of_natDegree_gt hP)
  obtain ⟨K', hG, he, hd⟩ :=
    Langlands.ClassFieldTheory.Local.unramifiedExtensionDegreeExistence p F
      Q.natDegree hQ.natDegree_pos
  refine ⟨K', hG, he.symm, ?_, ?_⟩
  · rw [hd]
    exact Polynomial.natDegree_le_of_dvd hQP (Polynomial.ne_zero_of_natDegree_gt hP)
  · let := (K'.asPadicField (p := p)).algebra
    let : IsScalarTower (Padic p) F.Carrier (K'.asPadicField (p := p)).Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    let T := F.canonicalTopologicalData
    let S := (K'.asPadicField (p := p)).canonicalTopologicalData
    let := relativeResidueAlgebra T S
    let := S.finite_residueField
    have hres : Module.finrank T.ResidueField S.ResidueField = Q.natDegree :=
      (residueFinrank_eq_of_ramificationIndex_eq T S he.symm).trans hd
    obtain ⟨z, hz⟩ := exists_root_of_finrank_eq Q hQ hres
    exact ⟨z, Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (Polynomial.map_dvd (relativeResidueMap T S) hQP) hz⟩

end Langlands.LocalClassField
