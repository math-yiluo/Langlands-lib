import Langlands.Representation.FiniteGeneralLinear.CuspidalClassCountBoundStatement
import Langlands.Representation.Category.FiniteIndexRestriction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.Unique

/-! Character orthogonality for cuspidal representations on arbitrary carrier universes. -/

noncomputable section

namespace Langlands.FiniteGeneralLinear

universe u w

/-- The orbit of one nonzero vector gives a finite spanning set. -/
theorem finiteDimensional_of_isIrreducible {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) : FiniteDimensional ℂ V := by
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero ρ hρ
  apply Module.Finite.of_fg_top
  rw [← FiniteIndexRestriction.span_orbit_eq_top ρ hρ hv]
  exact Submodule.fg_span (Set.finite_range _)

variable {k : Type u} [Field k] {n : ℕ}

private def representative (c : CuspidalClass.{u,w} n k) : CuspidalRep.{u,w} n k :=
  (CuspidalRep.isoClass_surjective c).choose

private theorem class_representative (c : CuspidalClass.{u,w} n k) :
    (representative c).isoClass = c :=
  (CuspidalRep.isoClass_surjective c).choose_spec

/-- The trace character of a cuspidal class, computed on a representative of that class. -/
def cuspidalCharacter (c : CuspidalClass.{u,w} n k) : GeneralLinear n k → ℂ :=
  (representative c).obj.ρ.character

variable [Finite k]

/-- Character orthogonality gives a linearly independent family indexed by the original
classes, in any carrier universe. -/
theorem cuspidalCharacter_linearIndependent :
    LinearIndependent ℂ (cuspidalCharacter (n := n) (k := k) :
      CuspidalClass.{u,w} n k → GeneralLinear n k → ℂ) := by
  classical
  let G := GeneralLinear n k
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  let pairing (d : CuspidalClass.{u,w} n k) : (G → ℂ) →ₗ[ℂ] ℂ :=
    (Nat.card G : ℂ)⁻¹ • ∑ g : G,
      cuspidalCharacter d g⁻¹ • LinearMap.proj g
  have hpair (c d : CuspidalClass.{u,w} n k) :
      pairing d (cuspidalCharacter c) = if c = d then (1 : ℂ) else 0 := by
    let A := representative c
    let B := representative d
    let : A.obj.ρ.IsIrreducible := A.isIrreducible
    let : B.obj.ρ.IsIrreducible := B.isIrreducible
    let : FiniteDimensional ℂ A.obj := finiteDimensional_of_isIrreducible _ A.isIrreducible
    let : FiniteDimensional ℂ B.obj := finiteDimensional_of_isIrreducible _ B.isIrreducible
    have hcd : Nonempty (B.obj.ρ.Equiv A.obj.ρ) ↔ c = d := by
      rw [← CuspidalRep.isoClass_eq_iff B A, class_representative, class_representative, eq_comm]
    simpa [pairing, cuspidalCharacter, A, B, hcd, mul_comm] using
      Representation.char_orthonormal A.obj.ρ B.obj.ρ
  rw [linearIndependent_iff']
  intro s a hsum d hd
  have h := congrArg (pairing d) hsum
  simpa [map_sum, hpair, hd] using h

/-- In particular the classes constitute a finite type in every carrier universe. -/
theorem cuspidalClass_finite : Finite (CuspidalClass.{u,w} n k) := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  have h := (cuspidalCharacter_linearIndependent (n := n) (k := k)).cardinalMk_le_finrank
  exact Cardinal.lt_aleph0_iff_finite.mp (h.trans_lt Cardinal.natCast_lt_aleph0)

/-- The elementary bound by the group order. -/
theorem cuspidalClass_card_le_group : ENat.card (CuspidalClass.{u,w} n k) ≤
    ENat.card (GeneralLinear n k) := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let := cuspidalClass_finite (n := n) (k := k)
  let := Fintype.ofFinite (CuspidalClass.{u,w} n k)
  simpa [Module.finrank_fintype_fun_eq_card] using
    (cuspidalCharacter_linearIndependent (n := n) (k := k)).fintype_card_le_finrank

open Polynomial FieldTheory in
/-- The rank-one case of the polynomial label bound. -/
theorem cuspidalClass_card_le_labels_one : ENat.card (CuspidalClass.{u,w} 1 k) ≤
    (irreduciblePolynomialLabels 1 k).encard := by
  refine cuspidalClass_card_le_group.trans ?_
  let e : GeneralLinear 1 k ≃* kˣ :=
    Units.mapEquiv (Matrix.uniqueRingEquiv (m := Fin 1) (A := k)).toMulEquiv
  let f (a : kˣ) : irreduciblePolynomialLabels 1 k :=
    ⟨X + C (a : k), mem_irreduciblePolynomialLabels_iff.mpr
      ⟨monic_X_add_C _, irreducible_of_degree_eq_one (degree_X_add_C _),
        natDegree_X_add_C _, fun h => by
          simpa using a.ne_zero (by simpa using congrArg (fun P : k[X] => P.coeff 0) h)⟩⟩
  rw [ENat.card_congr e.toEquiv]
  change ENat.card kˣ ≤ ENat.card (irreduciblePolynomialLabels 1 k)
  refine ENat.card_le_card_of_injective (f := f) ?_
  intro a b h
  apply Units.ext
  simpa [f] using congrArg (fun P : irreduciblePolynomialLabels 1 k => P.1.coeff 0) h

end Langlands.FiniteGeneralLinear
