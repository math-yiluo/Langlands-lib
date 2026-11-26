import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Unipotent.RationalPointsProof
import Langlands.GroupScheme.Rational.Characters
import Mathlib.LinearAlgebra.JordanChevalley

/-! # Semisimple points and commuting unipotent factors -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimplePoint

variable {k : Type u} [Field k] {G N : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational point acts semisimply in each finite-dimensional matrix representation. -/
abbrev IsSemisimple (s : rationalPoints G) : Prop :=
  ∀ n : ℕ, ∀ ρ : MatrixRepresentation G (Fin n),
    Module.End.IsSemisimple (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin n) (Fin n) k))

/-- Semisimplicity on rational points is preserved by a group homomorphism. -/
theorem map {s : rationalPoints G} (hs : IsSemisimple s) (q : G ⟶ N) :
    IsSemisimple (rationalPoints.map q s) := by
  intro n ρ
  rw [rationalPoints.map_apply, ← MatrixRepresentation.rationalMatrix_restrict ρ q s]
  exact hs n (ρ.restrict q)

/-- Conjugating a semisimple rational point preserves its semisimplicity. -/
theorem conj {s : rationalPoints G} (hs : IsSemisimple s) (g : rationalPoints G) :
    IsSemisimple (g * s * g⁻¹) := by
  intro n ρ
  let a := Matrix.GeneralLinearGroup.toLin (ρ.rationalMatrix g)
  let b := Matrix.GeneralLinearGroup.toLin (ρ.rationalMatrix s)
  let c := Matrix.GeneralLinearGroup.toLin (ρ.rationalMatrix (g * s * g⁻¹))
  have hc : c = a * b * a⁻¹ := by
    simp only [a, b, c, map_mul, map_inv]
  have hintertwines : (a.toLinearEquiv : (Fin n → k) →ₗ[k] (Fin n → k)) ∘ₗ
      (b : Module.End k (Fin n → k)) =
      (c : Module.End k (Fin n → k)) ∘ₗ a.toLinearEquiv := by
    change (a : Module.End k (Fin n → k)) * (b : Module.End k (Fin n → k)) =
      (c : Module.End k (Fin n → k)) * (a : Module.End k (Fin n → k))
    rw [← Units.val_mul, ← Units.val_mul, hc, inv_mul_cancel_right]
  exact (a.toLinearEquiv.isSemisimple_iff _ _ hintertwines).mp (hs n ρ)

private theorem matrix_eq_one_of_isSemisimple_mul [PerfectField k]
    {n : ℕ} (s v : GL (Fin n) k) (hsv : Commute s v)
    (hs : Module.End.IsSemisimple (Matrix.toLin' (s : Matrix (Fin n) (Fin n) k)))
    (hprod : Module.End.IsSemisimple
      (Matrix.toLin' ((s * v : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)))
    (hv : IsNilpotent ((v : Matrix (Fin n) (Fin n) k) - 1)) : v = 1 := by
  let a := Matrix.GeneralLinearGroup.toLin s
  let b := Matrix.GeneralLinearGroup.toLin v
  let A : Module.End k (Fin n → k) := a
  let B : Module.End k (Fin n → k) := b
  have hAB : Commute A B :=
    (hsv.map Matrix.GeneralLinearGroup.toLin).map (Units.coeHom (Module.End k (Fin n → k)))
  have hv' : IsNilpotent (B - 1) := by
    change IsNilpotent (Matrix.toLinAlgEquiv' (v : Matrix (Fin n) (Fin n) k) - 1)
    simpa only [map_sub, map_one] using hv.map
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k))
  have hsum : A * (B - 1) + A = A * B := by rw [mul_sub, mul_one, sub_add_cancel]
  have hnil : IsNilpotent (A * (B - 1)) := (hAB.sub_right (Commute.one_right A)).isNilpotent_mul_left hv'
  have hcomm : Commute (A * (B - 1)) A := Commute.mul_left rfl
    (hAB.sub_right (Commute.one_right A)).symm
  have hprod' : (A * B).IsSemisimple := by
    change Module.End.IsSemisimple (↑(a * b) : Module.End k (Fin n → k))
    rw [← map_mul]
    exact hprod
  have heq := (Module.End.isNilpotent_isSemisimple_unique hnil hs ⟨1, pow_one _⟩ hprod'
    hcomm (Commute.zero_left _) (hsum.trans (zero_add _).symm)).2
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [map_one]
  apply mul_left_cancel (a := a)
  apply Units.ext
  rw [mul_one]
  exact heq.symm

/-- If a semisimple rational point and its product with a commuting unipotent point
are semisimple, the unipotent point is the identity. -/
theorem eq_one_of_commute_of_mul [PerfectField k]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (i : N ⟶ G) (hN : IsUnipotent N) (v : rationalPoints N)
    {s : rationalPoints G} (hs : IsSemisimple s)
    (hc : Commute s (rationalPoints.map i v))
    (hprod : IsSemisimple (s * rationalPoints.map i v)) : rationalPoints.map i v = 1 := by
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  apply ρ.rationalMatrix_injective
  rw [map_one]
  apply matrix_eq_one_of_isSemisimple_mul _ _ (hc.map ρ.rationalMatrix) (hs n ρ)
  · simpa only [map_mul] using hprod n ρ
  · rw [rationalPoints.map_apply, ← MatrixRepresentation.rationalMatrix_restrict ρ i v]
    exact (perfectFieldUnipotentRationalPoints k N).1 hN (Fin n) (ρ.restrict i) v

end Langlands.GroupScheme.SemisimplePoint
