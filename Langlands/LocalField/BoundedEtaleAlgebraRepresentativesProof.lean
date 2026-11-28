import Langlands.LocalField.BoundedEtaleAlgebraRepresentativesStatement
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite representatives of bounded-dimensional étale algebras -/

namespace Langlands.LocalField

universe u v

theorem boundedEtaleAlgebraRepresentatives : BoundedEtaleAlgebraRepresentativesStatement.{u, v} := by
  classical
  intro F _ d hfinite
  let fields := {E : IntermediateField F (AlgebraicClosure F) |
    FiniteDimensional F E ∧ Module.finrank F E ≤ d}
  let : Finite fields := hfinite.to_subtype
  let shapes := Σ j : Fin (d + 1), Fin j.val → fields
  let : Fintype shapes := Fintype.ofFinite shapes
  let index := (Fintype.equivFin shapes).symm
  let model (t : shapes) := (j : Fin t.1.val) → (t.2 j).val
  let ring (t : shapes) : CommRing (model t) :=
    inferInstanceAs (CommRing ((j : Fin t.1.val) → (t.2 j).val))
  let alg (t : shapes) : Algebra F (model t) :=
    inferInstanceAs (Algebra F ((j : Fin t.1.val) → (t.2 j).val))
  refine ⟨_, model ∘ index, fun j => ring (index j), fun j => alg (index j), ?_⟩
  intro A _ _ hEtale hdim
  obtain ⟨I, hI, E, hField, hAlgebra, e, hE⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod F A).mp hEtale
  let : Fintype I := Fintype.ofFinite I
  let : ∀ i : I, Module.Finite F (E i) := fun i => (hE i).1
  have hsum : ∑ i, Module.finrank F (E i) ≤ d := by
    rw [← Module.finrank_pi_fintype, ← e.toLinearEquiv.finrank_eq]
    exact hdim
  have hcard : Fintype.card I ≤ d := by
    calc
      Fintype.card I = ∑ _i : I, 1 := by simp
      _ ≤ ∑ i, Module.finrank F (E i) :=
        Finset.sum_le_sum fun i _ => Module.finrank_pos
      _ ≤ d := hsum
  let n : Fin (d + 1) := ⟨Fintype.card I, Nat.lt_succ_of_le hcard⟩
  let reindex : Fin n.val ≃ I := (Fintype.equivFin I).symm
  let embedding (j : Fin n.val) : E (reindex j) →ₐ[F] AlgebraicClosure F :=
    IsAlgClosed.lift
  have hmem (j : Fin n.val) : (embedding j).fieldRange ∈ fields := by
    let rangeEquiv := (embedding j).equivFieldRange
    refine ⟨Module.Finite.of_surjective rangeEquiv.toLinearMap rangeEquiv.surjective, ?_⟩
    rw [← rangeEquiv.toLinearEquiv.finrank_eq]
    exact (Finset.single_le_sum (fun i _ => Nat.zero_le (Module.finrank F (E i)))
      (Finset.mem_univ (reindex j))).trans hsum
  let t : shapes := ⟨n, fun j => ⟨(embedding j).fieldRange, hmem j⟩⟩
  refine ⟨index.symm t, ?_⟩
  change Nonempty (A ≃ₐ[F] model (index (index.symm t)))
  rw [index.apply_symm_apply]
  exact ⟨e.trans ((AlgEquiv.piCongrLeft F E reindex).symm.trans
    (AlgEquiv.piCongrRight fun j => (embedding j).equivFieldRange))⟩

end Langlands.LocalField
