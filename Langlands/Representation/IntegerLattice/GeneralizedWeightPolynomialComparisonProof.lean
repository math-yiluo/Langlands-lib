import Langlands.Representation.IntegerLattice.GeneralizedWeightPolynomialComparisonStatement
import Langlands.Representation.IntegerLattice.GeneralizedWeightProductProof
import Langlands.Representation.IntegerLattice.GeneralizedWeightGlobalBasisProof
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # The particular polynomial witnesses for the actual lattice action -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

namespace IntegerLattice.PolynomialComparison

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem eval_matrix [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c)) (x : Fin d → ℂ) :
    (MvPolynomial.eval x).mapMatrix (generalizedWeightPolynomialMatrix A c b) =
      LinearMap.toMatrixAlgEquiv b
        (List.ofFn (fun i : Fin d =>
          ∑ k ∈ Finset.range (Module.finrank ℂ V),
            Ring.choose (x i) k • normalizedGeneratorDifference A c i ^ k)).prod := by
  classical
  have hfactor (i : Fin d) :
      (MvPolynomial.eval x).mapMatrix (generalizedWeightBinomialMatrixFactor A c b i) =
        LinearMap.toMatrixAlgEquiv b
          (∑ k ∈ Finset.range (Module.finrank ℂ V),
            Ring.choose (x i) k • normalizedGeneratorDifference A c i ^ k) := by
    ext p q
    simp [eval_generalizedWeightBinomialMatrixFactor, map_sum,
      LinearMap.toMatrixAlgEquiv_apply]
  rw [generalizedWeightPolynomialMatrix, map_list_prod, map_list_prod,
    List.map_ofFn, List.map_ofFn]
  simp only [Function.comp_def, hfactor]

end IntegerLattice.PolynomialComparison

/-- The published polynomial matrix evaluates to the actual restricted action
in every supplied local basis. -/
theorem commutingTupleGeneralizedWeightPolynomialAction :
    CommutingTupleGeneralizedWeightPolynomialActionStatement.{u} := by
  intro d V _ _ _ A c b n p q
  have hp := (commutingTupleGeneralizedWeightProduct d V A c n).2.2
  have hm := congrArg (LinearMap.toMatrixAlgEquiv b) hp
  rw [map_smul, ← IntegerLattice.PolynomialComparison.eval_matrix A c b
    (fun i => (n.toAdd i : ℂ))] at hm
  simpa only [LinearMap.toMatrixAlgEquiv_apply, Matrix.smul_apply, smul_eq_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm p) q

namespace IntegerLattice.PolynomialComparison

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The exact finite nonzero-block support contains every ambient basis index;
finite-support reconstruction therefore needs no finite whole sigma type. -/
theorem sum_block_coordinates (A : CommutingInvertibleTuple d V)
    (B : Module.Basis
      (Σ c : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A c))) ℂ V)
    (s : Finset (Fin d → ℂˣ))
    (hs : ∀ c, c ∈ s ↔ generalizedWeightBlock A c ≠ ⊥) (v : V) :
    ∑ c ∈ s, ∑ q : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
      B.repr v ⟨c, q⟩ • B ⟨c, q⟩ = v := by
  classical
  let t := s.sigma (fun c => (Finset.univ :
    Finset (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))))
  have hall (c : Fin d → ℂˣ)
      (q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))) : c ∈ s := by
    apply (hs c).2
    intro hzero
    have hpos : 0 < Module.finrank ℂ (generalizedWeightBlock A c) :=
      lt_of_le_of_lt (Nat.zero_le q.val) q.isLt
    rw [hzero, finrank_bot] at hpos
    exact Nat.lt_irrefl 0 hpos
  have hsub : (B.repr v).support ⊆ t := by
    rintro ⟨c, q⟩ _
    exact Finset.mem_sigma.mpr ⟨hall c q, Finset.mem_univ q⟩
  calc
    _ = ∑ i ∈ t, B.repr v i • B i := (Finset.sum_sigma _ _ _).symm
    _ = (B.repr v).sum (fun i a => a • B i) := by
      exact (Finset.sum_subset hsub (fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_smul])).symm
    _ = v := B.linearCombination_repr v

theorem functional_block_action [FiniteDimensional ℂ V] (A : CommutingInvertibleTuple d V)
    (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c))
    (ell : V →ₗ[ℂ] ℂ) (n : Lattice d)
    (q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))) :
    ell (tupleRepresentationEquiv d V A n (b q : V)) =
      ∑ p : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
        ((coordinateCharacter c n : ℂ) *
          MvPolynomial.eval (fun i => (n.toAdd i : ℂ))
            (generalizedWeightPolynomialMatrix A c b p q)) * ell (b p : V) := by
  classical
  have h := congrArg (fun w : generalizedWeightBlock A c => ell (w : V))
    (b.sum_repr (generalizedWeightBlockRepresentation A c n (b q)))
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    smul_eq_mul, generalizedWeightBlockRepresentation_apply_coe] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  rw [commutingTupleGeneralizedWeightPolynomialAction d V A c b n p q]

end IntegerLattice.PolynomialComparison

/-- Every compatible pair of supplied local and ambient bases contracts the
particular block polynomial matrices to the actual matrix coefficient. -/
theorem commutingTupleGeneralizedWeightPolynomialCoefficient :
    CommutingTupleGeneralizedWeightPolynomialCoefficientStatement.{u} := by
  classical
  intro d V _ _ _ A b B hB
  obtain ⟨hfinite, _, _, _⟩ := commutingTupleGeneralizedWeightDecomposition d V A
  let s := hfinite.toFinset
  have hs (c : Fin d → ℂˣ) : c ∈ s ↔ generalizedWeightBlock A c ≠ ⊥ :=
    hfinite.mem_toFinset
  refine ⟨s, hs, ?_⟩
  intro v ell n
  have hv := IntegerLattice.PolynomialComparison.sum_block_coordinates A B s hs v
  have hcoeff :
      ell (tupleRepresentationEquiv d V A n v) =
        ∑ c ∈ s, ∑ q : Fin (Module.finrank ℂ (generalizedWeightBlock A c)),
          B.repr v ⟨c, q⟩ *
            ell (tupleRepresentationEquiv d V A n (b c q : V)) := by
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, hB, smul_eq_mul]
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro c _
  simp only [IntegerLattice.PolynomialComparison.functional_block_action,
    generalizedWeightCoefficientPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Compatible actual bases and exact finite block support exist together,
before all vectors, functionals and integer lattice points. -/
theorem commutingTupleGeneralizedWeightPolynomialAssembly :
    CommutingTupleGeneralizedWeightPolynomialAssemblyStatement.{u} := by
  intro d V _ _ _ A
  obtain ⟨b, B, hB, _⟩ := commutingTupleGeneralizedWeightGlobalBasis d V A
  obtain ⟨s, hs, hcoeff⟩ :=
    commutingTupleGeneralizedWeightPolynomialCoefficient d V A b B hB
  exact ⟨b, B, s, hB, hs, hcoeff⟩

/-- Renard C.III's particular actual-block polynomials evaluate to the actual
action and assemble its actual coefficients in compatible bases. -/
theorem renardCIIIPolynomialComparison : RenardCIIIPolynomialComparisonStatement.{u} :=
  ⟨commutingTupleGeneralizedWeightPolynomialAction,
    commutingTupleGeneralizedWeightPolynomialCoefficient,
    commutingTupleGeneralizedWeightPolynomialAssembly⟩

end Langlands
