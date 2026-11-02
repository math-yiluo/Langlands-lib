import Langlands.Global.Arithmetic.QuadraticRootSupport
import Langlands.Global.Arithmetic.SplitQuadraticPrerequisites

/-! # Compositum degrees for the auxiliary quadratic construction -/

namespace Langlands.Global

open IntermediateField

universe u

/-- The actual rational intermediate field given by a canonical field embedding. -/
@[reducible] noncomputable def rationalFieldImage (K C : Type u)
    [Field K] [CharZero K] [Field C] [CharZero C] [Algebra K C] :
    IntermediateField ℚ C :=
  (IsScalarTower.toAlgHom ℚ K C).fieldRange

lemma squareRoot_sup_finrank {C : Type u} [Field C] [CharZero C]
    (B : IntermediateField ℚ C) [FiniteDimensional ℚ B]
    {d : ℚ} {x : C} (hd : ¬ IsSquare (algebraMap ℚ B d))
    (hx : x ^ 2 = algebraMap ℚ C d) :
    Module.finrank ℚ ↥(B ⊔ rationalRootField x) = Module.finrank ℚ B * 2 := by
  have hxB : x ^ 2 = algebraMap B C (algebraMap ℚ B d) := by
    rw [← IsScalarTower.algebraMap_apply ℚ B C]
    exact hx
  have := adjoin.finiteDimensional (squareRoot_isIntegral hxB)
  have hrel := squareRoot_finrank hd hxB
  have h := Module.finrank_mul_finrank ℚ B B⟮x⟯
  rw [hrel] at h
  rw [← restrictScalars_adjoin_eq_sup ℚ B {x}]
  exact h.symm

lemma quadraticTower_linearDisjoint {C : Type u} [Field C] [CharZero C]
    (I R B : IntermediateField ℚ C)
    [FiniteDimensional ℚ I] [FiniteDimensional ℚ R] [FiniteDimensional ℚ B]
    (hI : Module.finrank ℚ I = 2) (hR : Module.finrank ℚ R = 2)
    (htower : Module.finrank ℚ ↥((B ⊔ R) ⊔ I) = Module.finrank ℚ B * 4) :
    I.LinearDisjoint R ∧ (I ⊔ R).LinearDisjoint B := by
  have hsup : (B ⊔ R) ⊔ I = (I ⊔ R) ⊔ B := by
    ac_rfl
  have hle := finrank_sup_le (I ⊔ R) B
  rw [← hsup, htower] at hle
  have hupper : Module.finrank ℚ ↥(I ⊔ R) ≤ 4 := by
    simpa [hI, hR] using finrank_sup_le I R
  have hpos : 0 < Module.finrank ℚ B := Module.finrank_pos
  have hdegree : Module.finrank ℚ ↥(I ⊔ R) = 4 := by
    nlinarith
  constructor
  · apply LinearDisjoint.of_finrank_sup
    simp [hdegree, hI, hR]
  · apply LinearDisjoint.of_finrank_sup
    rw [hdegree, ← hsup, htower, Nat.mul_comm]

/-- The signed square-class supply and the actual local comparison suffice for
the auxiliary quadratic construction in the common algebraic closure. -/
theorem splitAuxiliaryQuadratics_of_prerequisites
    (h : SplitQuadraticPrerequisitesStatement.{u}) :
    SplitAuxiliaryQuadraticsStatement.{u} := by
  intro p hp K _ _ _
  let C := AlgebraicClosure K
  let B : IntermediateField ℚ C := rationalFieldImage K C
  let e : K ≃ₐ[ℚ] B :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ K C)
  have : FiniteDimensional ℚ B := LinearEquiv.finiteDimensional e.toLinearEquiv
  let : NumberField B := NumberField.of_module_finite ℚ B
  obtain ⟨d, hd, hdp, hdB⟩ := h.1 p hp B inferInstance inferInstance true
  change 0 < d at hd
  have hdQ : ¬ IsSquare d := fun hs ↦ hdB (hs.map (algebraMap ℚ B))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ C d) zero_lt_two
  let R : IntermediateField ℚ C := rationalRootField x
  let : NumberField R := rationalRootField_numberField hx
  have hR : Module.finrank ℚ R = 2 := squareRoot_finrank hdQ hx
  have hBR : Module.finrank ℚ ↥(B ⊔ R) = Module.finrank ℚ B * 2 :=
    squareRoot_sup_finrank B hdB hx
  let M : IntermediateField ℚ C := B ⊔ R
  let : NumberField M := NumberField.of_module_finite ℚ M
  obtain ⟨a, ha, hap, haM⟩ := h.1 p hp M inferInstance inferInstance false
  change a < 0 at ha
  have haQ : ¬ IsSquare a := fun hs ↦ haM (hs.map (algebraMap ℚ M))
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ C a) zero_lt_two
  let I : IntermediateField ℚ C := rationalRootField y
  let : NumberField I := rationalRootField_numberField hy
  have hI : Module.finrank ℚ I = 2 := squareRoot_finrank haQ hy
  have hMI : Module.finrank ℚ ↥(M ⊔ I) = Module.finrank ℚ M * 2 :=
    squareRoot_sup_finrank M haM hy
  have htower : Module.finrank ℚ ↥((B ⊔ R) ⊔ I) = Module.finrank ℚ B * 4 := by
    change Module.finrank ℚ ↥(M ⊔ I) = _
    rw [hMI, hBR]
    omega
  obtain ⟨hIR, hIRB⟩ := quadraticTower_linearDisjoint I R B hI hR htower
  have hIRK : (I ⊔ R).LinearDisjoint K :=
    hIRB.algEquiv_of_isAlgebraic (I ⊔ R) K AlgEquiv.refl e.symm (.inl inferInstance)
  refine ⟨I, R, inferInstance, inferInstance, hI, hR,
    rationalRootField_totallyComplex ha hy, rationalRootField_totallyReal hd hx,
    hIR, hIRK, ?_, ?_⟩
  · exact h.2 p hp I inferInstance inferInstance hI
      (rationalRootField_two_embeddings haQ hy hap)
  · exact h.2 p hp R inferInstance inferInstance hR
      (rationalRootField_two_embeddings hdQ hx hdp)

end Langlands.Global
