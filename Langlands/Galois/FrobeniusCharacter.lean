import Langlands.Galois.FrobeniusDensity
import Langlands.Weil.Representation.CoefficientExtension
import Langlands.Weil.Representation.IrreducibleCharacter

/-! # Continuous characters from geometric Frobenius Euler polynomials -/

noncomputable section

universe uK uL uM uE uV uW uG

namespace Langlands.FiniteRepresentation

variable {L : Type uL} [Field L] (E : Type uE) [Field E] [Algebra L E]
  {G : Type uG} [Monoid G]

/-- The trace character of the tensor-extended action is the mapped original character. -/
theorem character_extendCoefficients (A : FiniteRepresentation.{uL, uG, uV} L G) (g : G) :
    (A.extendCoefficients E).representation.character g =
      algebraMap L E (A.representation.character g) :=
  LinearMap.trace_baseChange (A.representation g) E

end Langlands.FiniteRepresentation

namespace Langlands.GaloisRepresentation

open Polynomial

variable {K : Type uK} [Field K]
variable {L : Type uL} [Field L] [TopologicalSpace L]

/-- The trace character of a continuous action is continuous for the given coefficient topology. -/
theorem continuous_character [IsTopologicalRing L] (A : Objects.{uK, uL, uV} K L) :
    Continuous A.val.representation.character := by
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L (Module.End L A.val)
  exact (IsModuleTopology.continuous_of_linearMap (LinearMap.trace L A.val)).comp A.property

/-- The linear coefficient of the reciprocal characteristic polynomial is minus the trace. -/
theorem coeff_one_eulerPolynomial (A : Objects.{uK, uL, uV} K L)
    (g : Field.absoluteGaloisGroup K) :
    (eulerPolynomial A g).coeff 1 = -A.val.representation.character g := by
  let b := Module.finBasis L A.val
  rw [eulerPolynomial_eq_det A b, ← Matrix.charpolyRev,
    Matrix.coeff_charpolyRev_eq_neg_trace, Representation.character,
    LinearMap.trace_eq_matrix_trace L b]

variable [NumberField K]
variable {E : Type uE} [TopologicalSpace E] [T2Space E]

/-- Continuous class functions are determined by the degree-one geometric Frobenius values
outside a finite set of places. -/
theorem eq_of_continuous_of_globalGeometricFrobenius_eq
    (S : Finset (Global.FinitePlace K))
    {f g : Field.absoluteGaloisGroup K → E} (hf : Continuous f) (hg : Continuous g)
    (hfconj : ∀ t x, f (t * x * t⁻¹) = f x) (hgconj : ∀ t x, g (t * x * t⁻¹) = g x)
    (h : ∀ v : Global.FinitePlace K, v ∉ S → (residueCardinality v).Prime →
      f (globalGeometricFrobenius v) = g (globalGeometricFrobenius v)) : f = g := by
  refine hf.ext_on (dense_conjugates_globalGeometricFrobenius_degreeOne S) hg ?_
  rintro _ ⟨v, hv, hp, t, rfl⟩
  rw [hfconj, hgconj]
  exact h v hv hp

variable {M : Type uM} [Field M] [TopologicalSpace M]
variable [IsTopologicalRing L] [IsTopologicalRing M] [Field E]

/-- Equal geometric Euler polynomials in a common coefficient field give equal global
trace characters after applying the two continuous coefficient embeddings. -/
theorem character_map_eq_of_frobeniusEulerPolynomial_map_eq
    (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uM, uW} K M)
    (i : L →+* E) (j : M →+* E) (hi : Continuous i) (hj : Continuous j)
    (S : Finset (Global.FinitePlace K))
    (h : ∀ v : Global.FinitePlace K, v ∉ S → (residueCardinality v).Prime →
      (frobeniusEulerPolynomial A v).map i = (frobeniusEulerPolynomial B v).map j) :
    (fun g => i (A.val.representation.character g)) =
      (fun g => j (B.val.representation.character g)) := by
  refine eq_of_continuous_of_globalGeometricFrobenius_eq S
    (hi.comp (continuous_character A)) (hj.comp (continuous_character B))
    (fun t g => congrArg i (Representation.char_conj A.val.representation g t))
    (fun t g => congrArg j (Representation.char_conj B.val.representation g t)) ?_
  intro v hv hp
  have he : (eulerPolynomial A (globalGeometricFrobenius v)).map i =
      (eulerPolynomial B (globalGeometricFrobenius v)).map j := h v hv hp
  have hc := congrArg (fun P : E[X] => P.coeff 1) he
  simpa only [Polynomial.coeff_map, coeff_one_eulerPolynomial, map_neg, neg_inj] using hc

/-- Equal mapped Euler polynomials and one irreducible extended local restriction give
an equivalence of the two actual extended local restrictions. -/
def FrobeniusEulerPolynomialLocalComparisonStatement : Prop :=
  ∀ {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    {M : Type uM} [Field M] [TopologicalSpace M] [IsTopologicalRing M]
    {E : Type uE} [Field E] [TopologicalSpace E] [T2Space E] [IsAlgClosed E]
    (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uM, uW} K M)
    (i : L →+* E) (j : M →+* E), Continuous i → Continuous j →
    ∀ (S : Finset (Global.FinitePlace K)),
      (∀ v : Global.FinitePlace K, v ∉ S → (residueCardinality v).Prime →
        (frobeniusEulerPolynomial A v).map i = (frobeniusEulerPolynomial B v).map j) →
      ∀ (v : Global.FinitePlace K), A.val.rank = B.val.rank →
        (letI : Algebra L E := i.toAlgebra;
          Representation.IsIrreducible ((atFinitePlace v A).val.extendCoefficients E).representation) →
        letI : Algebra L E := i.toAlgebra
        letI : Algebra M E := j.toAlgebra
        Nonempty (FiniteRepresentation.Equiv ((atFinitePlace v A).val.extendCoefficients E)
          ((atFinitePlace v B).val.extendCoefficients E))

theorem localEquiv_extendCoefficients_of_frobeniusEulerPolynomial_map_eq :
    FrobeniusEulerPolynomialLocalComparisonStatement.{uK, uL, uM, uE, uV, uW} := by
  intro K _ _ L _ _ _ M _ _ _ E _ _ _ _ A B i j hi hj S h v hd hI
  let : Algebra L E := i.toAlgebra
  let : Algebra M E := j.toAlgebra
  refine FiniteRepresentation.irreducibleCharacterComparison _ _ hI ?_ ?_
  · rw [FiniteRepresentation.rank_extendCoefficients, FiniteRepresentation.rank_extendCoefficients]
    exact hd
  · funext g
    rw [FiniteRepresentation.character_extendCoefficients,
      FiniteRepresentation.character_extendCoefficients]
    exact congrFun (character_map_eq_of_frobeniusEulerPolynomial_map_eq A B i j hi hj S h)
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g)

end Langlands.GaloisRepresentation
