import Langlands.ClassFieldTheory.Local.RelativeUnitCoordinates
import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Literal norm and trace coefficients under actual unramified base change. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {K : PadicField.{v} p}
variable (T : F.TopologicalData)

/-- The residue polynomial with the specified integral norm and trace coefficients. -/
def normTraceResiduePolynomial (ell : ℕ) (a b : T.Integers) (c : T.ResidueField) :
    Polynomial T.ResidueField :=
  Polynomial.C (T.residue a) * Polynomial.X ^ ell +
    Polynomial.C (T.residue b) * Polynomial.X - Polynomial.C c

theorem normTraceResiduePolynomial_eval (ell : ℕ) (a b : T.Integers)
    (c z : T.ResidueField) :
    (T.normTraceResiduePolynomial ell a b c).eval z =
      T.residue a * z ^ ell + T.residue b * z - c := by
  simp [normTraceResiduePolynomial]

theorem normTraceResiduePolynomial_natDegree (ell : ℕ) (hell : 1 < ell)
    (a b : T.Integers) (ha : T.residue a ≠ 0) (c : T.ResidueField) :
    (T.normTraceResiduePolynomial ell a b c).natDegree = ell := by
  rw [normTraceResiduePolynomial, Polynomial.natDegree_sub_C]
  have hlead := Polynomial.natDegree_C_mul_X_pow ell (T.residue a) ha
  have hlow_le : (Polynomial.C (T.residue b) * Polynomial.X).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_C_mul_le
      (T.residue b) (Polynomial.X : Polynomial T.ResidueField))
  have hlow : (Polynomial.C (T.residue b) * Polynomial.X).natDegree < ell :=
    lt_of_le_of_lt hlow_le hell
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead])]
  exact hlead

@[simp] theorem normTraceResiduePolynomial_one_zero (ell : ℕ) (c : T.ResidueField) :
    T.normTraceResiduePolynomial ell 1 0 c = Polynomial.X ^ ell - Polynomial.C c := by
  simp [normTraceResiduePolynomial]

variable [Algebra F.Carrier K.Carrier] [IsScalarTower (Padic p) F.Carrier K.Carrier]
variable (S : K.TopologicalData)

/-- This is an equality of polynomials with the actual mapped coefficients. -/
theorem normTraceResiduePolynomial_map (ell : ℕ) (a b : T.Integers)
    (c : T.ResidueField) :
    (T.normTraceResiduePolynomial ell a b c).map (relativeResidueMap T S) =
      S.normTraceResiduePolynomial ell (relativeIntegerMap T S a)
        (relativeIntegerMap T S b) (relativeResidueMap T S c) := by
  simp [normTraceResiduePolynomial]

/-- Nonzero literal residue coefficients remain nonzero under the supplied embedding. -/
theorem residue_relativeIntegerMap_ne_zero (a : T.Integers) (ha : T.residue a ≠ 0) :
    S.residue (relativeIntegerMap T S a) ≠ 0 := by
  rw [← relativeResidueMap_residue]
  exact (map_ne_zero _).mpr ha

/-- Equal positive absolute indices give equality of order for the actual field map. -/
theorem ord_relative_algebraMap_of_equal_ramificationIndex
    [FiniteDimensional F.Carrier K.Carrier]
    (he : S.ramificationIndex = T.ramificationIndex) (x : F.Carrier) :
    S.ord (algebraMap F.Carrier K.Carrier x) = T.ord x := by
  have h := Langlands.LocalClassField.ramificationIndex_mul_ord_relative_algebraMap
    F K T S x
  rw [he] at h
  exact mul_left_cancel₀ (show (T.ramificationIndex : ℤ) ≠ 0 by
    exact_mod_cast T.ramificationIndex_pos.ne') h

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

open IntermediateField PadicField.TopologicalData

universe u

/-- The same actual compositum supplies order, norm and trace transport and hence
transport of every literal integral norm and trace coefficient. -/
theorem totalUnramifiedCompositum_coefficientTransport
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field]
    (hEram : (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex)
    (hKram : (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) :
    E.field.LinearDisjoint K.field ∧
    ∃ M : FiniteIntermediateExtension F.Carrier,
      M.field = E.field ⊔ K.field ∧
      ∃ hE : E.field ≤ M.field, ∃ hK : K.field ≤ M.field,
        letI := (E.asPadicField (p := p)).algebra
        letI := (K.asPadicField (p := p)).algebra
        letI := (M.asPadicField (p := p)).algebra
        letI : Algebra E.field M.field := (inclusion hE).toAlgebra
        letI : Algebra K.field M.field := (inclusion hK).toAlgebra
        letI : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower F.Carrier K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) F.Carrier E.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) F.Carrier K.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
        letI : FiniteDimensional K.field M.field :=
          FiniteDimensional.right F.Carrier K.field M.field
        let TF := F.canonicalTopologicalData
        let TE := (E.asPadicField (p := p)).canonicalTopologicalData
        let TK := (K.asPadicField (p := p)).canonicalTopologicalData
        let TM := (M.asPadicField (p := p)).canonicalTopologicalData
        Module.finrank K.field M.field = Module.finrank F.Carrier E.field ∧
        TM.ramificationIndex = TE.ramificationIndex ∧
        IsGalois K.field M.field ∧
        Function.Bijective (relativeResidueMap TK TM) ∧
        (∀ z : E.field, TM.ord (inclusion hE z) = TE.ord z) ∧
        (∀ z : F.Carrier, TK.ord (algebraMap F.Carrier K.field z) = TF.ord z) ∧
        (∀ z : E.field, Algebra.norm K.field (inclusion hE z) =
          algebraMap F.Carrier K.field (Algebra.norm F.Carrier z)) ∧
        (∀ z : E.field, Algebra.trace K.field M.field (inclusion hE z) =
          algebraMap F.Carrier K.field (Algebra.trace F.Carrier E.field z)) ∧
        (∀ (n : ℕ) (πF : F.Carrier) (πE : E.field) (a : TF.Integers),
          (a : F.Carrier) = Algebra.norm F.Carrier πE ^ n / πF ^ n →
          (relativeIntegerMap TF TK a : K.field) =
            Algebra.norm K.field (inclusion hE πE) ^ n /
              (algebraMap F.Carrier K.field πF) ^ n) ∧
        (∀ (n m : ℕ) (πF : F.Carrier) (πE : E.field) (b : TF.Integers),
          (b : F.Carrier) = Algebra.trace F.Carrier E.field (πE ^ m) / πF ^ n →
          (relativeIntegerMap TF TK b : K.field) =
            Algebra.trace K.field M.field ((inclusion hE πE) ^ m) /
              (algebraMap F.Carrier K.field πF) ^ n) := by
  obtain ⟨hd, M, hM, hE, hK, hn, he, hg, hr, ho, hnorm⟩ :=
    totalUnramifiedCompositum p F E K hEram hKram
  let := (E.asPadicField (p := p)).algebra
  let := (K.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : Algebra E.field M.field := (inclusion hE).toAlgebra
  let : Algebra K.field M.field := (inclusion hK).toAlgebra
  let : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) F.Carrier E.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) F.Carrier K.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) K.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K.field M.field :=
    FiniteDimensional.right F.Carrier K.field M.field
  have htrace := totalUnramifiedCompositum_trace F E K M hM hE hK hd
  refine ⟨hd, M, hM, hE, hK, hn, he, hg, hr, ho, ?_, hnorm, htrace, ?_, ?_⟩
  · exact ord_relative_algebraMap_of_equal_ramificationIndex
      F.canonicalTopologicalData (K.asPadicField (p := p)).canonicalTopologicalData hKram
  · intro n πF πE a ha
    change algebraMap F.Carrier K.field (a : F.Carrier) = _
    rw [ha, map_div₀, map_pow, map_pow, hnorm]
  · intro n m πF πE b hb
    change algebraMap F.Carrier K.field (b : F.Carrier) = _
    rw [hb, map_div₀, map_pow (algebraMap F.Carrier K.field) πF n,
      ← htrace (πE ^ m), map_pow (inclusion hE) πE m]

end Langlands.LocalClassField
