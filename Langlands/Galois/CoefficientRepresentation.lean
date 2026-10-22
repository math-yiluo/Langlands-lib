import Langlands.Global.Adelic
import Langlands.Weil.Representation.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Continuous Galois representations over actual coefficient fields

The coefficient topology is retained. In particular, a lambda-adic representation
is not given the complex topology or an open-kernel condition. Compatibility
between different coefficient places is a separate proposition.
-/

noncomputable section

universe uK uL uV uW uE

namespace Langlands.GaloisRepresentation

open Polynomial

variable {K : Type uK} [Field K]
variable {L : Type uL} [Field L] [TopologicalSpace L]

/-- Continuity in the group variable, for the canonical module topology on
the endomorphisms over the given topological coefficient field. -/
def IsContinuous
    (A : FiniteRepresentation.{uL, uK, uV} L (Field.absoluteGaloisGroup K)) : Prop :=
  letI : TopologicalSpace (Module.End L A) := moduleTopology L (Module.End L A)
  Continuous A.representation

/-- Genuine finite-dimensional continuous representations of the actual
absolute Galois group; no semisimplicity or geometric-origin condition is imposed. -/
def Objects (K : Type uK) [Field K] (L : Type uL) [Field L] [TopologicalSpace L] :=
  {A : FiniteRepresentation.{uL, uK, uV} L (Field.absoluteGaloisGroup K) //
    IsContinuous A}

/-- Genuine linear-intertwining isomorphism classes, using the published quotient. -/
abbrev Classes (K : Type uK) [Field K] (L : Type uL) [Field L] [TopologicalSpace L] :=
  FiniteRepresentation.IsomorphismClassesWith
    (fun A : FiniteRepresentation.{uL, uK, uV} L (Field.absoluteGaloisGroup K) =>
      IsContinuous A)

/-- The coefficient completion carries its actual lambda-adic topology. -/
abbrev LambdaAdic (K : Type uK) [Field K] (L : Type uL) [Field L] [NumberField L]
    (lam : Global.FinitePlace L) :=
  Objects.{uK, uL, uV} K (Global.FiniteCompletion L lam)

variable (A : Objects.{uK, uL, uV} K L)

/-- The monic characteristic polynomial, with eigenvalues as roots. -/
def characteristicPolynomial (g : Field.absoluteGaloisGroup K) : L[X] :=
  (A.val.representation g).charpoly

/-- The reciprocal characteristic polynomial used in Harris 1998:
`det(1 - rho(g) T)`. The matrix formula below proves this normalization. -/
def eulerPolynomial (g : Field.absoluteGaloisGroup K) : L[X] :=
  (characteristicPolynomial A g).reverse

theorem characteristicPolynomial_monic (g : Field.absoluteGaloisGroup K) :
    (characteristicPolynomial A g).Monic :=
  LinearMap.charpoly_monic _

theorem characteristicPolynomial_natDegree (g : Field.absoluteGaloisGroup K) :
    (characteristicPolynomial A g).natDegree = A.val.rank :=
  LinearMap.charpoly_natDegree _

theorem characteristicPolynomial_coeff_zero_ne (g : Field.absoluteGaloisGroup K) :
    (characteristicPolynomial A g).coeff 0 ≠ 0 := by
  have hu : IsUnit (A.val.representation g) := by
    refine ⟨⟨A.val.representation g, A.val.representation (g⁻¹), ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
  have hv : (A.val.representation g).charpoly.eval 0 ≠ 0 := by
    rw [LinearMap.eval_charpoly]
    simpa only [map_zero, zero_sub] using (LinearMap.isUnit_det _ hu.neg).ne_zero
  simpa only [characteristicPolynomial, Polynomial.coeff_zero_eq_eval_zero] using hv

theorem eulerPolynomial_coeff_zero (g : Field.absoluteGaloisGroup K) :
    (eulerPolynomial A g).coeff 0 = 1 := by
  rw [eulerPolynomial, Polynomial.coeff_zero_reverse,
    (characteristicPolynomial_monic A g).leadingCoeff]

theorem eulerPolynomial_natDegree (g : Field.absoluteGaloisGroup K) :
    (eulerPolynomial A g).natDegree = A.val.rank := by
  rw [eulerPolynomial, Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr
      (Or.inr (characteristicPolynomial_coeff_zero_ne A g)),
    Nat.sub_zero, characteristicPolynomial_natDegree]

/-- Reversing the Euler polynomial recovers the eigenvalue polynomial exactly;
the action is invertible, so reversal loses no degree. -/
theorem reverse_eulerPolynomial (g : Field.absoluteGaloisGroup K) :
    (eulerPolynomial A g).reverse = characteristicPolynomial A g := by
  change Polynomial.reflect (eulerPolynomial A g).natDegree
    (Polynomial.reflect (characteristicPolynomial A g).natDegree
      (characteristicPolynomial A g)) = characteristicPolynomial A g
  rw [eulerPolynomial_natDegree, characteristicPolynomial_natDegree,
    Polynomial.reflect_reflect]

/-- This equality is valid for every finite basis, not just a selected matrix model. -/
theorem eulerPolynomial_eq_det {i : Type uW} [Fintype i] [DecidableEq i]
    (b : Module.Basis i L A.val) (g : Field.absoluteGaloisGroup K) :
    eulerPolynomial A g =
      Matrix.det (1 - (X : L[X]) •
        (LinearMap.toMatrix b b (A.val.representation g)).map C) := by
  rw [eulerPolynomial, characteristicPolynomial,
    ← LinearMap.charpoly_toMatrix _ b, Matrix.reverse_charpoly, Matrix.charpolyRev]

variable {A}

theorem characteristicPolynomial_eq_of_equiv
    {B : Objects.{uK, uL, uW} K L} (e : FiniteRepresentation.Equiv A.val B.val)
    (g : Field.absoluteGaloisGroup K) :
    characteristicPolynomial A g = characteristicPolynomial B g := by
  unfold characteristicPolynomial
  rw [← Representation.Equiv.conj_apply_self g e, LinearEquiv.charpoly_conj]

theorem eulerPolynomial_eq_of_equiv
    {B : Objects.{uK, uL, uW} K L} (e : FiniteRepresentation.Equiv A.val B.val)
    (g : Field.absoluteGaloisGroup K) :
    eulerPolynomial A g = eulerPolynomial B g := by
  rw [eulerPolynomial, eulerPolynomial, characteristicPolynomial_eq_of_equiv e g]

/-- Descend the Euler polynomial through genuine representation isomorphism. -/
def classEulerPolynomial (g : Field.absoluteGaloisGroup K) :
    Classes.{uK, uL, uV} K L → L[X] :=
  Quotient.lift (fun A => eulerPolynomial A g) fun _ _ ⟨e⟩ =>
    eulerPolynomial_eq_of_equiv e g

variable {E : Type uE} [Field E]

/-- Pull back along Mathlib's continuous map of actual absolute Galois groups.
Its chosen algebraic-closure embedding is not asserted canonical. -/
def pullback (f : K →+* E) (A : Objects.{uK, uL, uV} K L) :
    Objects.{uE, uL, uV} E L := by
  refine ⟨FiniteRepresentation.of
    (A.val.representation.comp (Field.absoluteGaloisGroup.map f).toMonoidHom), ?_⟩
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L (Module.End L A.val)
  exact A.property.comp (Field.absoluteGaloisGroup.map f).continuous

@[simp]
theorem characteristicPolynomial_pullback (f : K →+* E)
    (A : Objects.{uK, uL, uV} K L) (g : Field.absoluteGaloisGroup E) :
    characteristicPolynomial (pullback f A) g =
      characteristicPolynomial A (Field.absoluteGaloisGroup.map f g) := rfl

@[simp]
theorem eulerPolynomial_pullback (f : K →+* E)
    (A : Objects.{uK, uL, uV} K L) (g : Field.absoluteGaloisGroup E) :
    eulerPolynomial (pullback f A) g =
      eulerPolynomial A (Field.absoluteGaloisGroup.map f g) := rfl

/-- Restriction to an actual completion, using the actual completion embedding
and Mathlib's choice of compatible algebraic closures. -/
def atFinitePlace [NumberField K] (v : Global.FinitePlace K)
    (A : Objects.{uK, uL, uV} K L) :
    Objects.{uK, uL, uV} (Global.FiniteCompletion K v) L :=
  pullback (NumberField.FinitePlace.embedding v) A

end Langlands.GaloisRepresentation
