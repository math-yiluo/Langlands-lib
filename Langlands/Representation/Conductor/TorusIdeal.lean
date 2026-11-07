import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Invariant.Basic

/-!
# The algebraic ideal step in Jacquet's corrected essential-vector argument

The Laurent coordinate ring is the localization of a polynomial ring at the
product of its variables. Its closed points are precisely tuples of units.
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial

universe uK uA uσ

/-- A finite type algebra over an algebraically closed field has no proper ideal
whose elements have no common zero among its field-valued points. -/
theorem ideal_eq_top_of_no_common_algebra_point
    {K : Type uK} [Field K] [IsAlgClosed K]
    {A : Type uA} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (I : Ideal A)
    (h : ∀ φ : A →ₐ[K] K, ∃ f ∈ I, φ f ≠ 0) : I = ⊤ := by
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let : M.IsMaximal := hM
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite K (A ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let φ : A →ₐ[K] K :=
    (IsAlgClosed.lift : A ⧸ M →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)
  obtain ⟨f, hf, hφf⟩ := h φ
  apply hφf
  change (IsAlgClosed.lift : A ⧸ M →ₐ[K] K) (Ideal.Quotient.mk M f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hf), map_zero]

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- The coordinate ring of the split algebraic torus with coordinates indexed by
`σ`: polynomials with the product of the variables inverted. -/
abbrev TorusPolynomialAlgebra :=
  Localization.Away (∏ i : σ, (X i : MvPolynomial σ K))

/-- Evaluation of a Laurent polynomial at a tuple of nonzero field elements. -/
def torusPolynomialEvaluation (x : σ → Kˣ) : TorusPolynomialAlgebra σ K →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (∏ i : σ, (X i : MvPolynomial σ K))
    (f := aeval (fun i ↦ (x i : K))) (by
      simp only [map_prod, aeval_X]
      exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (x i).ne_zero))

@[simp] theorem torusPolynomialEvaluation_algebraMap (x : σ → Kˣ)
    (p : MvPolynomial σ K) :
    torusPolynomialEvaluation σ K x
      (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p) =
      aeval (fun i ↦ (x i : K)) p := by
  simp [torusPolynomialEvaluation, IsLocalization.Away.liftAlgHom]

/-- Every field-valued point of the Laurent coordinate ring evaluates at a tuple
of units, including when the coordinate index type is empty. -/
theorem torusPolynomialEvaluation_surjective :
    Function.Surjective (torusPolynomialEvaluation σ K) := by
  intro φ
  let v : σ → K := fun i ↦
    φ (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))
  have hprod : ∏ i : σ, v i ≠ 0 := by
    have hu := (IsLocalization.Away.algebraMap_isUnit
      (S := TorusPolynomialAlgebra σ K) (∏ i : σ, (X i : MvPolynomial σ K))).map
      φ.toMonoidHom
    simpa [v] using hu.ne_zero
  have hv (i : σ) : v i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  refine ⟨fun i ↦ Units.mk0 (v i) (hv i), ?_⟩
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : σ, (X i : MvPolynomial σ K)))
  ext i
  change torusPolynomialEvaluation σ K _
    (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)) = _
  rw [torusPolynomialEvaluation_algebraMap]
  simp only [aeval_X, Units.val_mk0]
  rfl

/-- The torus form of the weak Nullstellensatz: an ideal with no common zero on
unit tuples is the unit ideal. -/
theorem torusIdeal_eq_top_of_no_common_zero [IsAlgClosed K]
    (I : Ideal (TorusPolynomialAlgebra σ K))
    (h : ∀ x : σ → Kˣ, ∃ f ∈ I, torusPolynomialEvaluation σ K x f ≠ 0) : I = ⊤ := by
  apply ideal_eq_top_of_no_common_algebra_point (K := K) I
  intro φ
  obtain ⟨x, rfl⟩ := torusPolynomialEvaluation_surjective σ K φ
  exact h x

/-- The same criterion for an integral subalgebra of the Laurent coordinate
ring. This is the form used for symmetric Laurent polynomials in Jacquet 2012. -/
theorem torusSubalgebraIdeal_eq_top_of_no_common_zero [IsAlgClosed K]
    (S : Subalgebra K (TorusPolynomialAlgebra σ K))
    [Algebra.IsIntegral S (TorusPolynomialAlgebra σ K)] (I : Ideal S)
    (h : ∀ x : σ → Kˣ, ∃ f ∈ I, torusPolynomialEvaluation σ K x f.val ≠ 0) : I = ⊤ := by
  apply (Ideal.map_eq_top_iff S.val.toRingHom Subtype.val_injective
    (Algebra.isIntegral_def.mp inferInstance)).mp
  apply torusIdeal_eq_top_of_no_common_zero σ K
  intro x
  obtain ⟨f, hf, hxf⟩ := h x
  exact ⟨f.val, Ideal.mem_map_of_mem S.val.toRingHom hf, hxf⟩

/-- Permuting the torus coordinates extends polynomial renaming to Laurent
polynomials. -/
def torusPolynomialPermutation (e : Equiv.Perm σ) :
    TorusPolynomialAlgebra σ K →ₐ[K] TorusPolynomialAlgebra σ K :=
  IsLocalization.Away.liftAlgHom (∏ i : σ, (X i : MvPolynomial σ K))
    (f := (Algebra.algHom K (MvPolynomial σ K) (TorusPolynomialAlgebra σ K)).comp
      (rename e)) (by
      have he : rename e (∏ i : σ, (X i : MvPolynomial σ K)) =
          ∏ i : σ, (X i : MvPolynomial σ K) := by
        simp only [map_prod, rename_X, Equiv.prod_comp]
      change IsUnit (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K)
        (rename e (∏ i : σ, (X i : MvPolynomial σ K))))
      rw [he]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem torusPolynomialPermutation_algebraMap (e : Equiv.Perm σ)
    (p : MvPolynomial σ K) :
    torusPolynomialPermutation σ K e
      (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p) =
      algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (rename e p) := by
  simp [torusPolynomialPermutation, IsLocalization.Away.liftAlgHom]
  rfl

@[simp] theorem torusPolynomialPermutation_one :
    torusPolynomialPermutation σ K 1 = AlgHom.id K (TorusPolynomialAlgebra σ K) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : σ, (X i : MvPolynomial σ K)))
  ext i
  change torusPolynomialPermutation σ K 1
    (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)) = _
  rw [torusPolynomialPermutation_algebraMap, rename_X]
  rfl

@[simp] theorem torusPolynomialPermutation_mul (e f : Equiv.Perm σ) :
    torusPolynomialPermutation σ K (e * f) =
      (torusPolynomialPermutation σ K e).comp (torusPolynomialPermutation σ K f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : σ, (X i : MvPolynomial σ K)))
  ext i
  change torusPolynomialPermutation σ K (e * f)
    (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)) =
      torusPolynomialPermutation σ K e (torusPolynomialPermutation σ K f
        (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i)))
  simp only [torusPolynomialPermutation_algebraMap, rename_X]
  rfl

instance torusPolynomialPermutationAction :
    MulSemiringAction (Equiv.Perm σ) (TorusPolynomialAlgebra σ K) where
  smul e f := torusPolynomialPermutation σ K e f
  one_smul f := by
    change torusPolynomialPermutation σ K 1 f = f
    rw [torusPolynomialPermutation_one]
    rfl
  mul_smul e f p := by
    change torusPolynomialPermutation σ K (e * f) p =
      torusPolynomialPermutation σ K e (torusPolynomialPermutation σ K f p)
    rw [torusPolynomialPermutation_mul]
    rfl
  smul_zero e := map_zero _
  smul_add e := map_add _
  smul_one e := map_one _
  smul_mul e := map_mul _

/-- Symmetric Laurent polynomials, defined as the elements fixed by every
permutation of the coordinates. -/
def symmetricTorusSubalgebra : Subalgebra K (TorusPolynomialAlgebra σ K) where
  carrier := {p | ∀ e : Equiv.Perm σ, torusPolynomialPermutation σ K e p = p}
  zero_mem' e := map_zero _
  add_mem' hp hq e := by rw [map_add, hp e, hq e]
  one_mem' e := map_one _
  mul_mem' hp hq e := by rw [map_mul, hp e, hq e]
  algebraMap_mem' c e := (torusPolynomialPermutation σ K e).commutes c

instance symmetricTorus_isInvariant :
    Algebra.IsInvariant (symmetricTorusSubalgebra σ K) (TorusPolynomialAlgebra σ K)
      (Equiv.Perm σ) where
  isInvariant p hp := ⟨⟨p, hp⟩, rfl⟩

/-- The full Laurent coordinate ring is integral over the symmetric Laurent
subalgebra, by the monic orbit polynomial of the finite permutation group. -/
instance symmetricTorus_isIntegral :
    Algebra.IsIntegral (symmetricTorusSubalgebra σ K) (TorusPolynomialAlgebra σ K) :=
  Algebra.IsInvariant.isIntegral _ _ (Equiv.Perm σ)

/-- Jacquet's algebraic ideal criterion: if an ideal of symmetric Laurent
polynomials has no common zero on unit tuples, it contains every element. -/
theorem symmetricTorusIdeal_eq_top_of_no_common_zero [IsAlgClosed K]
    (I : Ideal (symmetricTorusSubalgebra σ K))
    (h : ∀ x : σ → Kˣ, ∃ f ∈ I, torusPolynomialEvaluation σ K x f.val ≠ 0) : I = ⊤ :=
  torusSubalgebraIdeal_eq_top_of_no_common_zero σ K (symmetricTorusSubalgebra σ K) I h

end Langlands.Conductor
