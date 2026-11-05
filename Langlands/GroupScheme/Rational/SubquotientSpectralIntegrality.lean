import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites
import Langlands.LinearAlgebra.ValuativeSpectralIntegrality
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! # Integral characteristic polynomials of actual subquotients -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped Matrix CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands

section MatrixRoots

variable {k : Type u} [Field k]
  {m : Type v} {n : Type w} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : Matrix n n k} {B : Matrix m m k}

/-- An injective intertwiner carries each eigenvalue into the ambient action. -/
theorem isRoot_charpoly_of_injective_intertwiner (C : Matrix m n k)
    (hC : Function.Injective C.mulVecLin) (hcomm : C * A = B * C)
    {x : k} (hx : A.charpoly.IsRoot x) : B.charpoly.IsRoot x := by
  have ha : Module.End.HasEigenvalue A.mulVecLin x :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A.mulVecLin x).mpr (by simpa using hx)
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have hb : Module.End.HasEigenvalue B.mulVecLin x := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := C.mulVecLin v)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · calc
        B.mulVecLin (C.mulVecLin v) = C.mulVecLin (A.mulVecLin v) := by
          simpa only [Matrix.mulVecLin_mul, LinearMap.comp_apply] using
            congrArg (fun M => M.mulVecLin v) hcomm.symm
        _ = x • C.mulVecLin v := by rw [hv.apply_eq_smul, map_smul]
    · intro hz
      exact hv.2 (hC (hz.trans (map_zero _).symm))
  simpa using (Module.End.hasEigenvalue_iff_isRoot_charpoly B.mulVecLin x).mp hb

/-- A surjective intertwiner carries the quotient spectrum into the source spectrum. -/
theorem isRoot_charpoly_of_surjective_intertwiner (C : Matrix m n k)
    (hC : Function.Surjective C.mulVecLin) (hcomm : C * A = B * C)
    {x : k} (hx : B.charpoly.IsRoot x) : A.charpoly.IsRoot x := by
  obtain ⟨D, hD⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hC
  have hleft : D.transpose.mulVecLin ∘ₗ C.transpose.mulVecLin = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.transpose_mul, hD,
      Matrix.transpose_one, Matrix.mulVecLin_one]
  have hi : Function.Injective C.transpose.mulVecLin :=
    (show Function.LeftInverse D.transpose.mulVecLin C.transpose.mulVecLin from
      fun v => LinearMap.congr_fun hleft v).injective
  have ht : C.transpose * B.transpose = A.transpose * C.transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hcomm.symm
  simpa using isRoot_charpoly_of_injective_intertwiner C.transpose hi ht
    (by simpa using hx)

end MatrixRoots

/-- Root inclusion after an unvalued algebraic closure suffices to transfer
integrality of the coefficients of monic polynomials. -/
theorem coeff_vle_one_of_map_roots_subset
    {k : Type u} [Field k] [ValuativeRel k] {p q : Polynomial k}
    (hp : p.Monic) (hq : q.Monic) (hc : ∀ i, p.coeff i ≤ᵥ (1 : k))
    (hr : ∀ x : AlgebraicClosure k,
      (q.map (algebraMap k (AlgebraicClosure k))).IsRoot x →
      (p.map (algebraMap k (AlgebraicClosure k))).IsRoot x) :
    ∀ i, q.coeff i ≤ᵥ (1 : k) := by
  let O := (ValuativeRel.valuation k).integer
  have hl : p ∈ Polynomial.lifts (algebraMap O k) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨p.coeff i, (ValuativeRel.valuation k).vle_iff_le.mp (hc i)⟩, rfl⟩
  obtain ⟨pO, hmap, _, hpO⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  intro i
  have hi : IsIntegral O
      ((q.map (algebraMap k (AlgebraicClosure k))).coeff i) := by
    apply Polynomial.isIntegral_coeff_of_factors _
      (by simp only [Polynomial.leadingCoeff_map, hq.leadingCoeff, map_one];
          exact isIntegral_one)
      (IsAlgClosed.splits _) _ i
    intro x hx
    refine ⟨pO, hpO, ?_⟩
    have hroot : (p.map (algebraMap k (AlgebraicClosure k))).eval x = 0 := hr x hx
    rw [← hmap, Polynomial.map_map, ← IsScalarTower.algebraMap_eq O k (AlgebraicClosure k),
      Polynomial.eval_map_algebraMap] at hroot
    exact hroot
  have hi' : IsIntegral O (q.coeff i) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom O k (AlgebraicClosure k))
      (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k))).mp
      (by simpa only [Polynomial.coeff_map, IsScalarTower.coe_toAlgHom'] using hi)
  have hval := (Valuation.integer.integers (ValuativeRel.valuation k)).isIntegral_iff_v_le_one.mp hi'
  exact (ValuativeRel.valuation k).vle_iff_le.mpr (by simpa only [map_one] using hval)


section MatrixCoefficients

variable {k : Type u} [Field k] [ValuativeRel k]
  {m : Type} {n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : Matrix n n k} {B : Matrix m m k}

/-- Integral characteristic coefficients pass to an injectively intertwined matrix. -/
theorem charpoly_coeff_vle_one_of_injective_intertwiner (C : Matrix m n k)
    (hC : Function.Injective C.mulVecLin) (hcomm : C * A = B * C)
    (hB : ∀ i, B.charpoly.coeff i ≤ᵥ (1 : k)) :
    ∀ i, A.charpoly.coeff i ≤ᵥ (1 : k) := by
  apply coeff_vle_one_of_map_roots_subset B.charpoly_monic A.charpoly_monic hB
  intro x hx
  rw [← Matrix.charpoly_map] at hx ⊢
  apply isRoot_charpoly_of_injective_intertwiner
    (C.map (algebraMap k (AlgebraicClosure k)))
    (GroupScheme.Lie.mulVecLin_map_injective C hC) _ hx
  simpa only [Matrix.map_mul] using
    congrArg (fun M => M.map (algebraMap k (AlgebraicClosure k))) hcomm

/-- Integral characteristic coefficients pass to a surjectively intertwined matrix. -/
theorem charpoly_coeff_vle_one_of_surjective_intertwiner (C : Matrix m n k)
    (hC : Function.Surjective C.mulVecLin) (hcomm : C * A = B * C)
    (hA : ∀ i, A.charpoly.coeff i ≤ᵥ (1 : k)) :
    ∀ i, B.charpoly.coeff i ≤ᵥ (1 : k) := by
  apply coeff_vle_one_of_map_roots_subset A.charpoly_monic B.charpoly_monic hA
  intro x hx
  rw [← Matrix.charpoly_map] at hx ⊢
  apply isRoot_charpoly_of_surjective_intertwiner
    (C.map (algebraMap k (AlgebraicClosure k)))
    (GroupScheme.Lie.mulVecLin_map_surjective C hC) _ hx
  simpa only [Matrix.map_mul] using
    congrArg (fun M => M.map (algebraMap k (AlgebraicClosure k))) hcomm

end MatrixCoefficients

namespace GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The canonical affine algebra test associated to an actual rational point. -/
def rationalAffinePoint (g : rationalPoints G) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶ G.X :=
  (Over.homMk (𝟙 (Spec (CommRingCat.of k))) (by
    simp [algSpec_obj_hom, Algebra.algebraMap_self]
    exact Category.id_comp _) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ g

/-- The actual rational-point matrix is the affine-test matrix at the base field. -/
theorem rationalMatrix_eq_affineMatrix (ρ : MatrixRepresentation G n) (g : rationalPoints G) :
    ρ.rationalMatrix g =
      ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) k) (rationalAffinePoint g) := by
  have hpoint : ρ.pointMatrix _ (rationalAffinePoint g) = ρ.pointMatrix _ g := by
    rw [rationalAffinePoint, pointMatrix_naturality]
    rfl
  change Matrix.GeneralLinearGroup.map _ (ρ.pointMatrix _ g) = _
  rw [← hpoint, pointMatrix_eq_affineMatrix]
  apply Units.ext
  ext i j
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) k)).inv.hom
      ((ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) k) (rationalAffinePoint g) :
        Matrix n n k) i j)) = _
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv _) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id _

/-- An all-affine-test intertwiner intertwines the actual rational-point matrices. -/
theorem Intertwines.rationalMatrix {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (g : rationalPoints G) :
    C * (ρ.rationalMatrix g : Matrix n n k) =
      (σ.rationalMatrix g : Matrix m m k) * C := by
  rw [rationalMatrix_eq_affineMatrix, rationalMatrix_eq_affineMatrix]
  simpa only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using
    hC (CommAlgCat.of (CommRingCat.of k) k) (rationalAffinePoint g)

/-- Every actual subquotient inherits integral characteristic polynomials. -/
theorem IsSubquotientOf.hasIntegralCharacteristicPolynomials [ValuativeRel k] {a b : ℕ}
    {σ : MatrixRepresentation G (Fin a)} {ρ : MatrixRepresentation G (Fin b)}
    (h : IsSubquotientOf σ ρ) (hρ : ρ.HasIntegralCharacteristicPolynomials) :
    σ.HasIntegralCharacteristicPolynomials := by
  obtain ⟨r, τ, C, D, hC, hi, hD, hs⟩ := h
  intro g
  exact charpoly_coeff_vle_one_of_surjective_intertwiner D hs (hD.rationalMatrix g)
    (charpoly_coeff_vle_one_of_injective_intertwiner C hi (hC.rationalMatrix g) (hρ g))

/-- The characteristic polynomial of an actual subquotient, certified over the
valuation ring with its original matrix polynomial and dimension. -/
def integralCharpolyOfSubquotient [ValuativeRel k] {a b : ℕ}
    {σ : MatrixRepresentation G (Fin a)} {ρ : MatrixRepresentation G (Fin b)}
    (h : IsSubquotientOf σ ρ) (hρ : ρ.HasIntegralCharacteristicPolynomials)
    (g : rationalPoints G) :
    {p : Polynomial (ValuativeRel.valuation k).integer //
      p.Monic ∧
      p.map (algebraMap (ValuativeRel.valuation k).integer k) =
        (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly ∧
      p.natDegree = a} := by
  classical
  apply Classical.choice
  have hl : (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly ∈
      Polynomial.lifts (algebraMap (ValuativeRel.valuation k).integer k) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, (ValuativeRel.valuation k).vle_iff_le.mp
      (h.hasIntegralCharacteristicPolynomials hρ g i)⟩, rfl⟩
  obtain ⟨p, hmap, hdeg, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly_monic
  exact ⟨⟨p, hmonic, hmap, by simpa using hdeg⟩⟩

end GroupScheme.MatrixRepresentation

end Langlands
