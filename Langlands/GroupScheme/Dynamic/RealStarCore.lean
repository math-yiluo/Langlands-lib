import Langlands.GroupScheme.Dynamic.RealCocharacterConjugation
import Mathlib.Algebra.Polynomial.Roots

/-! # A polynomial adjoint core containing a real cocharacter -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear

section Transpose

variable {A B : Type u} [CommRing A] [CommRing B]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Transpose on matrix units, including transpose of the inverse. -/
def transposeMatrix (g : GL n A) : GL n A where
  val := g.val.transpose
  inv := (g⁻¹).val.transpose
  val_inv := by
    rw [← Matrix.transpose_mul]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul]
    simp

@[simp] theorem transposeMatrix_val (g : GL n A) :
    (transposeMatrix g).val = g.val.transpose := rfl

@[simp] theorem transposeMatrix_inv (g : GL n A) :
    transposeMatrix g⁻¹ = (transposeMatrix g)⁻¹ := by
  apply Units.ext
  rfl

@[simp] theorem transposeMatrix_map (f : A →+* B) (g : GL n A) :
    transposeMatrix (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (transposeMatrix g) := by
  apply Units.ext
  rfl

/-- Swap the row and column indices in both coordinate families. -/
def transposeCoordinate : Coordinate n → Coordinate n
  | .entry i j => .entry j i
  | .inverseEntry i j => .inverseEntry j i

theorem values_transposeMatrix (g : GL n A) :
    values (transposeMatrix g) = values g ∘ transposeCoordinate := by
  funext v
  cases v <;> rfl

end Transpose

variable {k : Type u} [Field k] [Infinite k]

/-- Vanishing at all units detects a Laurent polynomial over an infinite field. -/
theorem laurent_eq_zero_of_eval_units
    (p : LaurentPolynomial k)
    (hp : ∀ t : kˣ, LaurentPolynomial.eval₂ (RingHom.id k) t p = 0) :
    p = 0 := by
  obtain ⟨d, q, hq⟩ := LaurentPolynomial.exists_T_pow p
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.finite_singleton (0 : k)).infinite_compl.mono
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have h := congrArg
      (LaurentPolynomial.eval₂ (RingHom.id k) (Units.mk0 x hx0)) hq
    rw [LaurentPolynomial.eval₂_toLaurent, map_mul, hp, zero_mul] at h
    simpa [Polynomial.IsRoot] using h
  have h : p * LaurentPolynomial.T (d : ℤ) = 0 := by
    rw [← hq, hq0, map_zero]
  have h' := congrArg (fun z => z * LaurentPolynomial.T (-(d : ℤ))) h
  simpa only [LaurentPolynomial.mul_T_assoc, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one, zero_mul] using h'

variable {B : Type u} [RCLike B] [Algebra k B]
  {n : Type} [Fintype n] [DecidableEq n]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme n (CommRingCat.of k))

omit [Infinite k] in
/-- Evaluation of the universal cocharacter matrix recovers any extension value. -/
theorem map_weightMatrix_eval (t : Bˣ) :
    Matrix.GeneralLinearGroup.map
        (cocharacterEvalExtensionUnit t).toRingHom (weightMatrix χ) =
      cocharacterUnitsHom χ B t := by
  have ht : Units.map (cocharacterEvalExtensionUnit t).toMonoidHom
      (cocharacterLaurentUnit (CommRingCat.of k)) = t := by
    apply Units.ext
    change LaurentPolynomial.eval₂ (algebraMap k B) t (LaurentPolynomial.T 1) = _
    simp
  have h := cocharacterUnitsHom_naturality χ (cocharacterEvalExtensionUnit t)
    (cocharacterLaurentUnit (CommRingCat.of k))
  rw [ht] at h
  exact h.symm

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.Group.AlgebraicMatrixPowers

variable {S : Type u} [RCLike S] {n : Type} [Fintype n] [DecidableEq n]

/-- The largest adjoint-stable subgroup contained in a matrix subgroup. -/
def starCore (H : Subgroup (GL n S)) : Subgroup (GL n S) where
  carrier := {g | g ∈ H ∧ star g ∈ H}
  one_mem' := ⟨H.one_mem, by simp⟩
  mul_mem' {g h} hg hh :=
    ⟨H.mul_mem hg.1 hh.1, by simpa only [star_mul] using H.mul_mem hh.2 hg.2⟩
  inv_mem' {g} hg :=
    ⟨H.inv_mem hg.1, by simpa only [star_inv] using H.inv_mem hg.2⟩

theorem star_mem_starCore (H : Subgroup (GL n S)) (g : GL n S)
    (hg : g ∈ starCore H) : star g ∈ starCore H :=
  ⟨hg.2, by simpa only [star_star] using hg.1⟩

end Langlands.Group.AlgebraicMatrixPowers

namespace Langlands.GroupScheme.MatrixRepresentation

open _root_.Langlands.GroupScheme.GeneralLinear Langlands.Group.AlgebraicMatrixPowers
open Langlands.Group.RealTwoPowerUnitaryConjugation

variable {k S : Type u} [Field k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n) [IsClosedImmersion ρ.hom.hom.left]

/-- Entrywise conjugation preserves a closed representation image when it
fixes the extended defining coefficients. -/
theorem conjugateEntries_mem_affineMatrix_range
    (hcoeff : ∀ z : k, star (algebraMap k S z) = algebraMap k S z)
    {g : GL n S} (hg : g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    conjugateEntries g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range := by
  let f : S →ₐ[k] S := { starRingEnd S with commutes' := hcoeff }
  rw [ρ.mem_affineMatrix_range_iff_zeroLocus S] at hg ⊢
  exact map_mem_zeroLocus f hg

/-- On an image defined over real coefficients, adjoint membership is
equivalent to transpose membership. -/
theorem star_mem_affineMatrix_range_iff_transpose
    (hcoeff : ∀ z : k, star (algebraMap k S z) = algebraMap k S z)
    (g : GL n S) :
    star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range ↔
      transposeMatrix g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range := by
  have h₁ : conjugateEntries (star g) = transposeMatrix g := by
    apply Units.ext
    ext i j
    simp [conjugateEntries, Matrix.star_apply]
  have h₂ : conjugateEntries (transposeMatrix g) = star g := by
    apply Units.ext
    rfl
  constructor
  · intro hg
    rw [← h₁]
    exact ρ.conjugateEntries_mem_affineMatrix_range hcoeff hg
  · intro hg
    rw [← h₂]
    exact ρ.conjugateEntries_mem_affineMatrix_range hcoeff hg

/-- The adjoint core of a closed image defined over real coefficients is
cut out by its image equations and their transpose renamings. -/
theorem starCore_affineMatrix_range_isPolynomiallyDefined
    (hcoeff : ∀ z : k, star (algebraMap k S z) = algebraMap k S z) :
    IsPolynomiallyDefined (starCore (ρ.affineMatrix (CommAlgCat.of k S)).range) := by
  refine ⟨ρ.affineImageEquations S ∪
    MvPolynomial.rename transposeCoordinate '' ρ.affineImageEquations S, ?_⟩
  intro g
  change (g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range ∧
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) ↔ _
  rw [ρ.star_mem_affineMatrix_range_iff_transpose hcoeff,
    ρ.mem_affineMatrix_range_iff_equations S,
    ρ.mem_affineMatrix_range_iff_equations S]
  constructor
  · intro hg p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact hg.1 p hp
    · rw [MvPolynomial.eval_rename, ← values_transposeMatrix]
      exact hg.2 q hq
  · intro hg
    refine ⟨fun p hp => hg p (Or.inl hp), ?_⟩
    intro p hp
    have h := hg _ (Or.inr ⟨p, hp, rfl⟩)
    rwa [MvPolynomial.eval_rename, ← values_transposeMatrix] at h

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [RCLike k] {n : Type} [Fintype n] [DecidableEq n]

theorem transposeMatrix_eq_star_of_real (hreal : ∀ z : k, star z = z)
    (g : GL n k) : transposeMatrix g = star g := by
  apply Units.ext
  ext i j
  exact (hreal (g.val j i)).symm

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.MatrixRepresentation

open _root_.Langlands.GroupScheme.GeneralLinear Langlands.Group.AlgebraicMatrixPowers

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n) [IsClosedImmersion ρ.hom.hom.left]

/-- Base-field adjoint stability forces every transpose cocharacter value
over every extension to satisfy the original closed-image equations. -/
theorem transpose_cocharacterUnitsHom_mem_affineMatrix_range
    (hreal : ∀ z : k, star z = z)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (t : Sˣ) :
    transposeMatrix (cocharacterUnitsHom (χ ≫ ρ) S t) ∈
      (ρ.affineMatrix (CommAlgCat.of k S)).range := by
  let ψ := χ ≫ ρ
  have hbase (a : kˣ) :
      transposeMatrix (cocharacterUnitsHom ψ k a) ∈
        zeroLocus k (Dynamic.embeddingIdeal ρ) := by
    rw [← ρ.mem_affineMatrix_range_iff_zeroLocus k,
      transposeMatrix_eq_star_of_real hreal]
    apply hstar
    exact ⟨Dynamic.cocharacterPointHom χ (CommAlgCat.of k k) a,
      ρ.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom_extension χ a⟩
  have huniv : transposeMatrix (weightMatrix ψ) ∈
      zeroLocus (LaurentPolynomial k) (Dynamic.embeddingIdeal ρ) := by
    intro p hp
    apply laurent_eq_zero_of_eval_units
    intro a
    let ev := cocharacterEvalExtensionUnit (k := k) a
    change ev (MvPolynomial.aeval (values (transposeMatrix (weightMatrix ψ))) p) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have hm : Matrix.GeneralLinearGroup.map ev.toRingHom
        (transposeMatrix (weightMatrix ψ)) =
          transposeMatrix (cocharacterUnitsHom ψ k a) := by
      rw [← transposeMatrix_map, map_weightMatrix_eval]
    have hv := values_map ev.toRingHom (transposeMatrix (weightMatrix ψ))
    rw [hm] at hv
    change MvPolynomial.aeval (ev.toRingHom ∘ values (transposeMatrix (weightMatrix ψ))) p = 0
    rw [← hv]
    exact hbase a p hp
  rw [ρ.mem_affineMatrix_range_iff_zeroLocus S]
  have h := map_mem_zeroLocus (cocharacterEvalExtensionUnit t) huniv
  rw [← transposeMatrix_map, map_weightMatrix_eval] at h
  exact h

/-- All extension values of a real cocharacter lie in the polynomial
adjoint core, assuming only adjoint stability over the base field. -/
theorem cocharacterUnitsHom_mem_starCore
    [IsScalarTower ℝ k S]
    (hreal : ∀ z : k, star z = z)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (t : Sˣ) :
    cocharacterUnitsHom (χ ≫ ρ) S t ∈
      starCore (ρ.affineMatrix (CommAlgCat.of k S)).range := by
  refine ⟨⟨Dynamic.cocharacterPointHom χ (CommAlgCat.of k S) t,
    ρ.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom_extension χ t⟩, ?_⟩
  apply (ρ.star_mem_affineMatrix_range_iff_transpose
    (star_algebraMap_eq_self_of_real hreal) _).mpr
  exact ρ.transpose_cocharacterUnitsHom_mem_affineMatrix_range hreal hstar χ t

end Langlands.GroupScheme.MatrixRepresentation
