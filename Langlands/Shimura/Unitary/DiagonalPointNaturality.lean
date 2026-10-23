import Langlands.Shimura.Unitary.DiagonalPointConjugacy

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable {S R : Type*} [CommRing S] [CommRing R] {n : ℕ}

/-- Inverse/trivial diagonal units commute with coefficient homomorphisms. -/
theorem inverseDiagonalUnit_map (f : S →+* R) (p : Fin n → Prop) [DecidablePred p]
    (u : Sˣ) :
    Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+*
      Matrix (Fin n) (Fin n) R).toMonoidHom (inverseDiagonalUnit S p u) =
        inverseDiagonalUnit R p (Units.map f.toMonoidHom u) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : p i <;> simp [inverseDiagonalUnit, RingHom.mapMatrix_apply,
      hi]
  · simp [inverseDiagonalUnit, RingHom.mapMatrix_apply, hij]

/-- A chosen permutation matrix unit is independent of the coefficient ring. -/
theorem weightPermutationUnit_map (f : S →+* R) (σ : Equiv.Perm (Fin n)) :
    Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+*
      Matrix (Fin n) (Fin n) R).toMonoidHom (weightPermutationUnit S σ) =
        weightPermutationUnit R σ := by
  apply Units.ext
  ext i j
  by_cases h : σ i = j <;>
    simp [weightPermutationUnit, RingHom.mapMatrix_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

/-- Support matching conjugators commute with coefficient homomorphisms. -/
theorem diagonalWeightConjugator_map (f : S →+* R)
    (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (h : (Finset.univ.filter p).card = (Finset.univ.filter q).card) :
    Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) S →+*
      Matrix (Fin n) (Fin n) R).toMonoidHom (diagonalWeightConjugator p q S h) =
        diagonalWeightConjugator p q R h :=
  weightPermutationUnit_map f _

/-- The inverse/trivial diagonal family is a homomorphism on scalar units. -/
def inverseDiagonalHom (S : Type*) [CommRing S] (p : Fin n → Prop) [DecidablePred p] :
    Sˣ →* (Matrix (Fin n) (Fin n) S)ˣ where
  toFun := inverseDiagonalUnit S p
  map_one' := by
    apply Units.ext
    change Matrix.diagonal _ = (1 : Matrix (Fin n) (Fin n) S)
    simp
  map_mul' u v := by
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hj : p j <;> simp [hj, mul_comm]

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual diagonal point family commutes with pullback of test schemes. -/
theorem diagonalWeightPointFamily_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (p : (E →+* ℝ) → Fin n → Prop)
    (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
    a ≫ D.diagonalWeightPointFamily C T p u =
      D.diagonalWeightPointFamily C T' p (Units.map a.left.appTop.hom.toMonoidHom u) := by
  apply (D.complexGroupPointsEquiv C T').injective
  rw [D.complexGroupPointsEquiv_naturality, D.diagonalWeightPointFamily_split,
    D.diagonalWeightPointFamily_split]
  apply Prod.ext
  · funext τ
    exact ComplexMatrix.inverseDiagonalUnit_map a.left.appTop.hom (p τ) u
  · exact map_inv (Units.map a.left.appTop.hom.toMonoidHom) u

/-- The actual chosen conjugators commute with pullback of test schemes. -/
theorem diagonalWeightPointConjugator_naturality {T T' : Over (Spec (CommRingCat.of ℂ))}
    (a : T' ⟶ T) (p q : (E →+* ℝ) → Fin n → Prop)
    (h : ∀ τ, (Finset.univ.filter (p τ)).card = (Finset.univ.filter (q τ)).card) :
    a ≫ D.diagonalWeightPointConjugator C T p q h =
      D.diagonalWeightPointConjugator C T' p q h := by
  apply (D.complexGroupPointsEquiv C T').injective
  rw [D.complexGroupPointsEquiv_naturality]
  simp only [diagonalWeightPointConjugator, MulEquiv.apply_symm_apply]
  apply Prod.ext
  · funext τ
    exact ComplexMatrix.diagonalWeightConjugator_map a.left.appTop.hom (p τ) (q τ) (h τ)
  · exact map_one (Units.map a.left.appTop.hom.toMonoidHom)

/-- The actual diagonal family as a homomorphism from the group of scalar units. -/
def diagonalWeightPointHom (T : Over (Spec (CommRingCat.of ℂ)))
    (p : (E →+* ℝ) → Fin n → Prop) :
    (AlgebraInvolution.complexTestAlgebra T)ˣ →* (T ⟶ D.complexRationalGroupScheme.X) where
  toFun := D.diagonalWeightPointFamily C T p
  map_one' := by
    apply (D.complexGroupPointsEquiv C T).injective
    rw [D.diagonalWeightPointFamily_split, map_one]
    apply Prod.ext
    · funext τ
      exact map_one (ComplexMatrix.inverseDiagonalHom _ (p τ))
    · exact inv_one
  map_mul' u v := by
    apply (D.complexGroupPointsEquiv C T).injective
    rw [D.diagonalWeightPointFamily_split, map_mul,
      D.diagonalWeightPointFamily_split, D.diagonalWeightPointFamily_split]
    apply Prod.ext
    · funext τ
      exact map_mul (ComplexMatrix.inverseDiagonalHom _ (p τ)) u v
    · exact mul_inv u v

end Langlands.Shimura.CentralSimpleUnitaryData
