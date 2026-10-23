import Langlands.Shimura.Unitary.ComplexWeightSpaces
import Langlands.Shimura.Unitary.ComplexGroupPoints
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra Module Matrix
open scoped CategoryTheory.MonObj Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable {S : Type*} [CommRing S] {n : ℕ}
  (a b : Sˣ → Matrix (Fin n) (Fin n) S)

/-- An intertwining linear equivalence preserves the common inverse-weight condition. -/
theorem mem_inverseWeightSpace_iff
    (e : (Fin n → S) ≃ₗ[S] (Fin n → S))
    (h : ∀ u v, b u *ᵥ e v = e (a u *ᵥ v)) (v : Fin n → S) :
    e v ∈ inverseWeightSpace b ↔ v ∈ inverseWeightSpace a := by
  change (∀ u : Sˣ, b u *ᵥ e v = (↑(u⁻¹) : S) • e v) ↔
    (∀ u : Sˣ, a u *ᵥ v = (↑(u⁻¹) : S) • v)
  simp_rw [h, ← e.map_smul, e.injective.eq_iff]

/-- Restriction of an intertwining equivalence to the actual inverse-weight submodules. -/
def inverseWeightSpaceEquiv
    (e : (Fin n → S) ≃ₗ[S] (Fin n → S))
    (h : ∀ u v, b u *ᵥ e v = e (a u *ᵥ v)) :
    inverseWeightSpace a ≃ₗ[S] inverseWeightSpace b where
  toFun v := ⟨e v, (mem_inverseWeightSpace_iff a b e h v).mpr v.property⟩
  invFun w := ⟨e.symm w, (mem_inverseWeightSpace_iff a b e h (e.symm w)).mp
    (by simpa only [e.apply_symm_apply] using w.property)⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  map_add' v w := Subtype.ext (e.map_add v w)
  map_smul' c v := Subtype.ext (e.map_smul c v)

/-- Conjugation by a matrix unit induces a linear equivalence of inverse-weight spaces. -/
def inverseWeightSpaceConjEquiv (g : (Matrix (Fin n) (Fin n) S)ˣ) :
    inverseWeightSpace a ≃ₗ[S]
      inverseWeightSpace (fun u => (g : Matrix (Fin n) (Fin n) S) * a u * (↑(g⁻¹) : Matrix (Fin n) (Fin n) S)) :=
  inverseWeightSpaceEquiv a _
    (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv (by
      intro u v
      change ((g : Matrix (Fin n) (Fin n) S) * a u * (↑(g⁻¹) : Matrix (Fin n) (Fin n) S)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) S) *ᵥ v) =
          (g : Matrix (Fin n) (Fin n) S) *ᵥ (a u *ᵥ v)
      simp only [mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one])

/-- The numerical inverse-weight rank is invariant under matrix-unit conjugation. -/
theorem finrank_inverseWeightSpace_conj (g : (Matrix (Fin n) (Fin n) S)ˣ) :
    Module.finrank S
      (inverseWeightSpace (fun u => (g : Matrix (Fin n) (Fin n) S) * a u * (↑(g⁻¹) : Matrix (Fin n) (Fin n) S))) =
        Module.finrank S (inverseWeightSpace a) :=
  (inverseWeightSpaceConjEquiv a g).finrank_eq.symm

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The inverse-weight submodule in a split matrix factor of a family of actual group points. -/
def complexPointWeightSpace (T : Over (Spec (CommRingCat.of ℂ)))
    (a : (AlgebraInvolution.complexTestAlgebra T)ˣ →
      (T ⟶ D.complexRationalGroupScheme.X)) (τ : E →+* ℝ) :
    Submodule (AlgebraInvolution.complexTestAlgebra T)
      (Fin n → AlgebraInvolution.complexTestAlgebra T) :=
  ComplexMatrix.inverseWeightSpace fun u =>
    ((D.complexGroupPointsEquiv C T (a u)).1 τ :
      Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by an actual Harris group point gives an equivalence of its matrix weight spaces. -/
def complexPointWeightSpaceConjEquiv (T : Over (Spec (CommRingCat.of ℂ)))
    (a : (AlgebraInvolution.complexTestAlgebra T)ˣ →
      (T ⟶ D.complexRationalGroupScheme.X)) (τ : E →+* ℝ)
    (g : T ⟶ D.complexRationalGroupScheme.X) :
    D.complexPointWeightSpace C T a τ ≃ₗ[AlgebraInvolution.complexTestAlgebra T]
      D.complexPointWeightSpace C T (fun u => g * a u * g⁻¹) τ := by
  have hm (u : (AlgebraInvolution.complexTestAlgebra T)ˣ) :
      D.complexGroupPointsEquiv C T (g * a u * g⁻¹) =
        D.complexGroupPointsEquiv C T g * D.complexGroupPointsEquiv C T (a u) *
          (D.complexGroupPointsEquiv C T g)⁻¹ := by
    rw [(D.complexGroupPointsEquiv C T).map_mul,
      (D.complexGroupPointsEquiv C T).map_mul,
      (D.complexGroupPointsEquiv C T).map_inv]
  unfold complexPointWeightSpace
  have hf :
      (fun u => ((D.complexGroupPointsEquiv C T (g * a u * g⁻¹)).1 τ :
        Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))) =
      (fun u => ((D.complexGroupPointsEquiv C T g).1 τ :
          Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T)) *
        ((D.complexGroupPointsEquiv C T (a u)).1 τ :
          Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T)) *
        (↑(((D.complexGroupPointsEquiv C T g).1 τ)⁻¹) :
          Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T))) := by
    funext u
    rw [hm]
    rfl
  rw [hf]
  exact ComplexMatrix.inverseWeightSpaceConjEquiv
    (fun u => ((D.complexGroupPointsEquiv C T (a u)).1 τ :
      Matrix (Fin n) (Fin n) (AlgebraInvolution.complexTestAlgebra T)))
    ((D.complexGroupPointsEquiv C T g).1 τ)

/-- The inverse-weight rank of any actual point family is invariant under conjugation. -/
theorem finrank_complexPointWeightSpace_conj (T : Over (Spec (CommRingCat.of ℂ)))
    (a : (AlgebraInvolution.complexTestAlgebra T)ˣ →
      (T ⟶ D.complexRationalGroupScheme.X)) (τ : E →+* ℝ)
    (g : T ⟶ D.complexRationalGroupScheme.X) :
    Module.finrank (AlgebraInvolution.complexTestAlgebra T)
      (D.complexPointWeightSpace C T (fun u => g * a u * g⁻¹) τ) =
        Module.finrank (AlgebraInvolution.complexTestAlgebra T)
          (D.complexPointWeightSpace C T a τ) :=
  (D.complexPointWeightSpaceConjEquiv C T a τ g).finrank_eq.symm

/-- Evaluation of the first-factor Kottwitz cocharacter recovers its existing matrix weight space. -/
theorem complexPointWeightSpace_kottwitz (T : Over (Spec (CommRingCat.of ℂ)))
    (τ : E →+* ℝ) :
    D.complexPointWeightSpace C T
      (fun u => (GroupScheme.Gm.pointsEquiv _ T).symm u ≫
        (D.kottwitzCocharacter C true).hom.hom) τ =
      D.kottwitzMatrixWeightSpace C T τ true := rfl

/-- Every conjugate of the actual first-factor Kottwitz family has its positive signature rank. -/
theorem finrank_complexPointWeightSpace_conj_kottwitz
    (T : Over (Spec (CommRingCat.of ℂ))) [Nontrivial Γ(T.left, ⊤)]
    (τ : E →+* ℝ) (g : T ⟶ D.complexRationalGroupScheme.X) :
    Module.finrank (AlgebraInvolution.complexTestAlgebra T)
      (D.complexPointWeightSpace C T
        (fun u => g * ((GroupScheme.Gm.pointsEquiv _ T).symm u ≫
          (D.kottwitzCocharacter C true).hom.hom) * g⁻¹) τ) =
      if τ = C.distinguished then n - 1 else n := by
  rw [D.finrank_complexPointWeightSpace_conj, D.complexPointWeightSpace_kottwitz]
  exact D.finrank_kottwitzMatrixWeightSpace_true C T τ

end Langlands.Shimura.CentralSimpleUnitaryData
