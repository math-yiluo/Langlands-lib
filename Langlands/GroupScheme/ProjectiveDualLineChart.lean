import Langlands.GroupScheme.ProjectiveOrbit
import Langlands.GroupScheme.SchemeActionInvariantOpen
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry

/-! # Invariant coordinate charts of matrix-equivariant maps to projective space -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A linear coordinate change whose `j`-th coordinate form is a unit multiple of itself
preserves the coordinate chart `D₊(X j)`. -/
theorem ProjectiveSpace.linearAction_preimage_coordinateOpen (R : Type u) [CommRing R]
    (n : ℕ) (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (j : Fin (n + 1)) (c : Rˣ)
    (he : (LinearMap.proj j).comp e.toLinearMap = (c : R) • LinearMap.proj j) :
    ProjectiveSpace.linearAction R n e ⁻¹ᵁ projectiveSpaceCoordinateOpen R n j =
      projectiveSpaceCoordinateOpen R n j := by
  ext p
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, mem_projectiveSpaceCoordinateOpen,
    mem_projectiveSpaceCoordinateOpen, ProjectiveSpace.linearAction_mem_iff,
    linearSubstitution_X, he, map_smul, Submodule.coe_smul, linearFormPolynomialEquiv_proj,
    MvPolynomial.smul_eq_C_mul, ← HomogeneousIdeal.mem_iff, ← HomogeneousIdeal.mem_iff,
    Ideal.unit_mul_mem_iff_mem _ (c.isUnit.map MvPolynomial.C)]

namespace RelativeProjectiveSpace

/-- Every polynomial projection pulls the polynomial chart back to the relative chart. -/
theorem toPolynomial_preimage_coordinateOpen {K : Type u} [CommRing K] {S : Scheme.{u}}
    (n : ℕ) (a : S ⟶ Spec (CommRingCat.of K)) (j : Fin (n + 1)) :
    toPolynomial n a ⁻¹ᵁ projectiveSpaceCoordinateOpen K n j = coordinateOpen S n j := by
  rw [coordinateOpen, ← toPolynomial_toIntegral (n := n) a, Scheme.Hom.comp_preimage,
    polynomialToIntegral_preimage_coordinateOpen]

/-- A coefficient coordinate change fixing the `j`-th coordinate form up to a unit
preserves the relative chart `D₊(X j)`. -/
theorem linearAction_preimage_coordinateOpen {K : Type u} [CommRing K] {S : Scheme.{u}}
    (n : ℕ) (a : S ⟶ Spec (CommRingCat.of K))
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) (j : Fin (n + 1)) (c : Kˣ)
    (he : (LinearMap.proj j).comp e.toLinearMap = (c : K) • LinearMap.proj j) :
    linearAction a e ⁻¹ᵁ coordinateOpen S n j = coordinateOpen S n j := by
  rw [← toPolynomial_preimage_coordinateOpen n a j, ← Scheme.Hom.comp_preimage,
    linearAction_toPolynomial, Scheme.Hom.comp_preimage,
    ProjectiveSpace.linearAction_preimage_coordinateOpen K n e j c he]

end RelativeProjectiveSpace

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry

namespace ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An invertible matrix whose `j`-th row is a unit multiple of the `j`-th standard row
preserves the relative coordinate chart `D₊(X j)`. -/
theorem matrixAction_preimage_coordinateOpen (n : ℕ) {T : Scheme.{u}}
    (M : GL (Fin (n + 1)) Γ(T, ⊤)) (j : Fin (n + 1)) (c : Γ(T, ⊤)ˣ)
    (hM : (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) j = Pi.single j (c : Γ(T, ⊤))) :
    matrixAction n M ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen T n j =
      RelativeProjectiveSpace.coordinateOpen T n j := by
  refine RelativeProjectiveSpace.linearAction_preimage_coordinateOpen n T.toSpecΓ
    (coordinateEquiv n M) j c ?_
  apply LinearMap.ext
  intro v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearEquiv.coe_coe, coordinateEquiv_apply, LinearMap.smul_apply,
    Matrix.mulVec, dotProduct, hM]
  simp [Pi.single_apply]

/-- If the `j`-th row of `P * M` is a unit multiple of the `j`-th row of `P`, then `M`
preserves the chart obtained from `D₊(X j)` by the coordinate change `P`. -/
theorem matrixAction_preimage_translatedChart (n : ℕ) {T : Scheme.{u}}
    (P M : GL (Fin (n + 1)) Γ(T, ⊤)) (j : Fin (n + 1)) (c : Γ(T, ⊤)ˣ)
    (hPM : Matrix.vecMul ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) j)
        (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) =
      (c : Γ(T, ⊤)) • (P : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) j) :
    matrixAction n M ⁻¹ᵁ
        (matrixAction n P ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen T n j) =
      matrixAction n P ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen T n j := by
  have hN : ((P * M * P⁻¹ : GL (Fin (n + 1)) Γ(T, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) j = Pi.single j (c : Γ(T, ⊤)) := by
    have hrow : ∀ (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)),
        (A * B) j = Matrix.vecMul (A j) B := by
      intro A B
      ext l
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    have hPP : ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) *
        ((P⁻¹ : GL (Fin (n + 1)) Γ(T, ⊤)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤))) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hrow, hrow, hPM, Matrix.smul_vecMul, ← hrow, hPP]
    ext l
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hPMeq : P * M = (P * M * P⁻¹) * P := by group
  rw [← Scheme.Hom.comp_preimage, ← matrixAction_mul, hPMeq, matrixAction_mul,
    Scheme.Hom.comp_preimage, matrixAction_preimage_coordinateOpen n _ j c hN]

variable {n : ℕ} {R : CommRingCat.{u}}

/-- The section of relative projective space over a test scheme determined by a test
point of the ambient projective scheme. -/
def pointSection {Z : Over (Spec R)} (y : Z ⟶ ambient n R) :
    Z.left ⟶ RelativeProjectiveSpace Z.left n :=
  RelativeProjectiveSpace.lift n (𝟙 Z.left)
    (y.left ≫ RelativeProjectiveSpace.toIntegral (Spec R) n)

@[reassoc (attr := simp)]
theorem pointSection_map {Z : Over (Spec R)} (y : Z ⟶ ambient n R) :
    pointSection y ≫ RelativeProjectiveSpace.map n Z.hom = y.left := by
  apply RelativeProjectiveSpace.hom_ext
  · simp only [pointSection, Category.assoc, RelativeProjectiveSpace.map_toBase,
      RelativeProjectiveSpace.lift_toBase_assoc, Category.id_comp]
    exact (Over.w y).symm
  · simp [pointSection]

/-- A morphism to the ambient projective scheme is equivariant for a group action and a
matrix representation when, on every test, translating a point by the action becomes the
matrix action on the corresponding projective section. -/
def IsMatrixEquivariant {H : GroupScheme (Spec R)} {X : Over (Spec R)}
    (a : SchemeAction H X) (ρ : MatrixRepresentation H (Fin (n + 1)))
    (φ : X ⟶ ambient n R) : Prop :=
  ∀ (Z : Over (Spec R)) (h : Z ⟶ H.X) (x : Z ⟶ X),
    (a.act h x ≫ φ).left =
      pointSection (x ≫ φ) ≫ matrixAction n (ρ.pointMatrix Z h) ≫
        RelativeProjectiveSpace.map n Z.hom

/-- Matrix equivariance is preserved by restricting the acting group. -/
theorem IsMatrixEquivariant.restrict {G H : GroupScheme (Spec R)} {X : Over (Spec R)}
    {a : SchemeAction G X} {ρ : MatrixRepresentation G (Fin (n + 1))}
    {φ : X ⟶ ambient n R} (hφ : IsMatrixEquivariant a ρ φ) (f : H ⟶ G) :
    IsMatrixEquivariant (a.restrict f) (ρ.restrict f) φ := by
  intro Z h x
  rw [SchemeAction.restrict_act, MatrixRepresentation.pointMatrix_restrict]
  exact hφ Z (h ≫ f.hom.hom) x

/-- The chart of the ambient projective scheme obtained from `D₊(X j)` by the coordinate
change `P`; it is `D₊` of the linear form given by the `j`-th row of `P`. -/
def translatedChart (P : GL (Fin (n + 1)) Γ(Spec R, ⊤)) (j : Fin (n + 1)) :
    (ambient n R).left.Opens :=
  matrixAction n P ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen (Spec R) n j

/-- The translated chart is affine. -/
theorem isAffineOpen_translatedChart (P : GL (Fin (n + 1)) Γ(Spec R, ⊤))
    (j : Fin (n + 1)) : IsAffineOpen (translatedChart P j) := by
  have : IsIso (matrixAction n P) :=
    ⟨⟨matrixAction n P⁻¹, matrixAction_hom_inv n P, matrixAction_inv_hom n P⟩⟩
  exact (RelativeProjectiveSpace.isAffineOpen_coordinateOpen (Spec R) n j).preimage _

/-- Pulling the translated chart back to a test gives the chart translated by the pulled-back
coordinate change. -/
theorem map_preimage_translatedChart {Z : Scheme.{u}} (f : Z ⟶ Spec R)
    (P : GL (Fin (n + 1)) Γ(Spec R, ⊤)) (j : Fin (n + 1)) :
    RelativeProjectiveSpace.map n f ⁻¹ᵁ translatedChart P j =
      matrixAction n (Matrix.GeneralLinearGroup.map f.appTop.hom P) ⁻¹ᵁ
        RelativeProjectiveSpace.coordinateOpen Z n j := by
  rw [translatedChart, ← Scheme.Hom.comp_preimage, map_matrixAction,
    Scheme.Hom.comp_preimage, RelativeProjectiveSpace.map_preimage_coordinateOpen]

/-- If every test point of the acting group multiplies the `j`-th row of the coordinate
change `P` by a unit, the inverse image of the translated chart is an invariant open. -/
theorem isInvariantOpen_preimage_translatedChart {H : GroupScheme (Spec R)}
    {X : Over (Spec R)} (a : SchemeAction H X) (ρ : MatrixRepresentation H (Fin (n + 1)))
    (φ : X ⟶ ambient n R) (hφ : IsMatrixEquivariant a ρ φ)
    (P : GL (Fin (n + 1)) Γ(Spec R, ⊤)) (j : Fin (n + 1))
    (hj : ∀ (Z : Over (Spec R)) (h : Z ⟶ H.X), ∃ c : Γ(Z.left, ⊤)ˣ,
      Matrix.vecMul
          ((Matrix.GeneralLinearGroup.map Z.hom.appTop.hom P :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j)
          (ρ.pointMatrix Z h : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        (c : Γ(Z.left, ⊤)) •
          (Matrix.GeneralLinearGroup.map Z.hom.appTop.hom P :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j) :
    a.IsInvariantOpen (φ.left ⁻¹ᵁ translatedChart P j) := by
  obtain ⟨c, hc⟩ := hj (H.X ⊗ X) (fst H.X X)
  have hact : a.act (fst H.X X) (snd H.X X) = a.hom := by
    simp [SchemeAction.act]
  have key := hφ (H.X ⊗ X) (fst H.X X) (snd H.X X)
  rw [hact] at key
  unfold SchemeAction.IsInvariantOpen
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
  change (a.hom ≫ φ).left ⁻¹ᵁ _ = (snd H.X X ≫ φ).left ⁻¹ᵁ _
  rw [key, ← pointSection_map (snd H.X X ≫ φ)]
  simp only [Scheme.Hom.comp_preimage, map_preimage_translatedChart,
    matrixAction_preimage_translatedChart n _ _ j c hc]

/-- Under an affine equivariant map, a translated chart whose defining row is fixed up to
units by the restricted group gives an affine open invariant under the restricted action. -/
theorem isAffineOpen_isInvariantOpen_preimage_translatedChart
    {G H : GroupScheme (Spec R)} {X : Over (Spec R)} (a : SchemeAction G X)
    (ρ : MatrixRepresentation G (Fin (n + 1))) (φ : X ⟶ ambient n R)
    [IsAffineHom φ.left] (hφ : IsMatrixEquivariant a ρ φ) (f : H ⟶ G)
    (P : GL (Fin (n + 1)) Γ(Spec R, ⊤)) (j : Fin (n + 1))
    (hj : ∀ (Z : Over (Spec R)) (h : Z ⟶ H.X), ∃ c : Γ(Z.left, ⊤)ˣ,
      Matrix.vecMul
          ((Matrix.GeneralLinearGroup.map Z.hom.appTop.hom P :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j)
          (ρ.pointMatrix Z (h ≫ f.hom.hom) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        (c : Γ(Z.left, ⊤)) •
          (Matrix.GeneralLinearGroup.map Z.hom.appTop.hom P :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j) :
    IsAffineOpen (φ.left ⁻¹ᵁ translatedChart P j) ∧
      (a.restrict f).hom.left ⁻¹ᵁ (φ.left ⁻¹ᵁ translatedChart P j) =
        (snd H.X X).left ⁻¹ᵁ (φ.left ⁻¹ᵁ translatedChart P j) := by
  refine ⟨(isAffineOpen_translatedChart P j).preimage φ.left, ?_⟩
  exact isInvariantOpen_preimage_translatedChart (a.restrict f) (ρ.restrict f) φ
    (hφ.restrict f) P j (fun Z h => by
      simpa only [MatrixRepresentation.pointMatrix_restrict] using hj Z h)

end ProjectiveOrbit

end Langlands.GroupScheme
