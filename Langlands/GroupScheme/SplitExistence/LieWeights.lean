import Langlands.GroupScheme.SplitExistence.LieMatrix

/-! # Torus weights on the Lie algebra in matrix coordinates

A matrix `N` is a *weight matrix* of weight `ξ ∈ X` if its nonzero entries `(c, d)` all satisfy
`wt c - wt d = ξ`. In matrix coordinates the torus acts on such an `N` through the character `ξ`,
and the regular cocharacter acts through `t ↦ t ^ ℓ(ξ)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {k : Type u} [Field k]

/-- `N` is a weight matrix of weight `ξ`. -/
def IsWeightMatrix {A : Type*} [Zero A] (ξ : X) (N : Matrix (Fin D.n) (Fin D.n) A) : Prop :=
  ∀ c d, N c d ≠ 0 → D.wt c - D.wt d = ξ

variable {D}

theorem IsWeightMatrix.map {A B : Type*} [Zero A] [Zero B] {ξ : X}
    {N : Matrix (Fin D.n) (Fin D.n) A} (hN : D.IsWeightMatrix ξ N) (f : A → B) (hf : f 0 = 0) :
    D.IsWeightMatrix ξ (N.map f) := by
  intro c d h
  apply hN c d
  intro h0
  apply h
  rw [Matrix.map_apply, h0, hf]

/-- Conjugating a weight matrix by a torus element `diag(χ(wt c))` multiplies it by `χ(ξ)`. -/
theorem IsWeightMatrix.torusHom_conj {A : Type u} [CommRing A] {ξ : X}
    {N : Matrix (Fin D.n) (Fin D.n) A} (hN : D.IsWeightMatrix ξ N)
    (χ : Multiplicative X →* Aˣ) :
    (D.torusHom χ : Matrix (Fin D.n) (Fin D.n) A) * N *
        (((D.torusHom χ)⁻¹ : GL (Fin D.n) A) : Matrix (Fin D.n) (Fin D.n) A) =
      ((χ (Multiplicative.ofAdd ξ) : Aˣ) : A) • N := by
  rw [← map_inv, coe_torusHom, coe_torusHom]
  ext c d
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases h : N c d = 0
  · simp [h]
  · have hw := hN c d h
    have hc : D.wt c = ξ + D.wt d := by rw [← hw]; abel
    rw [hc, ofAdd_add, map_mul, Units.val_mul, MonoidHom.inv_apply]
    have hu : ((χ (Multiplicative.ofAdd (D.wt d)) : Aˣ) : A) *
        (((χ (Multiplicative.ofAdd (D.wt d)))⁻¹ : Aˣ) : A) = 1 := Units.mul_inv _
    linear_combination (((χ (Multiplicative.ofAdd ξ)) : Aˣ) : A) * N c d * hu

/-- Conjugating a weight matrix by `diag(s ^ ℓ(wt c))` multiplies it by `s ^ ℓ(ξ)`. -/
theorem IsWeightMatrix.diagonalUnits_conj {A : Type u} [CommRing A] {ξ : X}
    {N : Matrix (Fin D.n) (Fin D.n) A} (hN : D.IsWeightMatrix ξ N) (s : Aˣ) :
    (GeneralLinear.diagonalUnits A D.ellWeights s : Matrix (Fin D.n) (Fin D.n) A) * N *
        (((GeneralLinear.diagonalUnits A D.ellWeights s)⁻¹ : GL (Fin D.n) A) :
          Matrix (Fin D.n) (Fin D.n) A) =
      ((s ^ D.ℓ ξ : Aˣ) : A) • N := by
  rw [← D.torusHom_ellChar, hN.torusHom_conj]
  rfl

/-- The affine points of the torus, as characters. -/
def torusAffineEquiv (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints (Tk (X := X) k).toGrp A ≃* (Multiplicative X →* Aˣ) :=
  Corepresented.affinePointsEquiv (Diagonalizable.functor (CommRingCat.of k) X)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) X) (CommAlgCat.of k A)

namespace ChevGroup

variable (G : D.ChevGroup k)

/-- The regular cocharacter on affine points, in `GL_n`: `s ↦ diag(s ^ ℓ(wt c))`. -/
theorem affinePointsEquiv_cochar (A : CommAlgCat.{u} (CommRingCat.of k))
    (s : (algSpec (CommRingCat.of k)).obj (op A) ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) A
        (s ≫ G.cochar.hom.hom ≫ G.i.hom.hom) =
      GeneralLinear.diagonalUnits A D.ellWeights
        (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom s) := by
  rw [← Grp.comp_hom_hom, G.cochar_comp_i]
  exact GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter D.ellWeights A s

theorem characterValue_powerHom (A : Type u) [CommRing A] [Algebra k A] (m : ℤ)
    (s : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp A) :
    Lie.characterValue (Gm.powerHom _ m) s =
      Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of k A))).hom s ^ m := by
  have h1 : s ≫ (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) m)).hom.hom =
      s ^ m := by
    rw [Gm.powerHom_apply, comp_groupHom_zsmul]
    congr 1
  rw [Lie.characterValue]
  exact (congrArg _ h1).trans (map_zpow _ _ _)

variable [IsAffineHom G.H.X.hom]

/-- **A weight matrix of weight `ξ` is a weight vector of weight `ℓ(ξ)` for `λ`.** -/
theorem mem_weightSpace_cochar {ξ : X} (x : Additive (lieKernel G.H k))
    (hw : D.IsWeightMatrix ξ (G.lieMat k x)) :
    x ∈ weightSpace G.cochar (Gm.powerHom _ (D.ℓ ξ)) := by
  intro A _ _ s
  apply G.lieMat_injective A
  rw [G.lieMat_adjoint, LinearMap.map_smul, G.lieMat_map, characterValue_powerHom]
  have hA := hw.map (algebraMap k A) (map_zero _)
  have h := G.affinePointsEquiv_cochar (CommAlgCat.of k A) s
  rw [← Category.assoc] at h
  rw [h]
  convert hA.diagonalUnits_conj _ using 2
  all_goals rfl

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
