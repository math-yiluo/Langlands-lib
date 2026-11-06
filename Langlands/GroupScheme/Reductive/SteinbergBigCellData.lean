import Langlands.GroupScheme.Reductive.SteinbergBigCellStatement

/-! # Bundled witnesses for the complete Steinberg big-cell conclusion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- The actual witnesses and all seven laws of the Steinberg big-cell conclusion.
This structure assumes no structural existence theorem. -/
structure SteinbergBigCellData (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] where
  Λ : Type u
  [latticeGroup : AddCommGroup Λ]
  j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G
  H : GroupScheme (Spec (CommRingCat.of k))
  [affineH : IsAffineHom H.X.hom]
  i : H ⟶ G
  n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  χ : AffineCoordinates.algebra H
  d : AffineCoordinates.algebra G
  conditions :
    d ∈ AffineCoordinates.leftCovariantSubspace i χ ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        AffineCoordinates.pointAlgebraHom G T
            (g * (h ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) d =
          AffineCoordinates.pointAlgebraHom H T h χ *
            AffineCoordinates.pointAlgebraHom G T g d) ∧
      AffineCoordinates.pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1 ∧
      d ∈ nonZeroDivisors (AffineCoordinates.algebra G) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        IsUnit (AffineCoordinates.pointAlgebraHom G T g d) →
          ∃ b b' : T ⟶ H.X,
            g = (b ≫ i.hom.hom) * (b' ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (c c' : T ⟶ H.X),
        c ≫ i.hom.hom = c' ≫ (i ≫ (G.innerIso n).hom).hom.hom →
          ∃ t : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X,
            c ≫ i.hom.hom = t ≫ j.hom.hom) ∧
      (∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
        (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e'))),
        (Chevalley.affineRegularRepresentation G _ bX
          (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace i (χ ^ e') f
            hv)).rationalRepresentation.IsIrreducible)

/-- Forgetting the bundle gives precisely the existential conclusion of the target. -/
theorem SteinbergBigCellData.exists_data
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (D : SteinbergBigCellData G) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ)
      (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
      (H : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom H.X.hom)
      (i : H ⟶ G) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (χ : AffineCoordinates.algebra H) (d : AffineCoordinates.algebra G),
      d ∈ AffineCoordinates.leftCovariantSubspace i χ ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        AffineCoordinates.pointAlgebraHom G T
            (g * (h ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) d =
          AffineCoordinates.pointAlgebraHom H T h χ *
            AffineCoordinates.pointAlgebraHom G T g d) ∧
      AffineCoordinates.pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1 ∧
      d ∈ nonZeroDivisors (AffineCoordinates.algebra G) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
        IsUnit (AffineCoordinates.pointAlgebraHom G T g d) →
          ∃ b b' : T ⟶ H.X,
            g = (b ≫ i.hom.hom) * (b' ≫ (i ≫ (G.innerIso n).hom).hom.hom)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (c c' : T ⟶ H.X),
        c ≫ i.hom.hom = c' ≫ (i ≫ (G.innerIso n).hom).hom.hom →
          ∃ t : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X,
            c ≫ i.hom.hom = t ≫ j.hom.hom) ∧
      (∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
        (bX : Module.Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e'))),
        (Chevalley.affineRegularRepresentation G _ bX
          (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace i (χ ^ e') f
            hv)).rationalRepresentation.IsIrreducible) := by
  cases D with
  | @mk Λ hΛ j H hH i n χ d h => exact ⟨Λ, hΛ, j, H, hH, i, n, χ, d, h⟩

end Langlands.GroupScheme
