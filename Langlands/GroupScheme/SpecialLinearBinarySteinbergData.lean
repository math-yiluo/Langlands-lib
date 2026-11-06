import Langlands.GroupScheme.SpecialLinearBinaryDiagonal
import Langlands.GroupScheme.SpecialLinearBinaryRegular
import Langlands.GroupScheme.SpecialLinearBinaryCofinal
import Langlands.GroupScheme.Reductive.SteinbergBigCellData

/-! # Complete binary Steinberg big-cell data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

variable {k : Type u} [Field k]

local instance {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] :
    IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

local instance : IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance : IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

local instance : IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance : IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

/-- Explicit complete Steinberg big-cell data for the actual binary special-linear group. -/
def steinbergBigCellData (p : ℕ) [Fact p.Prime] [CharP k p] [Infinite k] :
    SteinbergBigCellData (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) where
  Λ := DiagonalLattice
  latticeGroup := inferInstance
  j := diagonalInclusion (CommRingCat.of k)
  H := groupScheme (CommRingCat.of k)
  affineH := inferInstance
  i := inclusion (CommRingCat.of k)
  n := weylPoint (CommRingCat.of k)
  χ := characterCoordinate k
  d := lastEntryCoordinate k
  conditions := ⟨lastEntryCoordinate_mem_leftCovariant k,
    pointAlgebraHom_lastEntryCoordinate_mul_inv k,
    pointAlgebraHom_lastEntryCoordinate_one k _,
    lastEntryCoordinate_mem_nonZeroDivisors k,
    exists_factors_of_unit_lastEntryCoordinate k,
    exists_diagonal_lift_of_eq_conjugate (CommRingCat.of k),
    cofinal_covariantRegularRepresentation_isIrreducible p⟩

/-- All witnesses and all seven clauses of the big-cell conclusion for the actual
binary special-linear group, without any structural-existence premise. -/
theorem exists_steinbergBigCellData (p : ℕ) [Fact p.Prime]
    [CharP k p] [Infinite k] :
    let G := SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)
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
            hv)).rationalRepresentation.IsIrreducible) :=
  (steinbergBigCellData (k := k) p).exists_data

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
