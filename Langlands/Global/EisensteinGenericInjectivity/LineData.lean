import Langlands.GroupScheme.MatrixRepresentation.ParabolicOrbitWeightGap
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.MaximalParabolicLineDominance

/-! # A Chevalley line adapted to the split component of a parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- A Chevalley representation for the parabolic, with the selected line, diagonalized along
the split-component cocharacter, and with strictly smaller weights off the line. -/
theorem exists_lineData (r : ParabolicRootPresentation p l a) (hA : IsSplitTorus A.toGrp)
    (hG : IsConnectedReductive G) :
    ∃ (N : ℕ) (j : Fin N) (σ : MatrixRepresentation G (Fin N)) (e : Fin N → ℤ),
      σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j ∧
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) ≫ σ =
        GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e ∧
      σ.HasStrictOrbitWeightUpperBound e j := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := r.isCompatible.parabolic.isClosedSubgroup.mono
  obtain ⟨n, j₀, tau₀, h₀⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  have hstab : tau₀.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j₀ := h₀
  let iA : A.toGrp ⟶ G := a ≫ l ≫ p
  have hrange : SubgroupFunctor.range iA ≤ SubgroupFunctor.range p := by
    rintro T _ ⟨y, rfl⟩
    exact ⟨y ≫ (a ≫ l).hom.hom, rfl⟩
  have hTline :=
    MatrixRepresentation.HasExactCoordinateLineStabilizer.preservesCoordinateLine_restrict
      hstab iA hrange
  let D := torusEigenlineDiagonalization tau₀ iA hA j₀ hTline
  let σ := tau₀.basisConjugate D.basisMatrix
  have hstab' : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) D.lineIndex :=
    MatrixRepresentation.HasExactCoordinateLineStabilizer.basisConjugate hstab
      D.basisMatrix D.lineIndex D.lineBasis
  let ζ := r.splitComponentCocharacter
  let e : Fin (n + 1) → ℤ := fun i =>
    latticePairing A ((rationalCharacters.equivCharacterLattice A) (D.characters i)) ζ
  have hdiag : (CommGroupScheme.groupHom ζ ≫ a ≫ l ≫ p) ≫ σ =
      GeneralLinear.diagonalCocharacter (Fin (n + 1)) (CommRingCat.of F) e := by
    rw [Category.assoc]
    exact D.diagonal.cocharacter ζ
  have hline : (σ.restrict p).PreservesCoordinateLine D.lineIndex :=
    MatrixRepresentation.HasExactCoordinateLineStabilizer.preservesCoordinateLine_restrict
      hstab' p le_rfl
  let χc := CommGroupScheme.groupHom ζ ≫ a ≫ l ≫ p
  have hP : (Dynamic.parabolic χc).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  have hgap := σ.hasStrictOrbitWeightUpperBound_of_parabolic_eigenline χc e hdiag
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χc)) p
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) hP D.lineIndex hline
  exact ⟨n + 1, D.lineIndex, σ, e, hstab', hdiag, hgap⟩

end Langlands.Global.EisensteinGenericInjectivity
