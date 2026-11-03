import Langlands.GroupScheme.Rational.BruhatCoveringAssembly
import Langlands.GroupScheme.Rational.BruhatOpenCellReduction

/-! # Rational Bruhat assembly from the explicit structural propositions -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The structural inputs used to assemble the rational Bruhat statement. -/
structure RationalBruhatStructuralInputs : Prop where
  oppositeCell : OppositeCellStatement.{u}
  genericCentralizer : GenericCentralizerStatement.{u}
  genericMinimalParabolic : GenericMinimalParabolicStatement.{u}
  parabolicIntersectionCentralizer : ParabolicIntersectionCentralizerStatement.{u}
  minimalParabolicSplitTorusConjugacy : MinimalParabolicSplitTorusConjugacyStatement.{u}

/-- Opposite-cell geometry discharges the contraction input in the
parabolic-covering assembly. -/
theorem hasRationalBruhatDecomposition_of_parabolicCovering_and_oppositeCell
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hcell : OppositeCellStatement.{u})
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hcover : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ n ∈ normalizerPoints i,
        ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
          g = p * n * q) :
    HasRationalBruhatDecomposition i ν := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact hasRationalBruhatDecomposition_of_parabolicCovering_and_productContractions i ν
    hZ hcover (hasNormalizerProductContractions_of_oppositeCell i ν hcell)

/-- The five displayed structural propositions imply the exact, unchanged
rational Bruhat statement at the same universe. -/
theorem rationalBruhatStatement_of_structural
    (hcell : OppositeCellStatement.{u})
    (hCentralizer : GenericCentralizerStatement.{u})
    (hMinimal : GenericMinimalParabolicStatement.{u})
    (hCommon : ParabolicIntersectionCentralizerStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u}) :
    RationalBruhatStatement.{u} := by
  intro k _ G hG T i hi ν
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hν
  exact hasRationalBruhatDecomposition_of_parabolicCovering_and_oppositeCell i ν hcell
    (hCentralizer k G hG T i hi ν hν)
    (rationalBruhatCovering_of_structural hMinimal hCommon hInside k G hG T i hi ν hν)

/-- A supplied structural input package proves the existing Bruhat statement. -/
theorem RationalBruhatStructuralInputs.rationalBruhatStatement
    (h : RationalBruhatStructuralInputs.{u}) :
    RationalBruhatStatement.{u} :=
  rationalBruhatStatement_of_structural h.oppositeCell h.genericCentralizer
    h.genericMinimalParabolic h.parabolicIntersectionCentralizer
    h.minimalParabolicSplitTorusConjugacy

end Langlands.GroupScheme
