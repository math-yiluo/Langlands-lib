import Langlands.GroupScheme.Reductive.ExtremalNegativeRho
import Langlands.GroupScheme.Reductive.CoordinateNonZeroDivisor

/-! # The unit cell of the constructed negative-rho matrix coefficient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The constructed diagonal coefficient is a nonzerodivisor on a connected
reductive group, without any weight hypothesis on the representation. -/
theorem diagonalMatrixCoefficient_mem_nonZeroDivisors
    (hG : IsConnectedReductive G) (ρ : MatrixRepresentation G n) (a : n) :
    diagonalMatrixCoefficient ρ a ∈ nonZeroDivisors (algebra G) :=
  mem_nonZeroDivisors_of_pointAlgebraHom_one G hG
    (pointAlgebraHom_one_diagonalMatrixCoefficient ρ a _)

end AffineCoordinates

namespace Dynamic

open AffineCoordinates MatrixRepresentation

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
  (i : H ⟶ G) (jT : T.toGrp ⟶ G) (hjT : IsMaximalTorus jT)
  {J : Type u} [Fintype J]
  (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (hroot : IsRootDatumOf jT P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
  (ν : cocharacterLattice T)
  (hH : (parabolic (CommGroupScheme.groupHom ν ≫ jT)).IsRepresentedBy i)
  (hZ : (centralizer (CommGroupScheme.groupHom ν ≫ jT)).IsRepresentedBy jT)
  (hc : IsClosedSubgroup i)
  (ρ : MatrixRepresentation G n) (e : n → ℤ)
  (hν : (CommGroupScheme.groupHom ν ≫ jT) ≫ ρ =
    GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
  (a : n) (ha : ∀ c, c ≠ a → e a < e c)
  (hweight : rationalCharacters.equivCharacterLattice T
      (characterRestrict (centralizerToParabolic hH hZ)
        (minimumWeightCharacter ρ (CommGroupScheme.groupHom ν ≫ jT) e hν i hH a ha)) =
    -IntegralWeylVector.rho P b hspan)
  (w : normalizerPoints jT)
  (hanti : characterAut (normalizingAut jT w) (-IntegralWeylVector.rho P b hspan) =
    IntegralWeylVector.rho P b hspan)
  (hQ : (parabolic (oppositeCocharacter (CommGroupScheme.groupHom ν ≫ jT))).IsRepresentedBy
    (i ≫ (G.innerIso w.val).hom))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

include hc hweight hanti hQ in
omit [Fintype J] in
/-- Every product of the supplied opposite parabolics has unit value under
the constructed coefficient, on every relative test scheme. -/
theorem isUnit_diagonalMatrixCoefficient_of_opposite_factors
    (V : Over (Spec (CommRingCat.of k))) (c c' : V ⟶ H.X) :
    IsUnit (pointAlgebraHom G V
      ((c ≫ i.hom.hom) * (c' ≫ (i ≫ (G.innerIso w.val).hom).hom.hom)⁻¹)
        (diagonalMatrixCoefficient ρ a)) := by
  rw [pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho ρ
    (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha
    P b hspan hweight w hQ hanti]
  have hl := diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ
    (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha P b hspan hweight
  have hval := pointAlgebraHom_leftCovariant i _ hl V c 1
  rw [mul_one, pointAlgebraHom_one_diagonalMatrixCoefficient, mul_one] at hval
  rw [hval]
  exact (isUnit_negativeRhoCoordinate hH hZ P b hspan V c').mul
    (isUnit_negativeRhoCoordinate hH hZ P b hspan V c)

section Global

variable [IsAlgClosed k] (hcover : BorelTorusBruhatCovering i jT)

include hG hT hjT hroot hc hweight hanti hQ hcover in
/-- The global unit-cell lift for the actual constructed diagonal coefficient.
No coordinate or eigen-law remains a supplied input. -/
def extremalNegativeRhoUnitCellLift
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g (diagonalMatrixCoefficient ρ a))) :
    V ⟶ (Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ jT)).X ⊗ H.X :=
  negativeRhoUnitCellLift hG hT i jT hjT P hroot b hspan ν hH hZ w hanti
    (diagonalMatrixCoefficient ρ a)
    (diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha P b hspan hweight)
    (pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha
      P b hspan hweight w hQ hanti)
    hcover hQ g hg

/-- Multiplication of the constructed lift recovers the original test point. -/
theorem extremalNegativeRhoUnitCellLift_comp
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g (diagonalMatrixCoefficient ρ a))) :
    extremalNegativeRhoUnitCellLift hG hT i jT hjT P hroot b hspan ν hH hZ hc
        ρ e hν a ha hweight w hanti hQ hcover g hg ≫
      SubgroupFunctor.cellMultiplication
        (Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ jT))
        (i ≫ (G.innerIso w.val).hom) = g :=
  negativeRhoUnitCellLift_comp hG hT i jT hjT P hroot b hspan ν hH hZ w hanti
    (diagonalMatrixCoefficient ρ a)
    (diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha P b hspan hweight)
    (pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha
      P b hspan hweight w hQ hanti)
    hcover hQ g hg

include hG hT hjT hroot hc hweight hanti hQ hcover in
/-- Unit values of the constructed coefficient give global factors in the
two supplied opposite parabolics on the original test scheme. -/
theorem exists_opposite_factors_of_unit_diagonalMatrixCoefficient
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X)
    (hg : IsUnit (pointAlgebraHom G V g (diagonalMatrixCoefficient ρ a))) :
    ∃ c c' : V ⟶ H.X,
      g = (c ≫ i.hom.hom) * (c' ≫ (i ≫ (G.innerIso w.val).hom).hom.hom)⁻¹ :=
  exists_opposite_parabolic_factors_of_unit_negativeRho
    hG hT i jT hjT P hroot b hspan ν hH hZ w hanti
    (diagonalMatrixCoefficient ρ a)
    (diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha P b hspan hweight)
    (pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho ρ
      (CommGroupScheme.groupHom ν ≫ jT) e hν i hH jT hZ hc a ha
      P b hspan hweight w hQ hanti)
    hcover hQ g hg

include hG hT hjT hroot hc hweight hanti hQ hcover in
/-- The unit locus of the actual diagonal coefficient is exactly the
opposite-parabolic product, as a condition on every relative test point. -/
theorem isUnit_diagonalMatrixCoefficient_iff_opposite_factors
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X) :
    IsUnit (pointAlgebraHom G V g (diagonalMatrixCoefficient ρ a)) ↔
      ∃ c c' : V ⟶ H.X,
        g = (c ≫ i.hom.hom) * (c' ≫ (i ≫ (G.innerIso w.val).hom).hom.hom)⁻¹ := by
  constructor
  · exact exists_opposite_factors_of_unit_diagonalMatrixCoefficient hG hT i jT hjT
      P hroot b hspan ν hH hZ hc ρ e hν a ha hweight w hanti hQ hcover g
  · rintro ⟨c, c', rfl⟩
    exact isUnit_diagonalMatrixCoefficient_of_opposite_factors i jT P b hspan ν
      hH hZ hc ρ e hν a ha hweight w hanti hQ V c c'

end Global

end Dynamic

end Langlands.GroupScheme
