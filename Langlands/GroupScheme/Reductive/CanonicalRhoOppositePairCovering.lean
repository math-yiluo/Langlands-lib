import Langlands.GroupScheme.Rational.OppositePairBruhatCovering
import Langlands.GroupScheme.Rational.AlgClosedOppositeFactorPairsStatement
import Langlands.GroupScheme.Reductive.IntegralOppositionRepresentative
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.HighestWeightBigCell
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Canonical rho big-cell geometric data from opposite root pairs

The Bruhat covering for the parabolic of the polarized integral rho vector follows from
opposite root pairs. It fills the covering hypothesis of the Library's canonical big-cell
assemblies. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local instance canonicalRhoOppositePairIsAffine {K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

namespace IsRootDatumOf

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    {J : Type v} [Fintype J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- **Bruhat covering for the canonical rho parabolic.** Over an algebraically closed field,
let `j` be a split maximal torus of a connected reductive group with root datum `P`, base `b`
and integral coroot span. If every nonidentity point of every actual root group admits an
opposite factor pair, then the closed subgroup representing the dynamic parabolic of the
polarization of the integral rho vector satisfies the Bruhat covering with the torus `j`. -/
theorem borelTorusBruhatCovering_polarization_rho_of_oppositeFactorPairs [IsAlgClosed k]
    [Mono j.hom.hom.left] (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (hE : RelativeRoot.HasOppositeFactorPairs j) :
    BorelTorusBruhatCovering
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)) j := by
  have hi : IsMaximalSplitTorus j := hj.isMaximalSplitTorus hT
  exact borelTorusBruhatCovering_parabolicHom_of_oppositeFactorPairs hG hi
    (hP.polarization_rho_isGeneric b hspan) hE

/-- The same covering with the rank-one input supplied by
`AlgClosedOppositeFactorPairsStatement`. -/
theorem borelTorusBruhatCovering_polarization_rho_of_statement [IsAlgClosed k]
    (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (hE : AlgClosedOppositeFactorPairsStatement.{u}) :
    BorelTorusBruhatCovering
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)) j := by
  have hi : IsMaximalSplitTorus j := hj.isMaximalSplitTorus hT
  have := hi.isSplitSubtorus.mono
  exact borelTorusBruhatCovering_parabolicHom_of_oppositeFactorPairs hG hi
    (hP.polarization_rho_isGeneric b hspan) (hE k G hG T j hi)

end IsRootDatumOf

namespace IsRootDatumOf

open AffineCoordinates MatrixRepresentation

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    {J : Type u} [Fintype J]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} [P.IsReduced]

/-- **Canonical rho big-cell geometric data from opposite root pairs.** Over an algebraically
closed field, for a split maximal torus `j` of a connected reductive group with reduced root
datum `P`, base `b` and integral coroot span, a matrix representation `ρ` on which the
polarized rho cocharacter acts diagonally with exponents `e`, with a strictly minimal
exponent at `a` whose torus weight is `-rho`, gives the six geometric laws of the Steinberg
big cell. The witnesses are those of `IsRootDatumOf.canonicalRhoBigCellGeometricData`. Its
Bruhat-covering input comes from `AlgClosedOppositeFactorPairsStatement`. -/
def oppositePairBigCellGeometricData [IsAlgClosed k]
    (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (e : n → ℤ)
    (hν : (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j) ≫ ρ =
        GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
    (a : n) (ha : ∀ c, c ≠ a → e a < e c)
    (hweight : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      (ρ.pointMatrix V (t ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) a a =
        (characterEval ((rationalCharacters.equivCharacterLattice T).symm
          (-IntegralWeylVector.rho P b hspan)) V t : Γ(V.left, ⊤)))
    (hE : AlgClosedOppositeFactorPairsStatement.{u}) :
    SteinbergBigCellGeometricData G :=
  hP.canonicalRhoBigCellGeometricData b hspan hG hT hj ρ e hν a ha hweight
    (hP.borelTorusBruhatCovering_polarization_rho_of_statement b hspan hG hT hj hE)

end IsRootDatumOf

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- **Highest-weight big-cell geometric data from opposite root pairs.** For a split pinning
over an algebraically closed field with integral coroot span, a representation of highest
weight rho gives the six geometric laws of the Steinberg big cell. The witnesses are those of
`SplitPinning.highestWeightBigCellGeometricData`. Its Bruhat-covering input comes from
`AlgClosedOppositeFactorPairsStatement`. -/
def oppositePairHighestWeightBigCellGeometricData [IsAlgClosed k]
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ (IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hE : AlgClosedOppositeFactorPairsStatement.{u}) :
    SteinbergBigCellGeometricData G :=
  p.highestWeightBigCellGeometricData hspan ρ hρ
    (p.isRootDatum.borelTorusBruhatCovering_polarization_rho_of_statement p.base hspan
      p.isConnectedReductive p.isSplitTorus p.isMaximalTorus hE)

/-- The opposite-pair data is the Library highest-weight assembly with the covering filled in,
so all of its witness lemmas apply. -/
theorem oppositePairHighestWeightBigCellGeometricData_eq [IsAlgClosed k]
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ (IntegralWeylVector.rho p.rootDatum p.base hspan))
    (hE : AlgClosedOppositeFactorPairsStatement.{u}) :
    p.oppositePairHighestWeightBigCellGeometricData hspan ρ hρ hE =
      p.highestWeightBigCellGeometricData hspan ρ hρ
        (p.isRootDatum.borelTorusBruhatCovering_polarization_rho_of_statement p.base hspan
          p.isConnectedReductive p.isSplitTorus p.isMaximalTorus hE) := rfl

end SplitPinning

end Langlands.GroupScheme
