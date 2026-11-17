import Langlands.GroupScheme.Reductive.SuppliedRhoCofinalIrreducibility
import Langlands.GroupScheme.Reductive.HighestWeightBigCell

/-! # All seven Steinberg laws from supplied full roots and a clean Bruhat cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (c : p.SimpleRootCoordinateFamily) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ρ₀" => IntegralWeylVector.rho p.rootDatum p.base hspan
local notation "ν₀" => p.rootDatum.Polarization ρ₀
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

attribute [local irreducible] RootPairing.Polarization

local instance suppliedRootBigCellTorusClosed :
    IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

local instance suppliedRootBigCellReduced : p.rootDatum.IsReduced := p.isReduced

local instance suppliedRootBigCellIsAffine
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance suppliedRootBigCellParabolicIsAffineHom :
    IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

variable (q : ℕ) [ExpChar k q] (hq : q.Prime)
    (hcover : BorelTorusBruhatCovering
      (k := k) (G := G)
      (B := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion))
      (T := p.torus)
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion)) p.inclusion)

/-- Supplied full simple-root coordinates and a supplied actual Bruhat cover
produce all seven laws with the same witnesses. No structural existence is asserted. -/
def suppliedRootSteinbergBigCellData : SteinbergBigCellData G := by
  have hw : ∃ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)), p.IsHighestWeight ρ ρ₀ :=
    splitDominantHighestWeightRepresentationsExist k G p ρ₀
      (p.isDominantWeight_rho hspan)
  let m : ℕ := Classical.choose hw
  let ρ : MatrixRepresentation G (Fin m) := Classical.choose (Classical.choose_spec hw)
  have hρ : p.IsHighestWeight ρ ρ₀ := Classical.choose_spec (Classical.choose_spec hw)
  let D : SteinbergBigCellGeometricData G :=
    p.highestWeightBigCellGeometricData hspan ρ hρ hcover
  exact D.withIrreduciblePowers (p.suppliedRho_irreduciblePowers c hspan q hq)

/-- The assembled subgroup map is the original polarized-rho dynamic subgroup inclusion. -/
theorem suppliedRootSteinbergBigCellData_i :
    (p.suppliedRootSteinbergBigCellData c hspan q hq hcover).i =
      Dynamic.Affine.parabolicHom λ₀ := rfl

/-- The cofinal law uses the original negative-rho coordinate. -/
theorem suppliedRootSteinbergBigCellData_χ :
    (p.suppliedRootSteinbergBigCellData c hspan q hq hcover).χ = χ₀ := rfl

/-- The assembled diagonalizable subgroup is the supplied split torus model. -/
theorem suppliedRootSteinbergBigCellData_j :
    (p.suppliedRootSteinbergBigCellData c hspan q hq hcover).j =
      p.isSplitTorus.diagonalizableModel.embedding p.inclusion := rfl

/-- The assembled conjugating point is the supplied root datum's opposition representative. -/
theorem suppliedRootSteinbergBigCellData_n :
    (p.suppliedRootSteinbergBigCellData c hspan q hq hcover).n =
      (p.isRootDatum.oppositionRepresentative p.base hspan).val := rfl

end Langlands.GroupScheme.SplitPinning
