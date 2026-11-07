import Langlands.GroupScheme.Reductive.HighestWeightExtremal
import Langlands.GroupScheme.Reductive.CanonicalRhoBigCell
import Langlands.GroupScheme.Absolute.BruhatCoveringProof
import Langlands.GroupScheme.Dynamic.ParabolicIntersection

/-! # The canonical rho Borel pair and big-cell geometric data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme.Dynamic
open scoped CategoryTheory.MonObj Matrix

set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

namespace IsRootDatumOf

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    {J : Type u} [Fintype J]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)

local notation "ν₀" => P.Polarization (IntegralWeylVector.rho P b hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ j

attribute [local irreducible] RootPairing.Polarization

include hP hG hT hj

/-- The actual polarized-rho parabolic and the original torus form a Borel pair. -/
theorem isBorelPair_polarization_rho :
    IsBorelPair (Affine.parabolicHom λ₀) j := by
  have hregular : IsRegularCocharacter j ν₀ :=
    hP.polarization_rho_isGeneric b hspan
  refine ⟨(regularCocharacterBorel k G hG T j hT hj).1 ν₀ hregular
    _ _ (Affine.isClosedSubgroup_parabolicHom λ₀)
      (Affine.isRepresentedBy_parabolicHom λ₀), hj, ?_⟩
  exact ⟨_, (Affine.isRepresentedBy_parabolicHom λ₀).liftOfLE_comp j
    (range_le_parabolic_groupHom_comp j ν₀)⟩

/-- Published absolute Bruhat covering specializes to the canonical rho Borel pair. -/
theorem bruhatCovering_polarization_rho [IsAlgClosed k] :
    BorelTorusBruhatCovering (Affine.parabolicHom λ₀) j :=
  absoluteBruhatCovering k G hG _ T _ j
    (hP.isBorelPair_polarization_rho b hspan hG hT hj)

end IsRootDatumOf

namespace SplitPinning

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local instance : p.rootDatum.IsReduced := p.isReduced
local instance : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

local notation "ν₀" =>
  p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

local instance canonicalRhoBorelParabolicIsAffineHom :
    IsAffineHom (Affine.parabolicScheme λ₀).X.hom := by
  let : IsClosedImmersion (Affine.parabolicHom λ₀).hom.hom.left :=
    Affine.isClosedSubgroup_parabolicHom λ₀
  rw [← Over.w (Affine.parabolicHom λ₀).hom.hom]
  infer_instance

local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

variable [IsAlgClosed k]
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ (IntegralWeylVector.rho p.rootDatum p.base hspan))

/-- Construct all six geometric laws from a supplied highest-weight representation
at rho, proving the needed Borel pair and Bruhat covering. -/
def canonicalRhoBorelBigCellGeometricData : SteinbergBigCellGeometricData G := by
  let E := p.negativeRhoExtremalRepresentationData hspan ρ hρ
  exact p.isRootDatum.canonicalRhoBigCellGeometricData p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
    E.representation E.exponents E.cocharacter_eq E.index E.isMinimum E.weight
    (p.isRootDatum.bruhatCovering_polarization_rho p.base hspan
      p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)

/-- The diagonalizable presentation embeds the original supplied maximal torus. -/
theorem canonicalRhoBorelBigCellGeometricData_j :
    (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).j =
      p.isSplitTorus.diagonalizableModel.embedding p.inclusion := rfl

/-- The subgroup is the actual polarized-rho parabolic. -/
theorem canonicalRhoBorelBigCellGeometricData_i :
    (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).i =
      Affine.parabolicHom λ₀ := rfl

/-- The opposition point is the constructed rational normalizer representative. -/
theorem canonicalRhoBorelBigCellGeometricData_n :
    (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).n =
      (p.isRootDatum.oppositionRepresentative p.base hspan).val := rfl

/-- The weight coordinate is the canonical extended negative-rho coordinate. -/
theorem canonicalRhoBorelBigCellGeometricData_χ :
    (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).χ = χ₀ := rfl

/-- The group coordinate is the coefficient of the constructed conjugated dual. -/
theorem canonicalRhoBorelBigCellGeometricData_d :
    (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).d =
      AffineCoordinates.diagonalMatrixCoefficient
        (p.negativeRhoExtremalRepresentationData hspan ρ hρ).representation
        (p.negativeRhoExtremalRepresentationData hspan ρ hρ).index := rfl

/-- The exact whole covariant-space seventh law upgrades the canonical witnesses. -/
def canonicalRhoBorelBigCellData
    (hirr : ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace (Affine.parabolicHom λ₀) (χ₀ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
          (Affine.parabolicHom λ₀) (χ₀ ^ e') f hv)).rationalRepresentation.IsIrreducible) :
    SteinbergBigCellData G :=
  (p.canonicalRhoBorelBigCellGeometricData hspan ρ hρ).withIrreduciblePowers hirr

end SplitPinning

end Langlands.GroupScheme
