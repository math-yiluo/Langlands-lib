import Langlands.GroupScheme.Reductive.HighestWeightExtremal
import Langlands.GroupScheme.Reductive.CanonicalRhoBigCell

/-! # Canonical big-cell data from a supplied highest-weight representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme.Dynamic
open scoped CategoryTheory.MonObj Matrix

set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

omit [Fintype p.rootIndex] in
/-- The integral rho character is dominant for the supplied pinning. -/
theorem isDominantWeight_rho :
    p.IsDominantWeight (IntegralWeylVector.rho p.rootDatum p.base hspan) := by
  intro a
  rw [IntegralWeylVector.pairing_rho_simple]
  exact zero_le_one

local instance highestWeightBigCellIsReduced : p.rootDatum.IsReduced := p.isReduced
local instance highestWeightBigCellIsClosedImmersion : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

local notation "ν₀" =>
  p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

local instance highestWeightBigCellIsAffine {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

attribute [local irreducible] RootPairing.Polarization

local instance highestWeightBigCellIsAffineHom : IsAffineHom (Affine.parabolicScheme λ₀).X.hom := by
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
    (hcover : BorelTorusBruhatCovering
      (k := k) (G := G)
      (B := Affine.parabolicScheme (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion))
      (T := p.torus)
      (Affine.parabolicHom (CommGroupScheme.groupHom
        (p.rootDatum.Polarization (IntegralWeylVector.rho p.rootDatum p.base hspan)) ≫
          p.inclusion)) p.inclusion)

/-- A supplied highest weight at rho constructs the actual canonical witnesses
and all six geometric laws. Structural and Bruhat existence remain explicit. -/
def highestWeightBigCellGeometricData : SteinbergBigCellGeometricData G := by
  let E := p.negativeRhoExtremalRepresentationData hspan ρ hρ
  exact p.isRootDatum.canonicalRhoBigCellGeometricData p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus
    E.representation E.exponents E.cocharacter_eq E.index E.isMinimum E.weight hcover

/-- The diagonalizable subgroup presents the original supplied maximal torus. -/
theorem highestWeightBigCellGeometricData_j :
    (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).j =
      p.isSplitTorus.diagonalizableModel.embedding p.inclusion := rfl

/-- The subgroup map is the actual canonical polarized-rho parabolic map. -/
theorem highestWeightBigCellGeometricData_i :
    (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).i =
      Affine.parabolicHom λ₀ := rfl

/-- The opposition point is the one constructed from the supplied root datum. -/
theorem highestWeightBigCellGeometricData_n :
    (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).n =
      (p.isRootDatum.oppositionRepresentative p.base hspan).val := rfl

/-- The weight coordinate is independent of the chosen highest-weight module. -/
theorem highestWeightBigCellGeometricData_χ :
    (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).χ = χ₀ := rfl

/-- The group coordinate is the distinguished coefficient of the actual
conjugated-dual representation supplied by the extremal adapter. -/
theorem highestWeightBigCellGeometricData_d :
    (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).d =
      AffineCoordinates.diagonalMatrixCoefficient
        (p.negativeRhoExtremalRepresentationData hspan ρ hρ).representation
        (p.negativeRhoExtremalRepresentationData hspan ρ hρ).index := rfl

/-- The exact entire-space seventh law on the canonical parabolic upgrades the
same geometric witnesses to the complete Steinberg big-cell data. -/
def highestWeightBigCellData
    (hirr : ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace (Affine.parabolicHom λ₀) (χ₀ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
          (Affine.parabolicHom λ₀) (χ₀ ^ e') f hv)).rationalRepresentation.IsIrreducible) :
    SteinbergBigCellData G :=
  (p.highestWeightBigCellGeometricData hspan ρ hρ hcover).withIrreduciblePowers hirr

/-- If dominant highest-weight existence is supplied explicitly, its specialization
at rho constructs the six-law data without a separately chosen representation. -/
def highestWeightBigCellGeometricDataOfDominantExistence
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u}) :
    SteinbergBigCellGeometricData G :=
  Classical.choice (by
    obtain ⟨m, σ, hσ⟩ := hex k G p (IntegralWeylVector.rho p.rootDatum p.base hspan)
      (p.isDominantWeight_rho hspan)
    exact ⟨p.highestWeightBigCellGeometricData hspan σ hσ hcover⟩)

end Langlands.GroupScheme.SplitPinning
