import Langlands.GroupScheme.Reductive.SuppliedRhoHeightIrreducibility
import Langlands.GroupScheme.Rational.DominantHighestWeightProof

/-! # Cofinal whole-space Steinberg irreducibility from supplied root coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (c : p.SimpleRootCoordinateFamily) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ρ₀" => IntegralWeylVector.rho p.rootDatum p.base hspan
local notation "ν₀" => p.rootDatum.Polarization ρ₀
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion
local notation "iP" => Dynamic.Affine.parabolicHom λ₀
local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

local instance suppliedCofinalIsAffine
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance suppliedCofinalParabolicIsAffineHom :
    IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

/-- A finite standard-indexed basis of the entire covariant space, obtained
from supplied-family same-height detection. -/
def suppliedRhoSteinbergBasis (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.Basis
      (Fin (Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)))) k
      (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) := by
  letI := p.finite_suppliedRhoCovariantSubspace c hspan q r
  exact Module.finBasis k _

include c in
/-- The supplied full simple-root family gives exactly the cofinal seventh
law for the entire canonical covariant space, with no representation-existence
or irreducibility assumption. -/
theorem suppliedRho_irreduciblePowers (q : ℕ) [ExpChar k q] (hq : q.Prime) :
    ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace iP (χ₀ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
          iP (χ₀ ^ e') f hv)).rationalRepresentation.IsIrreducible := by
  intro e
  obtain ⟨r, hr, he⟩ := exists_pos_steinbergHeight q hq e
  obtain ⟨n, ρ, hρ⟩ := p.exists_highestWeight_nsmul_rho hspan
    splitDominantHighestWeightRepresentationsExist (q ^ r - 1)
  exact ⟨q ^ r - 1, he,
    Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)),
    p.suppliedRhoSteinbergBasis c hspan q r,
    p.suppliedRhoSteinbergHeightIrreducibility c hspan q r hr ρ hρ
      (p.suppliedRhoSteinbergBasis c hspan q r)⟩

end Langlands.GroupScheme.SplitPinning
