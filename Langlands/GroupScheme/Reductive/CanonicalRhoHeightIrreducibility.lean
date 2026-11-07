import Langlands.GroupScheme.Reductive.HighestWeightScalarRhoEigenrow
import Langlands.GroupScheme.Rational.HighestWeightFrobeniusOrbit
import Langlands.GroupScheme.Reductive.CovariantCoefficientExhaustion
import Langlands.GroupScheme.Reductive.CanonicalRhoRootDimension
import Langlands.GroupScheme.Reductive.CanonicalRhoSteinbergAssembly
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Irreducibility of the entire canonical space at a Steinberg height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.SplitPinning

open AffineCoordinates

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ρ₀" => IntegralWeylVector.rho p.rootDatum p.base hspan
local notation "ν₀" => p.rootDatum.Polarization ρ₀
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "iU" => Dynamic.Affine.unipotentHom λ₋
local notation "iP" => Dynamic.Affine.parabolicHom λ₀

local instance heightIsAffine
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance heightParabolicIsAffineHom :
    IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

local instance heightUnipotentIsAffineHom :
    IsAffineHom (Dynamic.Affine.unipotentScheme λ₋).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

variable (q : ℕ) [ExpChar k q] (r : ℕ)
    {n : Type} [Fintype n] [DecidableEq n]

/-- The actual Frobenius orbit at a nonzero highest vector supplies a lower
bound on the entire original coordinate space. -/
theorem highestWeight_finrank_ge_rootCount
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ ((q ^ r - 1) • ρ₀)) :
    (q ^ r) ^ Nat.card {s : p.rootIndex // p.base.IsPos s} ≤
      Module.finrank k (n → k) := by
  have hW : p.representationWeightSpace ρ ((q ^ r - 1) • ρ₀) ≠ ⊥ := by
    intro hz
    have hd := hρ.2.2.1
    rw [hz] at hd
    simp at hd
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hW
  have hle := Submodule.finrank_le
    (MatrixRepresentation.FrobeniusOrderedDistributions.originOrbitSpan
      q r (ρ.restrict iU) v)
  rw [p.highestWeight_finrank_originOrbitSpan hspan ρ q r hρ hv hv0] at hle
  simpa only [Nat.card_eq_fintype_card] using hle

/-- The selected eigen-row coefficients identify the same coordinate space
with the entire canonical covariant space. -/
def canonicalRhoSteinbergCoefficientEquiv
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ ((q ^ r - 1) • ρ₀)) :
    (n → k) ≃ₗ[k] p.canonicalRhoCovariantSubspace hspan (q ^ r - 1) := by
  letI : Smooth G.X.hom := p.isConnectedReductive.smooth
  letI : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  let e := p.scalarRhoEigenrowData hspan ρ (q ^ r - 1) hρ
    hρ.1.rationalRepresentation
  letI : Module.Finite k (leftCovariantSubspace iP (χ₀ ^ (q ^ r - 1))) :=
    p.finite_canonicalRhoCovariantSubspace hspan q r
  exact LinearEquiv.ofBijective
    (covariantCoefficientLinearMap G e.representation (Pi.single e.index 1)
      iP (χ₀ ^ (q ^ r - 1)) e.eigenrow)
    (covariantCoefficientLinearMap_bijective G e.representation (Pi.single e.index 1)
      iP (χ₀ ^ (q ^ r - 1)) e.eigenrow e.isIrreducible e.row_ne_zero
      ((q ^ r) ^ Nat.card {s : p.rootIndex // p.base.IsPos s})
      (p.highestWeight_finrank_ge_rootCount hspan q r ρ hρ)
      (p.finrank_canonicalRhoCovariantSubspace_le_rootCount hspan q r))

/-- Every finite basis of the entire canonical covariant space carries an
irreducible rational right regular representation at this height. -/
theorem canonicalRhoSteinberg_regular_rationalRepresentation_isIrreducible
    (ρ : MatrixRepresentation G n)
    (hρ : p.IsHighestWeight ρ ((q ^ r - 1) • ρ₀))
    {m : ℕ} (b : Module.Basis (Fin m) k
      (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1))) :
    (Chevalley.affineRegularRepresentation G _ b
      (fun f _ hv => rightAct_mem_leftCovariantSubspace
        iP (χ₀ ^ (q ^ r - 1)) f hv)).rationalRepresentation.IsIrreducible := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ G.X.hom
  let e := p.scalarRhoEigenrowData hspan ρ (q ^ r - 1) hρ
    hρ.1.rationalRepresentation
  exact affineRegularRepresentation_rationalRepresentation_isIrreducible_of_coefficient_bounds
    G e.representation (Pi.single e.index 1) iP (χ₀ ^ (q ^ r - 1)) e.eigenrow b
    e.isIrreducible e.row_ne_zero
    ((q ^ r) ^ Nat.card {s : p.rootIndex // p.base.IsPos s})
    (p.highestWeight_finrank_ge_rootCount hspan q r ρ hρ)
    (p.finrank_canonicalRhoCovariantSubspace_le_rootCount hspan q r)

/-- The fixed-height interface used by the cofinal assembly is proved from a
supplied highest-weight module, without a new existence premise. -/
theorem canonicalRhoSteinbergHeightIrreducibility :
    p.CanonicalRhoSteinbergHeightIrreducibility hspan q := by
  intro r _ n ρ hρ m b
  exact p.canonicalRhoSteinberg_regular_rationalRepresentation_isIrreducible
    hspan q r ρ hρ b

end Langlands.GroupScheme.SplitPinning
