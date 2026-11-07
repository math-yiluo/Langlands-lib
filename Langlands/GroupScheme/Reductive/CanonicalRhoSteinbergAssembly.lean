import Langlands.GroupScheme.Reductive.CanonicalRhoBorelBigCell
import Langlands.GroupScheme.Reductive.CanonicalRhoFrobeniusDetection

/-! # Cofinal Steinberg powers and canonical big-cell assembly -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

/-- Positive heights with Steinberg exponent at least a prescribed natural number
exist for every prime base. -/
theorem exists_pos_steinbergHeight (q : ℕ) (hq : q.Prime) (e : ℕ) :
    ∃ r : ℕ, 0 < r ∧ e ≤ q ^ r - 1 := by
  refine ⟨e + 1, by omega, ?_⟩
  have hpow : e + 1 < q ^ (e + 1) := Nat.lt_pow_self hq.one_lt
  omega

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ρ₀" => IntegralWeylVector.rho p.rootDatum p.base hspan
local notation "ν₀" => p.rootDatum.Polarization ρ₀
local notation "λ₀" => CommGroupScheme.groupHom ν₀ ≫ p.inclusion

local instance assemblyIsAffine
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local instance assemblyParabolicIsAffineHom :
    IsAffineHom (Dynamic.Affine.parabolicScheme λ₀).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

local notation "iP" => Dynamic.Affine.parabolicHom λ₀
local notation "χ₀" => Dynamic.negativeRhoCoordinate
  (Dynamic.Affine.isRepresentedBy_parabolicHom λ₀)
  (p.isRootDatum.isRepresentedBy_centralizer_polarization_rho p.base hspan
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus)
  p.rootDatum p.base hspan

omit [Fintype p.rootIndex] in
/-- Every natural multiple of integral rho is dominant for the same base. -/
theorem isDominantWeight_nsmul_rho (m : ℕ) :
    p.IsDominantWeight (m • ρ₀) := by
  intro a
  rw [map_nsmul, LinearMap.smul_apply, IntegralWeylVector.pairing_rho_simple]
  simp

variable [IsAlgClosed k]

omit [Fintype p.rootIndex] in
/-- Supplied dominant highest-weight existence specializes to every natural
multiple of integral rho, including each Steinberg exponent. -/
theorem exists_highestWeight_nsmul_rho
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u}) (m : ℕ) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), p.IsHighestWeight ρ (m • ρ₀) :=
  hex k G p (m • ρ₀) (p.isDominantWeight_nsmul_rho hspan m)

/-- The full canonical covariant space at height r has a finite standard-indexed
basis, by injective restriction to the same-height Frobenius quotient. -/
def canonicalRhoSteinbergBasis (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.Basis
      (Fin (Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)))) k
      (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) := by
  letI := p.finite_canonicalRhoCovariantSubspace hspan q r
  exact Module.finBasis k _

/-- The remaining per-height input: a supplied highest-weight module at a
positive Steinberg height makes the entire canonical covariant space
irreducible in every finite basis. This definition asserts no existence. -/
def CanonicalRhoSteinbergHeightIrreducibility (q : ℕ) : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ {n : ℕ} (ρ : MatrixRepresentation G (Fin n)),
      p.IsHighestWeight ρ ((q ^ r - 1) • ρ₀) →
        ∀ {m : ℕ}
          (bX : Module.Basis (Fin m) k
            (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1))),
          (Chevalley.affineRegularRepresentation G _ bX
            (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
              iP (χ₀ ^ (q ^ r - 1)) f hv)).rationalRepresentation.IsIrreducible

/-- Positive-height irreducibility, supplied highest-weight existence and actual
finite dimensionality give exactly the cofinal whole-space seventh law. -/
theorem canonicalRho_irreduciblePowers_of_heightIrreducibility
    (q : ℕ) [ExpChar k q] (hq : q.Prime)
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u})
    (hheight : p.CanonicalRhoSteinbergHeightIrreducibility hspan q) :
    ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Module.Basis (Fin m) k
        (AffineCoordinates.leftCovariantSubspace iP (χ₀ ^ e'))),
      (Chevalley.affineRegularRepresentation G _ bX
        (fun f _ hv => AffineCoordinates.rightAct_mem_leftCovariantSubspace
          iP (χ₀ ^ e') f hv)).rationalRepresentation.IsIrreducible := by
  intro e
  obtain ⟨r, hr, he⟩ := exists_pos_steinbergHeight q hq e
  obtain ⟨n, ρ, hρ⟩ := p.exists_highestWeight_nsmul_rho hspan hex (q ^ r - 1)
  exact ⟨q ^ r - 1, he,
    Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)),
    p.canonicalRhoSteinbergBasis hspan q r,
    hheight r hr ρ hρ (p.canonicalRhoSteinbergBasis hspan q r)⟩

/-- Conditional complete canonical data: supplied dominant highest-weight
existence and the explicit per-height input fill the seventh law of the
constructed rho Borel big cell. The pinning and coroot span remain supplied. -/
def canonicalRhoSteinbergBigCellData
    (q : ℕ) [ExpChar k q] (hq : q.Prime)
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u})
    (hheight : p.CanonicalRhoSteinbergHeightIrreducibility hspan q) :
    SteinbergBigCellData G := by
  let hw := hex k G p ρ₀ (by simpa using p.isDominantWeight_nsmul_rho hspan 1)
  let ρ := Classical.choose (Classical.choose_spec hw)
  let hρ := Classical.choose_spec (Classical.choose_spec hw)
  exact p.canonicalRhoBorelBigCellData hspan ρ hρ
    (p.canonicalRho_irreduciblePowers_of_heightIrreducibility hspan q hq hex hheight)

/-- Assembly preserves the actual canonical parabolic inclusion. -/
theorem canonicalRhoSteinbergBigCellData_i
    (q : ℕ) [ExpChar k q] (hq : q.Prime)
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u})
    (hheight : p.CanonicalRhoSteinbergHeightIrreducibility hspan q) :
    (p.canonicalRhoSteinbergBigCellData hspan q hq hex hheight).i = iP := rfl

/-- Assembly preserves the canonical negative-rho weight coordinate. -/
theorem canonicalRhoSteinbergBigCellData_χ
    (q : ℕ) [ExpChar k q] (hq : q.Prime)
    (hex : SplitDominantHighestWeightRepresentationsExistStatement.{u})
    (hheight : p.CanonicalRhoSteinbergHeightIrreducibility hspan q) :
    (p.canonicalRhoSteinbergBigCellData hspan q hq hex hheight).χ = χ₀ := rfl

end SplitPinning

end Langlands.GroupScheme
