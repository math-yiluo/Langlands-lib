import Langlands.Representation.Plancherel.RationalImaginaryParameters
import Langlands.Representation.Plancherel.RationalUnramifiedComplexChart

/-! # Basis coordinates and the imaginary exponential on unitary unramified characters -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (Additive (rationalDiscreteValuationImage G)))

/-- Restrict the published basis coordinates to the unitary subgroup. -/
def rationalUnitaryUnramifiedBasisCoordinateHom : Xu →* (Fin n → ℂ) where
  toFun χ := rationalUnramifiedBasisCoordinates G b (rationalUnitaryUnramifiedInclusion G χ)
  map_one' := by
    funext i
    obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (b i).toMul
    rw [rationalUnramifiedBasisCoordinates_apply G b _ i g hg]
    simp
  map_mul' χ₁ χ₂ := by
    funext i
    obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (b i).toMul
    simp only [Pi.mul_apply, rationalUnramifiedBasisCoordinates_apply G b _ i g hg,
      rationalUnitaryUnramifiedInclusion_val, Subgroup.coe_mul, ContinuousMonoidHom.mul_apply,
      Units.val_mul]

/-- The restricted coordinates have norm one at each basis vector. -/
theorem rationalUnitaryUnramifiedBasisCoordinateHom_norm (χ : Xu) (i : Fin n) :
    ‖rationalUnitaryUnramifiedBasisCoordinateHom G b χ i‖ = 1 := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (b i).toMul
  change ‖rationalUnramifiedBasisCoordinates G b (rationalUnitaryUnramifiedInclusion G χ) i‖ = 1
  rw [rationalUnramifiedBasisCoordinates_apply G b _ i g hg, rationalUnitaryUnramifiedInclusion_val]
  exact χ.property.2 g

omit [LocallyOfFiniteType G.X.hom] in
/-- The inclusion into all unramified characters preserves the subspace topology. -/
theorem isEmbedding_rationalUnitaryUnramifiedInclusion :
    IsEmbedding (rationalUnitaryUnramifiedInclusion G) :=
  IsEmbedding.inclusion inf_le_left

/-- The unitary basis coordinates are a topological embedding. -/
theorem isEmbedding_rationalUnitaryUnramifiedBasisCoordinateHom :
    IsEmbedding (rationalUnitaryUnramifiedBasisCoordinateHom G b) :=
  (isOpenEmbedding_rationalUnramifiedBasisCoordinates G b).isEmbedding.comp
    (isEmbedding_rationalUnitaryUnramifiedInclusion G)

private def imaginaryBasisParameter (t : Fin n → ℝ) : rationalImageImaginaryParameters G :=
  ⟨(b.constr ℤ (fun i => (t i : ℂ) * Complex.I)).toAddMonoidHom, by
    let realPart := Complex.reLm.restrictScalars ℤ
    have h : realPart.comp (b.constr ℤ (fun i => (t i : ℂ) * Complex.I)) = 0 := by
      apply b.ext
      intro i
      rw [LinearMap.comp_apply, Module.Basis.constr_basis]
      simp [realPart, Complex.mul_re]
    intro a
    exact DFunLike.congr_fun h a⟩

/-- Exponentiate the imaginary additive functional with basis values `t i * I`. -/
def rationalUnitaryBasisExponential (t : Fin n → ℝ) : Xu :=
  rationalCanonicalImaginaryUnramifiedCharacter G (imaginaryBasisParameter G b t)

/-- The unitary lift is the published complex exponential after inclusion. -/
theorem rationalUnitaryBasisExponential_inclusion (t : Fin n → ℝ) :
    rationalUnitaryUnramifiedInclusion G (rationalUnitaryBasisExponential G b t) =
      rationalCanonicalUnramifiedComplexExponential G
        (Multiplicative.ofAdd (b.constr ℤ (fun i => (t i : ℂ) * Complex.I)).toAddMonoidHom) := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  change ((rationalCanonicalImaginaryUnramifiedCharacter G
    (imaginaryBasisParameter G b t)).val g : ℂ) = _
  rw [rationalCanonicalImaginaryUnramifiedCharacter_val,
    rationalCanonicalUnramifiedComplexExponential_val]
  rfl

/-- The imaginary exponential has the same scalar normalization in every basis coordinate. -/
theorem rationalUnitaryBasisExponential_coordinates (t : Fin n → ℝ) (i : Fin n) :
    rationalUnitaryUnramifiedBasisCoordinateHom G b (rationalUnitaryBasisExponential G b t) i =
      Complex.exp (((-Real.log (LocalField.residueCardinality F : ℝ) * t i : ℝ) : ℂ) *
        Complex.I) := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (b i).toMul
  change rationalUnramifiedBasisCoordinates G b
    (rationalUnitaryUnramifiedInclusion G (rationalUnitaryBasisExponential G b t)) i = _
  rw [rationalUnitaryBasisExponential_inclusion,
    rationalUnramifiedBasisCoordinates_apply G b _ i g hg,
    rationalCanonicalUnramifiedComplexExponential_val, hg]
  change Complex.exp (-(b.constr ℤ (fun j => (t j : ℂ) * Complex.I)) (b i) *
    (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) = _
  rw [Module.Basis.constr_basis, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  ring

/-- The residue cardinality makes the imaginary exponential scale nonzero. -/
theorem rationalImaginaryExponentialScale_ne_zero (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    -Real.log (LocalField.residueCardinality F : ℝ) ≠ 0 :=
  neg_ne_zero.mpr (Real.log_pos (by exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'

end Langlands.Plancherel
