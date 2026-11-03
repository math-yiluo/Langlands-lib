import Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions

/-! # Integer monomials and basis independence of scalar orbit smoothness -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal ContDiff CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- An integer matrix induces a finite product of circle Laurent monomials. -/
def finiteTorusMonomial {J K : Type*} [Fintype K]
    (a : J → K → ℤ) (z : K → Circle) : J → Circle :=
  fun j => ∏ k, z k ^ a j k

/-- The real linear map whose exponential is the integer torus monomial. -/
def finiteTorusMonomialLift {J K : Type*} [Fintype K]
    (a : J → K → ℤ) (x : K → ℝ) : J → ℝ :=
  fun j => ∑ k, (a j k : ℝ) * x k

@[simp]
theorem finiteTorusExp_monomialLift {J K : Type*} [Fintype K]
    (a : J → K → ℤ) (x : K → ℝ) :
    finiteTorusExp (finiteTorusMonomialLift a x) =
      finiteTorusMonomial a (finiteTorusExp x) := by
  funext j
  change (Circle.expHom (∑ k, (a j k : ℝ) * x k)).toMul = _
  rw [map_sum, toMul_sum]
  change (∏ k, Circle.exp ((a j k : ℝ) * x k)) = _
  simp [Circle.exp_intCast_mul, finiteTorusMonomial, finiteTorusExp]

theorem contDiff_finiteTorusMonomialLift {J K : Type*} [Fintype J] [Fintype K]
    (a : J → K → ℤ) : ContDiff ℝ ∞ (finiteTorusMonomialLift a) := by
  apply contDiff_pi.mpr
  intro j
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply ℝ ℝ k)

/-- Precomposition by any integer torus monomial preserves scalar smoothness. -/
theorem IsSmoothFiniteTorusFunction.comp_monomial {J K : Type*} [Fintype J] [Fintype K]
    {f : (J → Circle) → ℂ} (hf : IsSmoothFiniteTorusFunction f)
    (a : J → K → ℤ) : IsSmoothFiniteTorusFunction (f ∘ finiteTorusMonomial a) := by
  have hh := hf.comp (contDiff_finiteTorusMonomialLift a)
  simpa only [IsSmoothFiniteTorusFunction, Function.comp_def,
    finiteTorusExp_monomialLift] using hh

/-- Change the values specifying a lattice character from one integer basis to
another by reconstructing that same character. -/
def finiteTorusBasisChange {L J K : Type*} [AddCommGroup L] [Module ℤ L]
    [Fintype J] (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L)
    (z : J → Circle) : K → Circle :=
  fun k => (b.constr ℤ (fun j => Additive.ofMul (z j)) (c k)).toMul

theorem finiteTorusBasisChange_eq_monomial {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L) :
    finiteTorusBasisChange b c = finiteTorusMonomial (fun k j => b.repr (c k) j) := by
  funext z k
  dsimp [finiteTorusBasisChange, finiteTorusMonomial]
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul]
  rfl

/-- Reconstruction in the target basis gives the same lattice character. -/
theorem finiteTorusBasisChange_constr {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J] [Fintype K]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L) (z : J → Circle) :
    c.constr ℤ (fun k => Additive.ofMul (finiteTorusBasisChange b c z k)) =
      b.constr ℤ (fun j => Additive.ofMul (z j)) := by
  apply c.ext
  intro k
  rw [Module.Basis.constr_basis]
  rfl

@[simp]
theorem finiteTorusBasisChange_inverse {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J] [Fintype K]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L) (z : J → Circle) :
    finiteTorusBasisChange c b (finiteTorusBasisChange b c z) = z := by
  funext j
  change (c.constr ℤ (fun k => Additive.ofMul (finiteTorusBasisChange b c z k)) (b j)).toMul = _
  rw [finiteTorusBasisChange_constr, Module.Basis.constr_basis]
  rfl

theorem continuous_finiteTorusBasisChange {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L) :
    Continuous (finiteTorusBasisChange b c) := by
  rw [finiteTorusBasisChange_eq_monomial]
  apply continuous_pi
  intro k
  exact continuous_finsetProd _ fun j _ => (continuous_apply j).zpow _

/-- Replacing a finite integer basis gives a homeomorphism of its coordinate
tori, whose inverse reconstructs in the other direction. -/
def finiteTorusBasisChangeHomeomorph {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J] [Fintype K]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L) :
    (J → Circle) ≃ₜ (K → Circle) where
  toFun := finiteTorusBasisChange b c
  invFun := finiteTorusBasisChange c b
  left_inv := finiteTorusBasisChange_inverse b c
  right_inv := finiteTorusBasisChange_inverse c b
  continuous_toFun := continuous_finiteTorusBasisChange b c
  continuous_invFun := continuous_finiteTorusBasisChange c b

/-- Scalar smoothness is independent of a finite integer basis of the lattice. -/
theorem isSmoothFiniteTorusFunction_basisChange_iff {L J K : Type*}
    [AddCommGroup L] [Module ℤ L] [Fintype J] [Fintype K]
    (b : Module.Basis J ℤ L) (c : Module.Basis K ℤ L)
    (f : (K → Circle) → ℂ) :
    IsSmoothFiniteTorusFunction (f ∘ finiteTorusBasisChange b c) ↔
      IsSmoothFiniteTorusFunction f := by
  constructor
  · intro h
    have hh := h.comp_monomial (fun j k => c.repr (b j) k)
    rw [← finiteTorusBasisChange_eq_monomial c b] at hh
    simpa only [Function.comp_def, finiteTorusBasisChange_inverse] using hh
  · intro h
    rw [finiteTorusBasisChange_eq_monomial]
    exact h.comp_monomial _

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalOrbitBasisGroupPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalOrbitBasisNonarchimedeanGroup :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

/-- Reconstruct the actual unitary unramified character from its values on any
finite integer basis of the actual valuation image. -/
def rationalUnitaryUnramifiedCharacterOfBasis (hG : GroupScheme.IsConnectedReductive G)
    {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G)))
    (z : J → Circle) :
    unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul) :=
  (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm
    (finiteTorusBasisChange b (rationalReductiveValuationBasis G hG) z)

omit [LocallyOfFiniteType G.X.hom] in
/-- Evaluation at an actual rational point is the Laurent monomial given by
that point's valuation coordinates in the supplied basis. -/
theorem rationalUnitaryUnramifiedCharacterOfBasis_apply
    (hG : GroupScheme.IsConnectedReductive G) {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G)))
    (z : J → Circle) (g : GroupScheme.rationalPoints G) :
    (((rationalUnitaryUnramifiedCharacterOfBasis hG b z).val g : ℂˣ) : ℂ) =
      ((∏ j, z j ^ (b.repr (Additive.ofMul (rationalValuationImageProjection G g)) j)
        : Circle) : ℂ) := by
  let _ := (GroupScheme.rationalCharacterLattice F G hG).2
  change (((((rationalReductiveValuationBasis G hG).constr ℤ
    (fun i => Additive.ofMul
      (finiteTorusBasisChange b (rationalReductiveValuationBasis G hG) z i)))
        (Additive.ofMul (rationalValuationImageProjection G g))).toMul : Circle) : ℂ) = _
  rw [finiteTorusBasisChange_constr, Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul]
  rfl

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
variable (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : MeasureTheory.Measure
  (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
variable (hG : GroupScheme.IsConnectedReductive G)

/-- The actual orbit parameter map reconstructed from a supplied image basis. -/
def rationalDiscreteSeriesOrbitCoordinateMapOfBasis
    {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (J → Circle) →
        discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
          (fun psi => (rationalNormCharacters G psi).toMul) omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega ∘
    finiteTorusBasisChange b (rationalReductiveValuationBasis G hG)

@[simp]
theorem rationalDiscreteSeriesOrbitCoordinateMapOfBasis_val
    {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (z : J → Circle),
      (rationalDiscreteSeriesOrbitCoordinateMapOfBasis s hs mu hG b omega z).val =
        rationalUnitaryUnramifiedCharacterOfBasis hG b z • omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intros
  rfl

theorem isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMapOfBasis
    {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      IsOpenQuotientMap (rationalDiscreteSeriesOrbitCoordinateMapOfBasis s hs mu hG b omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega
  exact (isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega).comp
    (finiteTorusBasisChangeHomeomorph b
      (rationalReductiveValuationBasis G hG)).isOpenQuotientMap

/-- Scalar smoothness tested in any finite image basis agrees with the existing
actual-orbit smoothness predicate. -/
theorem isSmoothRationalOrbitFunction_basis_iff
    {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ (Additive (rationalDiscreteValuationImage G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ),
      IsSmoothFiniteTorusFunction
        (f ∘ rationalDiscreteSeriesOrbitCoordinateMapOfBasis s hs mu hG b omega) ↔
      IsSmoothRationalOrbitFunction s hs mu hG omega f := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega f
  exact isSmoothFiniteTorusFunction_basisChange_iff b
    (rationalReductiveValuationBasis G hG)
    (f ∘ rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega)

end Langlands.Plancherel
