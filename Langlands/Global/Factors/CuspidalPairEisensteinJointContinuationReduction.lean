import Langlands.Global.Factors.CuspidalPairEisensteinLineContinuation
import Langlands.Global.Factors.CuspidalPairSquareIntegrableTwistStatement
import Langlands.Global.Factors.CuspidalPairEisensteinJointContinuationStatement
import Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement

/-! # The joint continuation of the cuspidal-pair Eisenstein series at universe 0

The meromorphic continuation of Eisenstein series, its joint root-hyperplane form, Lapid's
holomorphy on the imaginary axis and the square-integrable imaginary twist of cuspidal-pair
sections imply `CuspidalPairEisensteinJointContinuationStatement` for number fields in `Type`.
The imaginary-axis statement and square integrability are stated for number fields in `Type`
only, so the reduction is at universe `0`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions PrimitiveAdelicHeight

local instance jointRedGLAffine {F : Type} [Field F] (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance jointRedGLAffineHom {F : Type} [Field F] (n : ℕ) :
    IsAffineHom (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := CommRingCat.of F)

local instance jointRedGLFiniteType {F : Type} [Field F] [NumberField F] (n : ℕ) :
    LocallyOfFiniteType (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin n)).smooth
  inferInstance

local instance jointRedParabolicAffine {F : Type} [Field F] {r t : ℕ} :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance jointRedParabolicClosed {F : Type} [Field F] {r t : ℕ} :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

local instance jointRedLeviAffine {F : Type} [Field F] {r t : ℕ} :
    IsAffine (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  have : IsAffineHom (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.hom :=
    (isClosedSubgroup_blockLeviHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).isAffineHom
  isAffine_of_isAffineHom (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))).X.hom

local instance jointRedLeviFiniteType {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    LocallyOfFiniteType (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType
    (isClosedSubgroup_blockLeviHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t)))

local instance jointRedTorusMono {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    Mono (blockRootData F (blockShape r t)).root.data.i.hom.hom.left :=
  (blockRootData F (blockShape r t)).torus_mono

local instance jointRedFactorMono {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    Mono (CommGroupScheme.groupHom (blockRootData F (blockShape r t)).root.data.f).hom.hom.left :=
  (blockRootData F (blockShape r t)).factor_mono

local instance jointRedWeylFinite {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    Fintype (relativeWeylGroup (blockRootData F (blockShape r t)).root.data.i) :=
  @Fintype.ofFinite _ (blockRootData F (blockShape r t)).finite_weylGroup

/-- The meromorphic continuation of Eisenstein series
(`EisensteinMeromorphicContinuationStatement`) and its joint root-hyperplane form
(`EisensteinJointRootHyperplaneStatement`) for number fields in `Type`, Lapid's holomorphy on the
imaginary axis (`EisensteinImaginaryAxisHolomorphyStatement`) and the square-integrable imaginary
twist of cuspidal-pair sections (`CuspidalPairSquareIntegrableTwistStatement`) imply
`CuspidalPairEisensteinJointContinuationStatement` for number fields in `Type`. -/
def CuspidalPairEisensteinJointContinuationReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinJointRootHyperplaneStatement.{0} →
    EisensteinImaginaryAxisHolomorphyStatement → CuspidalPairSquareIntegrableTwistStatement →
      CuspidalPairEisensteinJointContinuationStatement.{0}

theorem cuspidalPairEisensteinJointContinuationReduction :
    CuspidalPairEisensteinJointContinuationReductionStatement := by
  intro hMero hJoint hHolo hSq F _ _ _ r t T T' hT hT' φ hφ
  obtain ⟨E, σ, h1, h2⟩ := cuspidalPairEisensteinLineReduction.{0} hMero hJoint F r t T T' φ hφ
  have hIm : EisensteinLine.HasImaginaryAxisHolomorphy (blockRootData F (blockShape r t)).root
      (blockRootData F (blockShape r t)).splitComponent
      (blockRootData F (blockShape r t)).splitTorus
      (isIwasawaCompact_blockParabolic F (blockShape r t))
      (φ ∘ adelicHomeomorph F (r + t + 2)) := by
    obtain ⟨y, ψ, hφψ, hψ⟩ := hSq F r t T T' hT hT' φ hφ
    refine EisensteinLine.hasImaginaryAxisHolomorphy_of_eq_mul_heightPower _ _ _ _ y hφψ ?_
    have hG := isConnectedReductive_generalLinear F (Fin (r + t + 2))
    have hs := hG.smoothDimension_spec
    have hc := adelicDifferentialCommutator_of_smooth F
      (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hs
    have hrho : IsClosedSubgroup (MatrixRepresentation.standard (Fin (r + t + 2))
        (CommRingCat.of F)) := by
      change IsClosedImmersion (𝟙 (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.left)
      infer_instance
    intro E' D hE' hER
    -- the one application of the imaginary-axis statement, for `F : Type`
    exact hHolo F _ _ _ _ _ _ _ _ _ (blockRootData F (blockShape r t)).root
      (blockRootData F (blockShape r t)).splitComponent
      (blockRootData F (blockShape r t)).splitTorus hG
      (blockUnipotentInclusion_isLeviGeometricUnipotentRadical F (blockShape r t))
      (standardCompactPoints F (r + t + 2)) (isIwasawaCompact_blockParabolic F (blockShape r t))
      (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F)) hs hc ψ
      (standardCompactPoints_isMaximalCompact F (r + t + 2)) hrho (hψ hs hc) E' D hE' hER
  refine ⟨E, σ, h1, fun s₀ => ?_⟩
  obtain ⟨m, W, h, hW, hs₀, hcont, hd, hinv, heq, him⟩ := h2 s₀
  exact ⟨m, W, h, hW, hs₀, hcont, hd, hinv, heq, him hIm⟩

end Langlands.Global.CuspidalPairEisenstein
