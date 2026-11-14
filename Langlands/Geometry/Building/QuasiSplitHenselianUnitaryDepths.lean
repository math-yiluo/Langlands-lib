import Langlands.Geometry.Building.QuasiSplitUnitaryDepthReduction
import Langlands.Geometry.Building.ValuedSU3CoordinateAssembly
import Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceStatement
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof

/-! # Henselian unitary depths from coherent algebraic coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Multipliable

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- The actual integral multiplier bound makes every multipliable root
indivisible within the relative-root set. -/
theorem mem_indivisibleRoots_of_double_mem [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hF : RelativeRoot.HasOppositeFactorPairs i)
    (a : relativeRoots i) (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i) :
    (a : characterLattice S) ∈ RelativeRoot.indivisibleRoots i := by
  refine ⟨a.property, ?_⟩
  intro b _ m hm hba
  have hroot : (2 * m) • b ∈ relativeRoots i := by
    rwa [mul_smul, hba]
  rcases hF.eq_one_or_two_of_nsmul_mem i hS hroot with h | h <;> omega

end Multipliable

namespace AlgebraicSU3RootCoordinates

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (Z : CentralizerDatum i) (hZ : IsTorus Z.Z) {b : characterLattice S}
  (C : AlgebraicSU3RootCoordinates (Z := Z.asTorus hZ) i Z.j Z.s b)
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (A : KPApartmentData i (IntegerValuation.order v))

/-- Over any henselian base, coherent algebraic unitary coordinates realize
the original base-normalized tower depth at a point of the supplied apartment. -/
theorem exists_unitaryTowerDepths [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hH : HenselianLocalRing v.valuationSubring)
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    ∃ (R : RootUnitaryCoordinates i Z.j Z.s b) (x : A.Apartment),
      ∀ p, x.val b (R.equiv p) =
        SU3Root.towerDepth k R.base R.extension v hH p := by
  refine ⟨C.positive.toRootUnitaryCoordinates, C.coordinateOrigin Z hZ A hn, ?_⟩
  exact (C.coordinateOrigin_depths Z hZ A hA hG hi hb hn
    (IntegerValuation.isNormCalibrated_henselianSeparableAddValuation hH C.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar k C.base C.extension v hH)).1

end AlgebraicSU3RootCoordinates

/-- Exact-target implication from the independent algebraic rank-one
coordinate-existence proposition, over every henselian integer-valued field. -/
def AlgebraicRankOneIndivisibleLiftsReductionStatement : Prop :=
  AlgebraicRankOneCoordinatesExistenceStatement.{u} →
    QuasiSplitIndivisibleDerivativeLiftsStatement.{u}

/-- Coherent algebraic coordinate existence discharges all remaining
multipliable unitary depth obligations for actual quasi-split apartments. -/
theorem quasiSplitMultipliableUnitaryTowerDepths_of_algebraicRankOneCoordinates
    (hc : AlgebraicRankOneCoordinatesExistenceStatement.{u}) :
    QuasiSplitMultipliableUnitaryTowerDepthsStatement.{u} := by
  intro k _ v _ hH G _ hq S i hi
  let := mono_of_isMaximalSplitTorus hi
  intro A Z hA
  have hG := hq.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom S.toGrp.X.hom := hi.1.1.isAffineHom
  let : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  let : IsClosedImmersion Z.j.hom.hom.left := Z.isClosedSubgroup
  let : IsAffine Z.Z.X.left := isAffine_of_isAffineHom Z.j.hom.hom.left
  have hZ : IsTorus Z.Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hq hi Z.isRepresentedBy
  have hF : RelativeRoot.HasOppositeFactorPairs i := by
    intro a ha g hg hg1
    exact ((rootRankOneFactorization k G hG S i hi) a ha g hg hg1).1.exists
  intro a h2a
  have ha := mem_indivisibleRoots_of_double_mem hi.1.1 hF a h2a
  obtain ⟨C, hn⟩ := (hc k G hG S (Z.asTorus hZ) i Z.j Z.s hi hZ
    Z.isRepresentedBy Z.comp_eq a ha).2 h2a
  exact C.exists_unitaryTowerDepths Z hZ A hH hA hG hi a.property hn

/-- The exact full-derivative lift target follows conditionally on the
independent algebraic coordinate-existence target, with no valuation gap. -/
theorem algebraicRankOneIndivisibleLiftsReduction :
    AlgebraicRankOneIndivisibleLiftsReductionStatement.{u} := by
  intro hc
  exact quasiSplitIndivisibleDerivativeLifts_of_multipliableUnitaryTowerDepths
    (quasiSplitMultipliableUnitaryTowerDepths_of_algebraicRankOneCoordinates hc)

end Langlands.Geometry.Building
