import Langlands.Geometry.Building.IntegerValuationBoundedCharacterImage
import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Rational.ValuedBoundedProducts
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylSpanFiniteness
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof

/-! # Finite apartment orbits of algebraically bounded normalizer sets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k] [ValuativeRel k]
    {v : Valuation k (WithZero (Multiplicative ℤ))} [v.Compatible]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

private instance boundedNormalizerAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- A bounded subset of the actual centralizer has finite orbit at every
apartment point, since its character kernel fixes the whole apartment. -/
theorem finite_centralizer_orbit_of_isAlgebraicallyBounded
    [IsAffine B.centralizer.Z.X.left]
    (X : Set (rationalPoints B.centralizer.Z))
    (hX : IsAlgebraicallyBounded k B.centralizer.Z.X X) (x : B.Apartment) :
    ((fun z => B.centralizer.toNormalizer z • x) '' X).Finite := by
  have hZ := splitTorusCentralizerReductive k G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus.isSplitSubtorus.1 B.centralizer.Z B.centralizer.j
    B.centralizer.isRepresentedBy
  obtain ⟨T, -, hT, hXT⟩ :=
    IntegerValuation.exists_finite_characterKernel_representatives_of_isAlgebraicallyBounded
      v B.centralizer.Z hZ X hX
  refine (hT.image (fun z => B.centralizer.toNormalizer z • x)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht, htz⟩ := hXT z hz
  refine ⟨t, ht, ?_⟩
  have he := congrArg (fun y => B.centralizer.toNormalizer t • y)
    (B.isOmegaCompatible.smul_eq_self htz x)
  simpa only [map_mul, map_inv, mul_smul, smul_inv_smul] using he.symm

/-- An algebraically bounded subset of the actual normalizer has finite orbit
at every apartment point. Boundedness is measured in the original ambient group. -/
theorem finite_normalizer_orbit_of_isAlgebraicallyBounded
    (X : Set (normalizerPoints B.i))
    (hX : IsAlgebraicallyBounded k G.X
      ((fun n : normalizerPoints B.i => (n : rationalPoints G)) '' X))
    (x : B.Apartment) :
    ((fun n : normalizerPoints B.i => n • x) '' X).Finite := by
  classical
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsClosedImmersion B.centralizer.j.hom.hom.left :=
    B.centralizer.isClosedSubgroup
  let : IsAffine B.centralizer.Z.X.left := by
    let : IsAffineHom B.centralizer.Z.X.hom := by
      rw [← Over.w B.centralizer.j.hom.hom]
      infer_instance
    exact isAffine_of_isAffineHom B.centralizer.Z.X.hom
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeWeylGroup_of_span B.i
    (relativeRootsRestrictedCharactersSpan k G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus)
  let m : relativeWeylGroup B.i → normalizerPoints B.i := Quotient.out
  let Xw (w : relativeWeylGroup B.i) : Set (rationalPoints B.centralizer.Z) :=
    {z | m w * B.centralizer.toNormalizer z ∈ X}
  have hb (w : relativeWeylGroup B.i) :
      IsAlgebraicallyBounded k B.centralizer.Z.X (Xw w) := by
    apply isAlgebraicallyBounded_of_closedImmersion k B.centralizer.j.hom.hom
    have ht := isAlgebraicallyBounded_smul_set_of_finiteType hX
      ((m w : rationalPoints G)⁻¹)
    apply ht.mono
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨(m w * B.centralizer.toNormalizer z : normalizerPoints B.i),
      ⟨m w * B.centralizer.toNormalizer z, hz, rfl⟩, ?_⟩
    simp only [Subgroup.coe_mul, coe_centralizerToNormalizer, smul_eq_mul,
      inv_mul_cancel_left]
    rfl
  have hfin := Set.finite_iUnion (fun w : relativeWeylGroup B.i =>
    (B.finite_centralizer_orbit_of_isAlgebraicallyBounded (Xw w) (hb w) x).image
      (fun y : B.Apartment => m w • y))
  apply hfin.subset
  rintro _ ⟨n, hn, rfl⟩
  let w : relativeWeylGroup B.i := QuotientGroup.mk n
  have hmw : (QuotientGroup.mk (m w) : relativeWeylGroup B.i) =
      QuotientGroup.mk n := Quotient.out_eq _
  have hc : ((m w)⁻¹ * n : normalizerPoints B.i).val ∈ centralizerPoints B.i := by
    rw [← Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq.mp hmw
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at hc
  obtain ⟨z, hjz⟩ : ∃ z : rationalPoints B.centralizer.Z,
      rationalPoints.map B.centralizer.j z =
        (((m w)⁻¹ * n : normalizerPoints B.i) : rationalPoints G) := hc
  have hzn : B.centralizer.toNormalizer z = (m w)⁻¹ * n := Subtype.ext hjz
  have hzm : m w * B.centralizer.toNormalizer z = n := by
    rw [hzn, mul_inv_cancel_left]
  refine Set.mem_iUnion.mpr ⟨w, ?_⟩
  refine ⟨B.centralizer.toNormalizer z • x, ⟨z, ?_, rfl⟩, ?_⟩
  · change m w * B.centralizer.toNormalizer z ∈ X
    rwa [hzm]
  · change m w • (B.centralizer.toNormalizer z • x) = n • x
    rw [← mul_smul, hzm]

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.Geometry.Building.IntegerValuation

/-- Ambient algebraic boundedness forces finite apartment orbits for subsets
of the actual normalizer, over any compatible integer-valued field. -/
def BoundedNormalizerOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)
    (X : Set (normalizerPoints B.i)),
    IsAlgebraicallyBounded k G.X
      ((fun n : normalizerPoints B.i => (n : rationalPoints G)) '' X) →
    ∀ x : B.Apartment, ((fun n : normalizerPoints B.i => n • x) '' X).Finite

/-- The centralizer character-kernel and finite relative-Weyl arguments prove
the exact arbitrary-universe finite normalizer-orbit proposition. -/
theorem boundedNormalizerOrbit : BoundedNormalizerOrbitStatement.{u} := by
  intro k _ _ v _ G _ B X hX x
  exact B.finite_normalizer_orbit_of_isAlgebraicallyBounded X hX x

end Langlands.Geometry.Building.IntegerValuation
