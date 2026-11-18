import Langlands.Representation.Jacquet.StandardComponentScheme
import Langlands.Representation.Jacquet.StandardConstantTermFixedLevel
import Langlands.Representation.Exponents.NormalizedIwahoriEigenCoefficient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedExponentCone
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitCoefficientBound

/-! # Bounds for actual standard Jacquet exponents along a specified strict ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Jacquet
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.BruhatTits.SpecialCompact

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν J q L)

include hB hmem in
omit [LocallyOfFiniteType G.X.hom] in
/-- Every specified actual strict component lattice point, rather than
only the chosen strict point, has cofinally small standard Iwahori
contractions for that same element. -/
theorem hasIwahoriContractionBasisAt_standard_strict
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q)) :
    HasIwahoriContractionBasisAt (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J)
      (standardComponentHom hA a : rationalPoints G) := by
  intro L
  obtain ⟨W, hW, hWL⟩ := isOpen_induced_iff.mp L.isOpen
  have h1 : (1 : rationalPoints G) ∈ W := by
    have h : (1 : standardLeviPoints i ν J) ∈
        (Subtype.val : standardLeviPoints i ν J → rationalPoints G) ⁻¹' W := by
      rw [hWL]
      exact L.one_mem
    exact h
  obtain ⟨K, hKB, hKW⟩ := hB.2.mem_iff.mp (hW.mem_nhds h1)
  have hgCA : (standardComponentHom hA a : rationalPoints G) ∈ standardComponentCA i q :=
    ⟨a, ha.1, rfl⟩
  have hgplus : (standardComponentHom hA a : rationalPoints G) ∈
      standardComponentCAplus i ν J q :=
    ⟨a, ⟨ha.1, fun α hα => (ha.2 α hα).le⟩, rfl⟩
  have hgstrict : (standardComponentHom hA a : rationalPoints G) ∈
      standardComponentCAstrict i ν J q := ⟨a, ha, rfl⟩
  refine ⟨basisOpenSubgroup hB hKB, (hB.1 K hKB).2.2.2, ?_, ?_⟩
  · intro m hm
    change m ∈ (L : Set (standardLeviPoints i ν J))
    rw [← hWL]
    exact hKW hm
  · exact isIwahoriContraction_of_contractionAndCofinality (hB.1 K hKB).2.2.1
      (hmem K hKB).1 (hmem K hKB).2 (standardComponentHom hA a).property
      hgCA hgplus hgstrict

end Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν J q L)

/-- A bound on the generalized exponents of the actual normalized Jacquet action. -/
abbrev HasStandardJacquetExponentNormBoundAt
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
    (a : rationalPoints A.toGrp) (bound : ℝ) : Prop :=
  ∀ (χ : rationalPoints A.toGrp →* ℂˣ),
    IsGeneralizedEigencharacter
      ((standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ).representation.comp
        (standardComponentHom hA)) χ →
    ‖(χ a : ℂ)‖ ≤ bound

include hB hmem in
set_option maxHeartbeats 1200000 in
/-- Actual normalized standard Jacquet exponent values have norm at most
one when the original coefficients have a Xi bound and Xi along the
specified actual strict ray is bounded by its half-modulus times a
polynomial in the power. These analytic inputs remain explicit here. -/
theorem norm_standardJacquet_exponent_le_one_of_ray_bound
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
    {Ξ : rationalPoints G → ℝ} (hcoeff : HasXiBoundedCoefficients Ξ ρ.representation)
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q))
    (hray : ∃ (C : ℝ) (d : ℕ), ∀ n : ℕ, 1 ≤ n →
      Ξ ((standardComponentHom hA a : rationalPoints G) ^ n) ≤
        C * ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ ^ n * (1 + n) ^ d) :
    HasStandardJacquetExponentNormBoundAt hA ρ a 1 := by
  intro χ hχ
  have hχ' := (isGeneralizedEigencharacter_standardNormalizedJacquet_iff hA ρ χ).mpr hχ
  obtain ⟨L, hL, x, ℓ, hℓx, _, hexact⟩ :=
    exists_eigen_coefficient_of_normalizedJacquet_generalizedEigencharacter
      (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) (isClosed_standardUnipotentPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) ρ hρ
      (standardComponentHom hA) χ hχ' a
      (Subgroup.mem_center_iff.mpr (fun m => (standardComponentHom_commute hA a m).symm))
      (hasIwahoriContractionBasisAt_standard_strict hA hB hmem a ha)
  have hhalf :
      ((HaarModulus.closedInverseHalfCharacter (standardUnipotentPoints i ν J)
        (isClosed_standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
        (standardComponentHom hA a) : ℂ)⁻¹) =
      standardHalfModulus i ν J (standardComponentHom hA a) := by
    rw [HaarModulus.closedInverseHalfCharacter, inverseHalfCharacter_apply, inv_inv]
    rfl
  simp only [hhalf] at hexact
  obtain ⟨c, hc, hcb⟩ := hcoeff x ℓ
  obtain ⟨C, d, hC⟩ := hray
  have hs : 0 < ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ :=
    norm_pos_iff.mpr (standardHalfModulus_ne_zero _)
  have hle : ‖standardHalfModulus i ν J (standardComponentHom hA a) * (χ a : ℂ)‖ ≤
      ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ := by
    apply le_of_eventually_pow_mul_le hs (norm_pos_iff.mpr hℓx) (C := c * C) (k := d)
    filter_upwards [eventually_ge_atTop 1] with n hn
    calc
      ‖standardHalfModulus i ν J (standardComponentHom hA a) * (χ a : ℂ)‖ ^ n *
          ‖(ℓ : Module.Dual ℂ ρ) x‖ =
          ‖(ℓ : Module.Dual ℂ ρ)
            (ρ.representation ((standardComponentHom hA a : rationalPoints G) ^ n) x)‖ := by
        rw [hexact n]
        simp only [norm_mul, norm_pow]
      _ ≤ c * Ξ ((standardComponentHom hA a : rationalPoints G) ^ n) := hcb _
      _ ≤ c * (C * ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ ^ n *
          (1 + n) ^ d) := mul_le_mul_of_nonneg_left (hC n hn) hc.le
      _ = c * C * ‖standardHalfModulus i ν J (standardComponentHom hA a)‖ ^ n *
          (1 + n) ^ d := by ring
  rw [norm_mul] at hle
  exact (mul_le_iff_le_one_right hs).mp hle

end Langlands.HarishChandraSchwartz
