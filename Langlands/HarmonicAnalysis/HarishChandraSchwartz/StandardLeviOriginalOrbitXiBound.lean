import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ArbitraryCompactTwistCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviArbitraryCompactXi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedLeviCompact

/-! # Original actual orbit coefficients from central square integrability -/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Generic

universe uG uV uI uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)]


/-- Representative bound for the original coefficient map with arbitrary source compact. -/
theorem exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi_arbitraryCompact
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : UnitaryOrbitRepresentative ν π) (g : G),
      ‖unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A) g‖ ≤
        c * xi hP₀K δ₀ g := by
  have hPK' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.2, k, k.2, hg⟩
  let R := productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    (productInducedOrbitPullback ν π e h hU q.val)
  have hR : R ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj) := q.property.2
  obtain ⟨c, hc, hb⟩ := norm_family_coefficientMap_le_xi_arbitraryCompact h hU π.obj K hK ν hν hP hr hPK' hG hδ
    π.property.2 hδU hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff R hR (Function.invFun (unitaryTorusParameter ν e))
  refine ⟨c, hc, fun A g => ?_⟩
  let z := unitaryOrbitRepresentativeParameter ν π e A
  let B := unitaryOrbitParameterRepresentative ν π e z
  have hq : q.val A = productInducedCoefficientTransport h hU
      (unitaryOrbitRepresentativeEquiv ν π e A) (q.val B) := q.property.1 B A _
  rw [hq, unitaryOrbitRepresentativeCoefficientMap_transport]
  have hz : Function.invFun (unitaryTorusParameter ν e) (unitaryTorusParameter ν e z) = z :=
    Function.leftInverse_invFun (unitaryTorusParameter_injective ν e) z
  have hbz := hb (unitaryTorusParameter ν e z) (norm_unitaryTorusParameter_apply ν e z) g
  rw [hz] at hbz
  have hts : twistedSection h hU π.obj K ν hP hK hν hr (factorization_subtype hPK')
      (unitaryTorusParameter ν e z) (R z) = q.val B :=
    (productInducedCompactEquiv ν h K hP hK hν hr hU (factorization_subtype hPK')
      (unitaryTorusParameter ν e z) π.obj).symm_apply_apply (q.val B)
  rw [hts] at hbz
  exact hbz

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- Orbit descent of the original representative coefficient bound,
using a displayed arbitrary source compact subgroup. -/
theorem exists_norm_unitaryOrbitCoefficientMap_le_xi_arbitraryCompact
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ω : discreteSeriesOrbit C hC mu ν (discreteSeriesClass C hC mu π hsq)) (g : G),
        ‖unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC mu hsq e q ω g‖ ≤
          c * xi hP₀K δ₀ g := by
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi_arbitraryCompact h hU hP K hK
    hPK hG hδ ν π hν hr e hδU hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff q
  refine ⟨c, hc, fun ω g => ?_⟩
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC mu hsq ω
  rw [unitaryOrbitCoefficientMap_representative]
  exact hb A g


end Generic

section Actual

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)}

set_option hygiene false in
local notation "rootsI" => RationalPointFamily.rootSet i ν I
set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν rootsI
set_option hygiene false in
local notation "hsemi" => isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)

/-- The source compact on the literal Levi obtained by projecting the
original compact intersection with the original source parabolic. -/
def rationalProjectedLeviCompact : Subgroup 𝐌 :=
  projectedLeviCompact hsemi (K : Subgroup (rationalPoints G))

/-- The projected source compact is open in the literal Levi. -/
theorem isOpen_rationalProjectedLeviCompact :
    IsOpen (rationalProjectedLeviCompact hG hi hν I (K := K) : Set 𝐌) :=
  isOpen_projectedLeviCompact hsemi (K : Subgroup (rationalPoints G)) K.isOpen

omit [LocallyOfFiniteType G.X.hom] in
/-- The original compact source intersection has compact projected image. -/
theorem isCompact_rationalProjectedLeviCompact (hKc : IsCompact (K : Set (rationalPoints G))) :
    IsCompact (rationalProjectedLeviCompact hG hi hν I (K := K) : Set 𝐌) :=
  isCompact_projectedLeviCompact hsemi (K : Subgroup (rationalPoints G))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The actual source Iwasawa factorization follows from the original
ambient one, without a projection-stability premise on the original K. -/
theorem isIwasawaPair_rationalProjectedLeviCompact
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G))) :
    IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf 𝐌)
      (rationalProjectedLeviCompact hG hi hν I (K := K)) :=
  isIwasawaPair_projectedLeviCompact hsemi (K : Subgroup (rationalPoints G))
    (standardParabolicPoints_empty_le hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (fun _ hu => standardUnipotent_le_standardParabolic i ν ∅ _
      (standardUnipotentPoints_le_empty_of_subset hG hi hν (RationalPointFamily.rootSet_subset i ν I) hu)) hPK

/-- The actual source spherical function at the projected compact. -/
def rationalProjectedLeviXi (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
    (m : 𝐌) : ℝ :=
  letI : CompactSpace (rationalProjectedLeviCompact hG hi hν I (K := K)) :=
    isCompact_iff_compactSpace.mp (isCompact_rationalProjectedLeviCompact hG hi hν I hKc)
  xi (isIwasawaPair_rationalProjectedLeviCompact hG hi hν I hPK)
    (standardLeviMinimalModulusOf i ν rootsI) m

variable (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
  (hbasis : SimultaneousStandardBasisAt i ν K0)
  (hcover : StandardLeviCartanCovering F i ν rootsI K0)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

include hK0c hbasis hcover hsq in
/-- The original literal-Levi coefficients have a global Xi bound with
source compact derived from the original ambient Iwasawa factorization.
Only original ambient structural and central-square-integrability inputs
remain; no intrinsic structural or source-Iwasawa output is a premise. -/
theorem hasXiBoundedCoefficients_standardLeviProjectedCompact :
    HasXiBoundedCoefficients (rationalProjectedLeviXi hG hi hν I hKc hPK) π.obj.representation := by
  exact hasXiBoundedCoefficients_standardLeviArbitraryCompact hG hi hν
    (RationalPointFamily.rootSet_subset i ν I)
    (isOpen_rationalProjectedLeviCompact hG hi hν I)
    (isCompact_rationalProjectedLeviCompact hG hi hν I hKc)
    (isIwasawaPair_rationalProjectedLeviCompact hG hi hν I hPK)
    hK0c hbasis hcover π C hC mu hsq

include hK0c hbasis hcover hsq in
/-- Global original orbit coefficient control from the original ambient
structural data and square integrability modulo the original central subgroup. -/
theorem exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi_of_squareIntegrable
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ω : discreteSeriesOrbit C hC mu
        (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))
        (g : rationalPoints G),
      ‖rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q ω g‖ ≤
        c * rationalXi hKc hPK g := by
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let : CompactSpace (rationalProjectedLeviCompact hG hi hν I (K := K)) :=
    isCompact_iff_compactSpace.mp (isCompact_rationalProjectedLeviCompact hG hi hν I hKc)
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitCoefficientMap_le_xi_arbitraryCompact (G := rationalPoints G)
    (M := 𝐌) hsemi
    (isClosed_standardUnipotentPoints i ν rootsI)
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK
    (rationalProjectedLeviCompact hG hi hν I (K := K))
    (isIwasawaPair_rationalProjectedLeviCompact hG hi hν I hPK)
    (isOpen_rationalProjectedLeviCompact hG hi hν I)
    (standardLeviMinimalModulusOf_eq_one_sourceCompact hG hi hν (RationalPointFamily.rootSet_subset i ν I)
      (isOpen_rationalProjectedLeviCompact hG hi hν I)
      (isCompact_rationalProjectedLeviCompact hG hi hν I hKc))
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    (hasXiBoundedCoefficients_standardLeviProjectedCompact hG hi hν I hKc hPK hK0c hbasis hcover
      π C hC mu hsq) q
  refine ⟨c, hc, fun ω g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  rewrite [← hx]
  with_reducible_and_instances exact hb ω g

end Actual

end Langlands.HarishChandraSchwartz
