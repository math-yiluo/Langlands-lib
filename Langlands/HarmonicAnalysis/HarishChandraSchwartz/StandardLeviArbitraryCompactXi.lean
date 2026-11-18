import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GlobalSquareIntegrableCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviTempered
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviCartanCoverTransport
import Langlands.BruhatTits.SpecialCompact.StandardLeviBasisInheritance

/-! # Arbitrary source compact Xi control on the literal standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance arbitraryCompactLeviAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance arbitraryCompactLeviAffine : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance arbitraryCompactLeviFiniteType : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J
local instance arbitraryCompactLeviTopology : TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
  rationalPointTopology F (Standard.leviScheme i ν J).X
local instance arbitraryCompactLeviNonarchimedean :
    NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν J)) :=
  rationalPoints_nonarchimedeanGroup _

/-- The literal preimage of an arbitrary displayed source compact in the
canonical Levi scheme. It need not be an ambient compact intersection. -/
def leviSchemeSourceCompact (KM : Subgroup (standardLeviPoints i ν J)) :
    Subgroup (rationalPoints (Standard.leviScheme i ν J)) :=
  KM.comap (leviSchemePointsEquiv i ν J).toMonoidHom

variable {i ν J} {KM : Subgroup (standardLeviPoints i ν J)}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Openness of the displayed compact source subgroup transports exactly. -/
theorem isOpen_leviSchemeSourceCompact (hKMo : IsOpen (KM : Set (standardLeviPoints i ν J))) :
    IsOpen (leviSchemeSourceCompact i ν J KM : Set (rationalPoints (Standard.leviScheme i ν J))) :=
  hKMo.preimage (leviSchemePointsEquiv i ν J).continuous

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Compactness of the displayed compact source subgroup transports exactly. -/
theorem isCompact_leviSchemeSourceCompact (hKMc : IsCompact (KM : Set (standardLeviPoints i ν J))) :
    IsCompact (leviSchemeSourceCompact i ν J KM : Set (rationalPoints (Standard.leviScheme i ν J))) :=
  (leviSchemePointsEquiv i ν J).toHomeomorph.isCompact_preimage.mpr hKMc

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- An arbitrary displayed source Iwasawa factorization becomes the
intrinsic minimal-parabolic Iwasawa factorization on the canonical Levi. -/
theorem isIwasawaPair_leviSchemeSourceCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J)) KM) :
    IsIwasawaPair (standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅)
      (leviSchemeSourceCompact i ν J KM) := by
  intro x
  let e := leviSchemePointsEquiv i ν J
  obtain ⟨p, hp, k, hk, hx⟩ := hM (e x)
  refine ⟨e.symm p,
    (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ _).2 ?_,
    e.symm k, ?_, ?_⟩
  · rw [map_leviSchemePointsEquiv_symm]
    exact hp
  · change e (e.symm k) ∈ KM
    rwa [e.apply_symm_apply]
  · apply e.injective
    rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hx]

/-- The actual minimal Levi modulus is trivial on the intersection with
any displayed compact open source subgroup. -/
theorem standardLeviMinimalModulusOf_eq_one_sourceCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKMo : IsOpen (KM : Set (standardLeviPoints i ν J)))
    (hKMc : IsCompact (KM : Set (standardLeviPoints i ν J)))
    (p : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (hp : (p : standardLeviPoints i ν J) ∈ KM) :
    standardLeviMinimalModulusOf i ν J p = 1 := by
  let e := leviSchemePointsEquiv i ν J
  let pL : standardParabolicPoints (Standard.leviTorusHom i ν J) ν ∅ :=
    ⟨e.symm (p : standardLeviPoints i ν J),
      (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ _).2 (by
        rw [map_leviSchemePointsEquiv_symm]
        exact p.property)⟩
  have hpL : (pL : rationalPoints (Standard.leviScheme i ν J)) ∈
      leviSchemeSourceCompact i ν J KM := by
    change e (e.symm (p : standardLeviPoints i ν J)) ∈ KM
    rwa [e.apply_symm_apply]
  have hq := rationalMinimalModulus_eq_one (Standard.leviTorusHom i ν J) ν
    (isOpen_leviSchemeSourceCompact hKMo) (isCompact_leviSchemeSourceCompact hKMc) pL hpL
  rw [← standardLeviMinimalModulus_leviHom hG hi hν hJ pL] at hq
  rw [standardLeviMinimalModulusOf_apply]
  convert hq using 1; congr 1
  apply Subtype.ext
  exact (map_leviSchemePointsEquiv_symm i ν J (p : standardLeviPoints i ν J)).symm

/-- Exact spherical transport for an arbitrary displayed source compact. -/
theorem rationalXi_leviSchemeSourceCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKMo : IsOpen (KM : Set (standardLeviPoints i ν J)))
    (hKMc : IsCompact (KM : Set (standardLeviPoints i ν J)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J)) KM)
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    letI : CompactSpace KM := isCompact_iff_compactSpace.mp hKMc
    rationalXi (isCompact_leviSchemeSourceCompact hKMc)
      (isIwasawaPair_leviSchemeSourceCompact hG hi hν hJ hM) x =
      xi hM (standardLeviMinimalModulusOf i ν J) (leviSchemePointsEquiv i ν J x) := by
  let : CompactSpace KM := isCompact_iff_compactSpace.mp hKMc
  let : CompactSpace (leviSchemeSourceCompact i ν J KM) :=
    isCompact_iff_compactSpace.mp (isCompact_leviSchemeSourceCompact hKMc)
  unfold rationalXi
  refine (xi_map (leviSchemePointsEquiv i ν J)
    (standardLeviMinimalModulusOf_eq_one_sourceCompact hG hi hν hJ hKMo hKMc)
    (fun p hp => ?_) (fun k => Iff.rfl) (fun p => ?_) x).symm
  · rw [Subgroup.mem_subgroupOf, leviSchemePointsEquiv_coe]
    exact (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).1 hp
  · rw [standardLeviMinimalModulusOf_apply]
    exact standardLeviMinimalModulus_leviHom hG hi hν hJ p

/-- Every coefficient of the original literal-Levi representation is
bounded by the source spherical function for any displayed compact open
source Iwasawa subgroup. All intrinsic basis and Cartan inputs are derived
from the original ambient basis and standard-Levi Cartan cover. The central
subgroup, quotient Haar measure and representation are the original ones. -/
theorem hasXiBoundedCoefficients_standardLeviArbitraryCompact
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKMo : IsOpen (KM : Set (standardLeviPoints i ν J)))
    (hKMc : IsCompact (KM : Set (standardLeviPoints i ν J)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J)) KM)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : StandardLeviCartanCovering F i ν J K0)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := standardLeviPoints i ν J))
    (C : Subgroup (standardLeviPoints i ν J)) [C.Normal]
    (hC : C ≤ Subgroup.center (standardLeviPoints i ν J))
    [MeasurableSpace (standardLeviPoints i ν J ⧸ C)] [BorelSpace (standardLeviPoints i ν J ⧸ C)]
    (mu : Measure (standardLeviPoints i ν J ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu) :
    letI : CompactSpace KM := isCompact_iff_compactSpace.mp hKMc
    HasXiBoundedCoefficients (xi hM (standardLeviMinimalModulusOf i ν J)) π.obj.representation := by
  let : CompactSpace KM := isCompact_iff_compactSpace.mp hKMc
  let e := leviSchemePointsEquiv i ν J
  let CL : Subgroup (rationalPoints (Standard.leviScheme i ν J)) := C.comap e.toMonoidHom
  have hCL : CL ≤ Subgroup.center (rationalPoints (Standard.leviScheme i ν J)) :=
    (Subgroup.comap_mono hC).trans (Subgroup.comap_center_le_center e.injective)
  have hCLmap : CL.map e.toMulEquiv.toMonoidHom = C :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective C
  let : MeasurableSpace (rationalPoints (Standard.leviScheme i ν J) ⧸ CL) := borel _
  let : BorelSpace (rationalPoints (Standard.leviScheme i ν J) ⧸ CL) := ⟨rfl⟩
  let eQ := quotientContinuousMulEquiv e C CL hCLmap
  let muL : Measure (rationalPoints (Standard.leviScheme i ν J) ⧸ CL) := mu.map eQ.symm
  have : muL.IsHaarMeasure := eQ.symm.isHaarMeasure_map mu
  have hmap : muL.map eQ = mu :=
    MeasurableEquiv.map_map_symm eQ.toHomeomorph.toMeasurableEquiv
  let πL := IrreducibleAdmissibleRep.pullback e π
  have hsqL : IsSquareIntegrableModCentralSubgroup CL hCL πL.obj.representation muL :=
    (isSquareIntegrableModCentralSubgroup_comp_iff e C hC CL hCL hCLmap mu muL hmap
      π.obj.representation).mpr hsq
  obtain ⟨-, T, a, -, ha, -⟩ := standardLeviSplitComponentStatement F G hG S i hi ν hν J hJ
  have hbound := hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
    (isOpen_leviSchemeSourceCompact hKMo) (isCompact_leviSchemeSourceCompact hKMc)
    (isIwasawaPair_leviSchemeSourceCompact hG hi hν hJ hM)
    (standardLevi_isConnectedReductive hG i hi ν hν J hJ)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (isGenericCocharacter_leviTorusHom hν)
    (isCompact_leviSchemeCompact (i := i) (ν := ν) (J := J) hK0c)
    (hbasis.leviScheme i ν J hG hi hν hJ)
    (finiteCartanCovering_leviScheme i ν J hG hi hν hJ hcover)
    ha πL CL hCL muL hsqL
  have hXi : rationalXi (isCompact_leviSchemeSourceCompact hKMc)
      (isIwasawaPair_leviSchemeSourceCompact hG hi hν hJ hM) =
      xi hM (standardLeviMinimalModulusOf i ν J) ∘ e :=
    funext (rationalXi_leviSchemeSourceCompact hG hi hν hJ hKMo hKMc hM)
  rw [hXi] at hbound
  exact (hasXiBoundedCoefficients_comp_continuousMulEquiv_iff _ π.obj.representation e).mp hbound

end Langlands.HarishChandraSchwartz
