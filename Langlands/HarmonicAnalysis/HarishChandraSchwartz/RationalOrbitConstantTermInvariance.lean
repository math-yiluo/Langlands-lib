import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalPositivePartDecayAssembly

/-! # A common open right-invariance subgroup for actual orbit constant terms -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

section Generic

variable {J : Set (characterLattice S)}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

/-- All chosen standard constant terms in the family are fixed by the right translations of
one open subgroup of the actual standard Levi. -/
def HasUniformStandardConstantTermRightInvariance {κ : Type*}
    (f : κ → rationalPoints G → ℂ) : Prop :=
  ∃ U : OpenSubgroup (standardLeviPoints i ν J), ∀ ω m k, k ∈ U →
    standardConstantTerm hA (f ω) (m * k) = standardConstantTerm hA (f ω) m

variable (hi : IsMaximalSplitTorus i) {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)

include hi hζ in
/-- Right invariance under a compact open subgroup passes to the chosen constant term on
its intersection with the Levi. The zero branch of `standardConstantTerm` is included. -/
theorem standardConstantTerm_mul_right_eq_of_invariance
    {H : OpenSubgroup (rationalPoints G)} (hH : IsCompact (H : Set (rationalPoints G)))
    {f : rationalPoints G → ℂ}
    (hf : ∀ g k, k ∈ H → f (g * k) = f g)
    (m k : standardLeviPoints i ν J) (hk : (k : rationalPoints G) ∈ H) :
    standardConstantTerm hA f (m * k) = standardConstantTerm hA f m := by
  classical
  by_cases h : HasStandardConstantTerm hA f
  · have hδ : standardHalfModulus i ν J k = 1 := by
      have hd : standardRadicalModulus i ν J k = 1 :=
        standardUnipotentModulus_eq_one i ν J H.isOpen hH k hk
      simp [standardHalfModulus, hd]
    have heq := congrFun (standardConstantTerm_mul_right hi hζ hA h k) m
    have hfun : (fun g => f (g * (k : rationalPoints G))) = f := by
      funext g
      exact hf g k hk
    rw [hfun, hδ, one_mul] at heq
    exact heq.symm
  · simp [standardConstantTerm, h]

include hi hζ in
/-- A common compact open subgroup fixing the full function family gives one common open
right-invariance subgroup for all of its chosen standard constant terms. -/
theorem hasUniformStandardConstantTermRightInvariance_of_rightInvariant {κ : Type*}
    {f : κ → rationalPoints G → ℂ} {H : OpenSubgroup (rationalPoints G)}
    (hH : IsCompact (H : Set (rationalPoints G)))
    (hf : ∀ ω g k, k ∈ H → f ω (g * k) = f ω g) :
    HasUniformStandardConstantTermRightInvariance hA f := by
  let U := H.comap (standardLeviPoints i ν J).subtype continuous_subtype_val
  exact ⟨U, fun ω m k hk =>
    standardConstantTerm_mul_right_eq_of_invariance hA hi hζ hH (hf ω) m k hk⟩

end Generic

section Orbit

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "𝒪" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

set_option hygiene false in
local notation "𝐟" => rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq

/-- The actual orbit coefficients have one common compact open subgroup of bi-invariance,
uniform over the entire orbit. -/
theorem rationalInducedOrbitCoefficientMap_hasUniformBiInvariance
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ H : OpenSubgroup (rationalPoints G), H ≤ K ∧ IsCompact (H : Set (rationalPoints G)) ∧
      ∀ (ω : 𝒪) (k l : H) (g : rationalPoints G),
        𝐟 ψ ω ((k : rationalPoints G) * g * (l : rationalPoints G)) = 𝐟 ψ ω g := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  unfold rationalInducedOrbitCoefficientMap
  with_reducible_and_instances apply unitaryOrbitCoefficientMap_biInvariant

/-- At every fixed actual group point, the orbit coefficient is continuous in the entire
actual unitary orbit parameter. -/
theorem continuous_rationalInducedOrbitCoefficientMap
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) :
    Continuous (fun ω : 𝒪 => 𝐟 ψ ω g) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  unfold rationalInducedOrbitCoefficientMap
  with_reducible_and_instances apply continuous_unitaryOrbitCoefficient
  · exact leviRationalUnitaryCoordinates_hasLaurent hG hi hν I
  · exact (leviRationalUnitaryCoordinates hG hi hν I).continuous

variable (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I') ζ)

include hζ in
/-- The actual chosen orbit constant terms share an open subgroup of right invariance.
This needs no constant-term existence or family-regularity premise. -/
theorem rationalOrbitConstantTerm_hasUniformRightInvariance
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    HasUniformStandardConstantTermRightInvariance hA (fun (ω : 𝒪) => 𝐟 ψ ω) := by
  obtain ⟨H, _, hH, hfix⟩ :=
    rationalInducedOrbitCoefficientMap_hasUniformBiInvariance hG hi hν I hKc hPK π C hC mu hsq ψ
  apply hasUniformStandardConstantTermRightInvariance_of_rightInvariant hA hi hζ hH
  intro ω g k hk
  have heq := hfix ω (1 : H) ⟨k, hk⟩ g
  simpa only [OneMemClass.coe_one, one_mul] using heq

include hζ in
/-- Pointwise parameter continuity of the full actual constant terms suffices for their
joint continuity; the common open right-invariance subgroup is derived above. -/
theorem continuous_uncurry_rationalOrbitConstantTerm
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (hc : ∀ m, Continuous (fun ω : 𝒪 =>
      rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω m)) :
    Continuous (Function.uncurry
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ)) := by
  obtain ⟨U, hU⟩ := rationalOrbitConstantTerm_hasUniformRightInvariance
    hG hi hν I hKc hPK π C hC mu hsq I' hA hζ ψ
  exact continuous_uncurry_of_uniform_right_invariance U.isOpen hc hU

include hζ in
/-- Once fixed-point parameter continuity is supplied, compactness of the actual full
unitary orbit and continuity/positivity of the actual Levi Xi give the compact-bound clause
of `HasRationalSplitDecayInput`. No additional orbit-compactness premise is needed. -/
theorem rationalOrbitConstantTerm_hasUniformWeightedCompactBounds
    (hM' : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')))
      ((K : Subgroup (rationalPoints G)).subgroupOf
        (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I'))))
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (hc : ∀ m, Continuous (fun ω : 𝒪 =>
      rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω m)) :
    HasUniformWeightedCompactBounds
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ)
      (rationalLeviXi hKc hM') := by
  let : CompactSpace (unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters
      i ν I)) := (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  let := compactSpace_discreteSeriesOrbit C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)
  exact hasUniformWeightedCompactBounds_of_continuous
    (continuous_uncurry_rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA hζ ψ hc)
    (continuous_rationalLeviXi hG hi hν (RationalPointFamily.rootSet_subset i ν I')
      K.isOpen hKc hM')
    (rationalLeviXi_pos K.isOpen hKc hG hi hν (RationalPointFamily.rootSet_subset i ν I') hM')

end Orbit

end Langlands.HarishChandraSchwartz
