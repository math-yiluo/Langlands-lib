import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.Representation.Plancherel.RationalUnitaryDenominatorCancellation
import Langlands.Representation.Plancherel.RationalRankOneOperatorDenominator
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport

/-! # Cancellation of supplied unitary poles for the weighted c-family -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily

universe u uV uW uE

section Cancellation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H)

local instance cancellationPointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "νH" => fun a => (rationalNormCharacters H a).toMul
set_option quotPrecheck false in
local notation "X" => unramifiedCharacters νH
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters νH
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions νH

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Ω : Set X} {A : Ω → V →ₗ[ℂ] W}

include hH in
/-- The continuation is treated on its full nonvanishing locus, which can meet the
unitary subgroup even when the original convergence domain does not. After
cancellation extend the cross identity to the ambient character torus. This
recovers the clearing identity everywhere on the original domain, including
at zeros of the new denominator. -/
private theorem exists_poleFree_clearing (hne : Ω.Nonempty)
    (p : RationalOperatorContinuationData Ω A)
    (q : RationalOperatorPolePresentation H p.denominator p.numerator)
    (e : W ≃ₗ[ℂ] E)
    (hB : HasClearedUnitaryBound H (fun z => e.toLinearMap.comp (p.numerator z)) p.denominator) :
    ∃ (d : R) (N : X → V →ₗ[ℂ] W),
      IsPolynomialOperatorOn Set.univ (fun z => N z.val) ∧
      (∀ z : Ω, N z.val = d.val z.val • A z) ∧
      ∀ z : Xu, d.val (unitaryToUnramified H z) ≠ 0 := by
  let pR : RationalOperatorContinuationData p.regularRegion p.continuedOperator :=
    ⟨p.denominator, fun z => z.property, p.numerator, p.polynomial, fun z => by
      symm
      exact smul_inv_smul₀ z.property _⟩
  have hp0 : p.denominator ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    intro h
    exact p.denominator_nonzero ⟨z, hz⟩ (by rw [h]; rfl)
  have hD : Dense (unitaryToUnramified H ⁻¹' p.regularRegion) :=
    ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero H hH p.denominator hp0
  have hJ : ∀ v : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Xu)
      (hz : unitaryToUnramified H z ∈ p.regularRegion),
      ‖e (p.continuedOperator ⟨unitaryToUnramified H z, hz⟩ v)‖ ≤ C := by
    intro v
    obtain ⟨C, hC, hCv⟩ := hB v
    refine ⟨C, hC, fun z hz => ?_⟩
    let w := unitaryToUnramified H z
    have hb := hCv z
    change ‖e (p.numerator w v)‖ ≤ C * ‖p.denominator.val w‖ at hb
    rw [show p.numerator w = p.denominator.val w • p.continuedOperator ⟨w, hz⟩
      from pR.clears ⟨w, hz⟩, LinearMap.smul_apply, map_smul, norm_smul, mul_comm C] at hb
    exact le_of_mul_le_mul_left hb (norm_pos_iff.mpr hz)
  let Q := q.factors.cancelFromCross H hH pR e q.denominator q.numerator q.polynomial q.cross hD hJ
  let d := q.factors.remainder
  have hd0 : d ≠ 0 := by
    intro h
    exact q.factors.remainder_nonzero (1 : Xu) (by change d.val _ = 0; rw [h]; rfl)
  let hp := continuous_rationalValuationImageProjection H
  have hR : Dense p.regularRegion := rationalUnramifiedRegular_dense_nonzero H hp hH _ hp0
  have hd : Dense {z : X | d.val z ≠ 0} := rationalUnramifiedRegular_dense_nonzero H hp hH _ hd0
  have ho : IsOpen {z : X | d.val z ≠ 0} :=
    isOpen_ne_fun (continuous_unramifiedRegularFunction _ d) continuous_const
  have hcross : ∀ z : X, p.denominator.val z • Q.numerator z = d.val z • p.numerator z := by
    intro z
    exact polynomial_operator_cross_eq_of_dense
      (hR.inter_of_isOpen_right hd ho) isOpen_univ isOpen_univ
      (fun w => p.continuedOperator ⟨w.val, w.property.1⟩) Q.numerator p.numerator
      d p.denominator Q.polynomial p.polynomial (fun w _ => Q.clears w)
      (fun w _ => pR.clears ⟨w.val, w.property.1⟩) z ⟨Set.mem_univ _, Set.mem_univ _⟩
  refine ⟨d, Q.numerator, Q.polynomial, ?_, q.factors.remainder_nonzero⟩
  intro z
  apply smul_right_injective (V →ₗ[ℂ] W) (p.denominator_nonzero z)
  calc
    p.denominator.val z.val • Q.numerator z.val = d.val z.val • p.numerator z.val := hcross z.val
    _ = p.denominator.val z.val • (d.val z.val • A z) := by
      rw [p.clears z, smul_smul, smul_smul, mul_comm]

end Cancellation

section Weighted

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weightedCancellationAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weightedCancellationLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weightedCancellationLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weightedCancellationLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance weightedCancellationPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph eM ν₀
set_option hygiene false in
local notation "Φu" => standardLeviUnitaryCharacterHomeomorph I

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "Wₛ" => ProductInducedCompactPicture (decomposition χs)
  (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM) (SmoothRep.pullback (eₛ).symm π.obj)
set_option hygiene false in
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "A₀" => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN
set_option hygiene false in
local notation "Ω" => Φ ⁻¹' interior D₀
set_option hygiene false in
local notation "A" => fun z : (Ω : Set (unramifiedCharacters ν₀)) =>
  A₀ ⟨Φ z.val, interior_subset z.property⟩
set_option hygiene false in
local notation "Extension" => WeightedCExtension hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
  π PG PM hN

/-- For the fixed weighted c-family, transport its convergence-domain interior to the
actual inducing Levi's scheme characters. A rational continuation there, a cross-related
pole presentation, and a bound on the primary cleared numerator in the normed model
suffice for a `WeightedCExtension` on the original literal Levi characters. -/
def WeightedCExtensionFromPolesStatement
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : Wₛ ≃ₗ[ℂ] E) : Prop :=
  (interior D₀).Nonempty →
  ∀ (p : RationalOperatorContinuationData Ω A),
    Nonempty (RationalOperatorPolePresentation M₀ p.denominator p.numerator) →
    HasClearedUnitaryBound M₀ (fun z => e.toLinearMap.comp (p.numerator z)) p.denominator →
    Nonempty Extension

/-- Cancel the supplied poles on the scheme characters, then transport the resulting
numerator and denominator to the actual weighted c-family's character space. -/
theorem weightedCExtensionFromPoles
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : Wₛ ≃ₗ[ℂ] E) :
    WeightedCExtensionFromPolesStatement hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN e := by
  intro hint p ⟨q⟩ hB
  have hne : (Ω : Set (unramifiedCharacters ν₀)).Nonempty := by
    obtain ⟨z, hz⟩ := hint
    refine ⟨(Φ).symm z, ?_⟩
    have he : Φ ((Φ).symm z) = z := (Φ).apply_symm_apply z
    exact Eq.mpr (congrArg (fun y : unramifiedCharacters νM => y ∈ interior D₀) he) hz
  obtain ⟨d, N, hpoly, hclear, hreg⟩ := exists_poleFree_clearing M₀
    (lowerAmbient_isConnectedReductive hG hi hν I) hne p q e hB
  refine ⟨⟨hint, unramifiedRegularFunctionsEquiv eM ν₀ d, fun z => N ((Φ).symm z), ?_, ?_, ?_⟩⟩
  · intro v
    obtain ⟨r, b, V, h⟩ := hpoly v
    exact ⟨r, fun j => unramifiedRegularFunctionsEquiv eM ν₀ (b j), V,
      fun z => h ⟨(Φ).symm z.val, Set.mem_univ _⟩⟩
  · intro z hz
    let w := (Φ).symm z
    have he : Φ w = z := (Φ).apply_symm_apply z
    have hw : w ∈ (Ω : Set (unramifiedCharacters ν₀)) :=
      Eq.mpr (congrArg (fun y : unramifiedCharacters νM => y ∈ interior D₀) he) hz
    have hh : (⟨Φ w, interior_subset hw⟩ : D₀) = ⟨z, interior_subset hz⟩ := Subtype.ext he
    exact (hclear ⟨w, hw⟩).trans (congrArg (fun x : D₀ => d.val w • A₀ x) hh)
  · intro z
    let w := (Φu).symm z
    have he : Φ (unitaryToUnramified M₀ w) = ⟨z.val, z.property.1⟩ :=
      Subtype.ext (congrArg (fun t : unitaryUnramifiedCharacters νM => t.val)
        ((Φu).apply_symm_apply z))
    have hw : (Φ).symm ⟨z.val, z.property.1⟩ = unitaryToUnramified M₀ w :=
      (Φ).injective (((Φ).apply_symm_apply _).trans he.symm)
    intro hz
    exact hreg w ((congrArg d.val hw).symm.trans hz)

end Weighted

end Langlands.HarishChandraSchwartz.WeakExpansion
