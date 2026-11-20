import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryIrreducibilityProof
import Langlands.Representation.Families.AdmissibleInducedIrreducibilityOpen

/-! # An ambient irreducibility open for actual common-Levi induction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Aubert.General.RepresentedParabolic Induction HarishChandraSchwartz
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition ActualCommonLeviTensor
open DynamicCommonLeviPresentationComparison DynamicCommonLeviCompact CompactInduction
open Renard.AlgebraicFamily Renard.AlgebraicFamily.UnramifiedPolynomialWitness

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure]

variable (hG : IsConnectedReductive G)
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (hsplit : IsActualSplitCenter χ C)
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "h" => commonDecomposition χ ψ hψ
local notation "hU" => radical_isClosed ψ
set_option quotPrecheck false in
local notation "I" z => (normalizedInductionFunctor h hU).obj (twistObject χ z A)

include hG hsq hi hsplit in
/-- An irreducible unitary point supplies an ambient principal open of
irreducible actual inductions. Its defining regular function is from the
actual unramified algebra of the common Levi. -/
theorem exists_actual_induction_irreducibility_factor :
    ∃ b : unramifiedRegularFunctions (normCharacters χ), b ≠ 0 ∧
      ∀ z : X, b.val z ≠ 0 → (I z).representation.IsIrreducible := by
  obtain ⟨z₀, hz₀⟩ := (denseUnitaryIrreducibility χ A C hC qMeasure hG hsq hi hsplit ψ hψ).nonempty
  let := hG.smooth
  obtain ⟨T, a, ha, _⟩ := hsplit
  let d := DynamicCommonLeviPresentations.parabolicData χ ψ hG hψ T a ha
  have hp := d.r.isCompatible.parabolic
  have hl := d.r.isCompatible.levi
  have hmul := d.r.isIso_subgroupMultiplication_of_radical d.radical
  let ρ := SmoothRep.pullback (parameterHomeomorph χ) A
  have hρ : ρ.IsIrreducible :=
    (SmoothRep.isIrreducible_pullbackFunctor_obj_iff _ A).mpr hi
  have hρadm : ρ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hsq.1
  let e := leviInductionFunctor d.p d.l d.n hp d.radical hl hmul
  have hcompare (z : X) :
      (e.obj (ρ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ z))).IsIrreducible ↔
        (I z).IsIrreducible := by
    refine leviInduction_isIrreducible_iff_of_pointImage d.p d.l d.n hp d.radical hl hmul h hU
      (parabolicPoints_eq χ ψ d.realizes) (leviPoints_eq χ ψ d.realizes)
      (radicalPoints_eq χ ψ d.realizes)
      (ρ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ z))
      (twistObject χ z A) (LinearEquiv.refl ℂ A) (parameterHomeomorph χ) ?_ ?_
    · intro m
      rw [d.levi_comp]
      rfl
    · intro m x
      change (z.val m : ℂ) • A.representation (parameterHomeomorph χ m) x =
        (z.val ((parameterHomeomorph χ).symm (parameterHomeomorph χ m)) : ℂ) •
          A.representation (parameterHomeomorph χ m) x
      rw [ContinuousMulEquiv.symm_apply_apply]
  let z₁ := unitaryParameter χ z₀
  obtain ⟨f, hf₁, hf⟩ := admissibleInducedIrreducibilityOpen.{u, uV} F G hG
    d.P (parameterScheme χ) d.U d.p d.l d.n hp hl d.radical hmul ρ hρ hρadm z₁
    ((hcompare z₁).mpr hz₀)
  let hM := hl.isConnectedReductive
  let b : unramifiedRegularFunctions (normCharacters χ) :=
    rationalCanonicalUnramifiedLaurentAlgebraEquiv (parameterScheme χ) hM (polynomialToLaurent _ f)
  have hmem (z : X) : z ∈ rationalUnramifiedPrincipalOpen (parameterScheme χ) hM f ↔ b.val z ≠ 0 := by
    rw [mem_rationalUnramifiedPrincipalOpen]
    dsimp only [b]
    rw [canonicalLaurent_eval, polynomialToLaurent_eval]
  have hb : b ≠ 0 := by
    intro he
    have hne := (hmem z₁).mp hf₁
    rw [he] at hne
    exact hne rfl
  exact ⟨b, hb, fun z hz => (hcompare z).mp (hf z ((hmem z).mpr hz))⟩

/-- Choose a nonzero regular factor for this actual induction's ambient
principal irreducibility locus. -/
def actualInductionIrreducibilityFactor :
    {b : unramifiedRegularFunctions (normCharacters χ) // b ≠ 0 ∧
      ∀ z : X, b.val z ≠ 0 → (I z).representation.IsIrreducible} :=
  ⟨Classical.choose (exists_actual_induction_irreducibility_factor χ A C hC qMeasure hG hsq hi hsplit ψ hψ),
    Classical.choose_spec (exists_actual_induction_irreducibility_factor χ A C hC qMeasure hG hsq hi hsplit ψ hψ)⟩

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  ambientMeasurable ambientBorel parabolicLocallyCompact

variable (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

include hG hK hψK in
/-- On an irreducible admissible normalized fiber, the actual induction of
the original smooth dual at the inverse parameter is irreducible as well. -/
theorem actualDualInduction_isIrreducible
    (z : X) (hAz : (twistObject χ z A).IsAdmissible)
    (hirr : (I z).representation.IsIrreducible) :
    (UnramifiedLeviInduction h hU (leviNormCharacters χ) (parameterTransport χ z⁻¹)
      A.contragredient).representation.IsIrreducible := by
  let hP := DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
  let hr := commonProjection_continuous χ ψ hψ
  have hI := induced_isAdmissible h hU K hK (iwasawa_sets K ψ hψK) (twistObject χ z A) hr hAz
  have hDual := (SmoothRep.isIrreducible_contragredient_iff
    (compactOpenCofinal_of_nonarchimedean (RationalPoint F G.X)) (I z) hI).mpr hirr
  let e := integralDualEquiv h hU hP hr K hK (iwasawa_sets K ψ hψK)
    (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) (twistObject χ z A) hAz
  let e' := normalizedInductionLeviEquiv h hU
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) (twistObject χ z A).contragredient
  exact (Langlands.isIrreducible_iff_of_equiv
    (e.trans (e'.trans (dualInductionEquiv χ hG ψ hψ A z)))).mp hDual

end Langlands.Plancherel.ActualCommonLeviV3
