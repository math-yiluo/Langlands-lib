import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionRegularOperatorTransfer

/-! # Fixed-level seminorm control for actual weighted lower sections -/

noncomputable section

set_option maxRecDepth 8000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily
open Langlands.Induction Langlands.HarmonicAnalysis.TorusFourier

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weightedLevelAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weightedLevelLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weightedLevelLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weightedLevelLeviFiniteType (J : Set (characterLattice T)) :
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

-- `M_I(F)` as a subtype of `G(F)`, written as in `rationalInducedSmoothOrbitSections`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "eM" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hL" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "conjChar" => lowerCharacterConjugation hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "conjLevi" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "eL" => (DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs).toMulEquiv
set_option hygiene false in
local notation "JL" => Fin (rationalImageRank (parameterScheme χs))
set_option hygiene false in
local notation "JU" => Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν I)))

include hζ in
/-- From the lower torus to the original one, conjugation is an integer
monomial in the actual canonical circle coordinates. -/
theorem exists_monomial_lowerCharacterConjugation_symm :
    ∃ a : JU → JL → ℤ, ∀ w : JL → Circle,
      eM ((conjChar).symm ((eL).symm w)) = finiteTorusMonomial a w := by
  let e := leviRationalPointHomeomorph i ν I
  let ν₀ := fun ψ => (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) ψ).toMul
  let e₀ := unitaryUnramifiedCharactersHomeomorph e ν₀
  choose g hg using fun j : JU => exists_rationalCanonicalUnitaryCoordinate_eq_eval _
    (isConnectedReductive_leviScheme_rootSet hG hi hν I) j
  have he (j : JU) (z : unitaryUnramifiedCharacters νM) :
      (eM z j : ℂ) = (z.val (e (g j)) : ℂ) := by
    have h := hg j (e₀.symm z)
    change (eM z j : ℂ) = _ at h
    have heq := congrArg (fun z : unitaryUnramifiedCharacters νM => (z.val (e (g j)) : ℂ))
      (e₀.apply_symm_apply z)
    exact h.trans (by simpa only [e₀, unitaryUnramifiedCharactersHomeomorph_apply,
      ContinuousMulEquiv.symm_apply_apply] using heq)
  have hconj (z : unitaryUnramifiedCharacters (leviNormCharacters χs)) (m : 𝐌) :
      ((conjChar).symm z).val m = z.val (conjLevi m) := by
    obtain ⟨y, rfl⟩ := (conjChar).surjective z
    rw [ContinuousMulEquiv.symm_apply_apply, lowerCharacterConjugation_apply,
      ContinuousMulEquiv.symm_apply_apply]
  choose a ha using fun j : JU => DynamicInducedOrbit.leviUnitaryCoordinates_hasLaurent hL χs
    (conjLevi (e (g j)))
  refine ⟨a, fun w => ?_⟩
  funext j
  apply Circle.ext
  rw [he j, hconj, ha j]
  change ∏ k, ((w k ^ a j k : Circle) : ℂ) = ((∏ k, w k ^ a j k : Circle) : ℂ)
  exact (map_prod Circle.coeHom (fun k => w k ^ a j k) Finset.univ).symm

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "Udecomp" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "Uclosed" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "UpClosed" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "Unorm" => continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "Uproj" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) Udecomp
set_option hygiene false in
local notation "Ufactor" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "UpperPicture" => ProductInducedCompactPicture Udecomp K π.obj
set_option hygiene false in
local notation "UpperLevel[" H "]" => OrbitSectionLevel νM π eM Udecomp Uclosed K UpClosed hKc
  Unorm Uproj Ufactor H
set_option hygiene false in
local notation "upInclude[" H "]" => OrbitSectionLevel.toSections νM π eM Udecomp Uclosed K UpClosed
  hKc Unorm Uproj Ufactor H
set_option hygiene false in
local notation "upNorms[" H "]" => OrbitSectionLevel.seminormFamily νM π eM Udecomp Uclosed K UpClosed
  hKc Unorm Uproj Ufactor H

set_option hygiene false in
local notation "KL" => lowerK hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "KLc" => lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "Lfactor" => lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "πL" => lowerRepresentation hG hi hν I I' hζ n hn π
set_option hygiene false in
local notation "Ldecomp" => decomposition χs
set_option hygiene false in
local notation "Lclosed" => radical_isClosed χs
set_option hygiene false in
local notation "LpClosed" => parabolic_isClosed χs
set_option hygiene false in
local notation "Lnorm" => DynamicInducedOrbit.leviNormCharacters_continuous χs
set_option hygiene false in
local notation "Lproj" => projection_continuous χs
set_option hygiene false in
local notation "νL" => leviNormCharacters χs
set_option hygiene false in
local notation "LowerPicture" => ProductInducedCompactPicture Ldecomp KL (πL).obj
set_option hygiene false in
local notation "LowerLevel[" H "]" => OrbitSectionLevel νL πL eL Ldecomp Lclosed KL LpClosed KLc
  Lnorm Lproj Lfactor H
set_option hygiene false in
local notation "lowInclude[" H "]" => OrbitSectionLevel.toSections νL πL eL Ldecomp Lclosed KL LpClosed KLc
  Lnorm Lproj Lfactor H
set_option hygiene false in
local notation "lowNorms[" H "]" => OrbitSectionLevel.seminormFamily νL πL eL Ldecomp Lclosed KL LpClosed KLc
  Lnorm Lproj Lfactor H
set_option hygiene false in
local notation "restrictLower" => dynamicSectionCompactPicture (H := 𝐋) hL χs (K := KL) KLc Lfactor πL
set_option hygiene false in
local notation "Extension" => WeightedCExtension hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN
set_option hygiene false in
local notation "WeightedSection" => IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN
set_option hygiene false in
local notation "InputIndex" => List JU × Module.Dual ℂ UpperPicture
set_option hygiene false in
local notation "OutputIndex" => List JL × Module.Dual ℂ LowerPicture
set_option hygiene false in
local notation "LowerSections" => LowerSectionsAt hG hi hν I I' hζ π n hn hRefl hCST PM

set_option maxHeartbeats 1500000 in
private theorem weightedCSection_at_lowerCoordinates (E : Extension)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (Ψ : LowerSections) (hΨ : WeightedSection E q Ψ) (w : JL → Circle) :
    let z := (conjChar).symm
      ((DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs).symm w)
    restrictLower Ψ w = E.unitaryValue z (sectionCompactPicture hG hi hν I hKc hPK π q z) := by
  dsimp only
  have he := hΨ ((conjChar).symm
    ((DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs).symm w))
  simpa only [ContinuousMulEquiv.apply_symm_apply] using he

set_option maxHeartbeats 2200000 in
/-- The actual compact formula of a weighted lower section has the regular
operator form at the monomial image of its lower parameter. -/
theorem hasRegularOrbitSectionTransfer_of_weightedCSection
    (H : OpenSubgroup (rationalPoints G)) (E : Extension)
    (Ψ : UpperLevel[H] → LowerSections)
    (hΨ : ∀ q, WeightedSection E (upInclude[H] q) (Ψ q)) :
    ∃ a : JU → JL → ℤ,
      HasRegularOrbitSectionTransfer Udecomp Uclosed UpClosed K hKc Ufactor
        νM π Unorm Uproj eM H Ldecomp Lclosed LpClosed KL KLc Lfactor νL πL Lnorm Lproj eL
        a E.denominator E.numerator Ψ := by
  obtain ⟨a, ha⟩ := exists_monomial_lowerCharacterConjugation_symm hG hi hν I I' hζ n hn
  refine ⟨a, ?_⟩
  intro q w
  let z := (conjChar).symm
    ((DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hL χs).symm w)
  let R := productInducedSmoothOrbitCompactRestriction Udecomp Uclosed νM π K UpClosed
    hKc Unorm Uproj Ufactor eM (upInclude[H] q)
  have hmono : eM z = finiteTorusMonomial a w := ha w
  have hright : unitaryRegularOperator νM eM E.denominator E.numerator (eM z)
      (R (eM z)) =
      E.unitaryValue z (sectionCompactPicture hG hi hν I hKc hPK π (upInclude[H] q) z) := by
    simp only [unitaryRegularOperator, WeightedCExtension.unitaryValue, MulEquiv.symm_apply_apply]
    rfl
  have hleft : restrictLower (Ψ q) w = E.unitaryValue z
      (sectionCompactPicture hG hi hν I hKc hPK π (upInclude[H] q) z) :=
    weightedCSection_at_lowerCoordinates hG hi hν I I' hζ hζ' hKc hPK π n hn
      hRefl hCST PG PM hN E (upInclude[H] q) (Ψ q) (hΨ q) w
  have hfinal : restrictLower (Ψ q) w = unitaryRegularOperator νM eM E.denominator E.numerator
      (finiteTorusMonomial a w) (R (finiteTorusMonomial a w)) :=
    hleft.trans (hright.symm.trans
      (congrArg (fun y => unitaryRegularOperator νM eM E.denominator E.numerator y (R y)) hmono))
  exact hfinal

/-- The section does not depend on which regular extension is used in
the compact formula. -/
theorem isWeightedCSection_of_extension
    (E E' : Extension) (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (Ψ : LowerSections) (hΨ : WeightedSection E' q Ψ) : WeightedSection E q Ψ := by
  intro z
  exact (hΨ z).trans (LinearMap.congr_fun (E'.unitaryValue_eq E z)
    (sectionCompactPicture hG hi hν I hKc hPK π q z))

set_option maxHeartbeats 1200000 in
/-- One lower level contains the given family of sections, with every finite
supremum of lower seminorms controlled by original seminorms. -/
def HasWeightedCSectionLevelControl
    (H : OpenSubgroup (rationalPoints G)) (Ψ : UpperLevel[H] → LowerSections) : Prop :=
  ∃ (H' : OpenSubgroup (RationalPoint F 𝐋.X)), H' ≤ KL ∧
    ∃ (T : UpperLevel[H] → LowerLevel[H']),
      (∀ q, lowInclude[H'] (T q) = Ψ q) ∧
      ∀ t : Finset OutputIndex, ∃ s : Finset InputIndex, ∃ c : ℝ≥0,
        ∀ q, (t.sup lowNorms[H']) (T q) ≤ (c : ℝ) * (s.sup upNorms[H]) q

set_option maxHeartbeats 2500000 in
/-- A weighted c-extension gives the fixed-level control for all of its
actual lower sections over the original level. -/
theorem hasWeightedCSectionLevelControl_of_weightedCSection
    (H : OpenSubgroup (rationalPoints G)) (hHK : H ≤ K) (E : Extension)
    (Ψ : UpperLevel[H] → LowerSections)
    (hΨ : ∀ q, WeightedSection E (upInclude[H] q) (Ψ q)) :
    HasWeightedCSectionLevelControl hG hi hν I I' hζ hKc hPK π n hn hRefl hCST PM H Ψ := by
  obtain ⟨a, ha⟩ := hasRegularOrbitSectionTransfer_of_weightedCSection
    hG hi hν I I' hζ hζ' hKc hPK π n hn hRefl hCST PG PM hN H E Ψ hΨ
  exact exists_regularOrbitSectionTransfer_finsetSup_bound Udecomp Uclosed UpClosed K hKc Ufactor
    νM π Unorm Uproj eM H Ldecomp Lclosed LpClosed KL KLc Lfactor νL πL Lnorm Lproj eL
    a E.denominator E.numerator Ψ hHK
    (compactOpenCofinal_of_isClosed (isClosed_standardLeviPoints i ν (rootSet i ν I)))
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I) E.unitary_regular E.polynomial ha

end WeakExpansion

end Langlands.HarishChandraSchwartz
