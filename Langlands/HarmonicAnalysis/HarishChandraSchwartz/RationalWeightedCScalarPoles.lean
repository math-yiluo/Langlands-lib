import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeightedCDomain
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketDensity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionDensityNonzero
import Langlands.Representation.Plancherel.DynamicSquareIntegrableGalleryProduct
import Langlands.Representation.Plancherel.DynamicOppositeGalleryProduct
import Langlands.Representation.Plancherel.RationalOperatorPoleTransport

/-! # Pole presentation of the scalar in the actual weighted c-family -/

noncomputable section

set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

universe u uV

open UnramifiedOperatorFamily ValuationKernelCoordinates

section ReducedFraction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [TopologicalSpace (rationalPoints H)]
  (hp : Continuous (rationalValuationImageProjection H)) (hH : IsConnectedReductive H)

set_option hygiene false in
local notation "νH" => fun ψ => (rationalNormCharacters H ψ).toMul
local notation "R" => unramifiedRegularFunctions νH
local notation "L" => rationalUnramifiedFunctionField H hp hH

/-- In the Laurent UFD a reduced denominator divides every other denominator
of the same fraction. Its evaluation therefore decides regularity at every
parameter, not just on a chosen dense open set. -/
private theorem exists_reduced_regularFraction (f : L) :
    ∃ a b : R, b ≠ 0 ∧ (a ≠ 0 ↔ f ≠ 0) ∧
      (∀ z, RationalFunctionRegularAt H hp hH f z ↔ b.val z ≠ 0) ∧
      ∀ z (hz : RationalFunctionRegularAt H hp hH f z),
        rationalValueAt f hz = a.val z / b.val z := by
  let : IsDomain R := rationalUnramifiedRegularFunctions_isDomain H hp hH
  let : UniqueFactorizationMonoid R := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid H hp hH
  let a := IsFractionRing.num R f
  let b : R := IsFractionRing.den R f
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero (IsFractionRing.den R f).property
  have hcop : IsRelPrime a b := IsFractionRing.num_den_reduced R f
  have hf : f = algebraMap R L a / algebraMap R L b := (IsFractionRing.mk'_num_den' R f).symm
  have hreg (z) (hz : RationalFunctionRegularAt H hp hH f z) : b.val z ≠ 0 := by
    obtain ⟨m, n, hn, he⟩ := hz
    have hn₀ : n ≠ 0 := fun h => hn (by rw [h]; rfl)
    let i := algebraMap R L
    have hi := rationalUnramifiedFunctionField_algebraMap_injective H hp hH
    have hmap {d : R} (hd : d ≠ 0) : i d ≠ 0 := fun h => hd (hi (h.trans (map_zero i).symm))
    have hcross : a * n = m * b :=
      hi (by simpa only [map_mul] using (div_eq_div_iff (hmap hb) (hmap hn₀)).mp (hf.symm.trans he))
    obtain ⟨t, ht⟩ := hcop.symm.dvd_of_dvd_mul_left (by rw [hcross]; exact dvd_mul_left _ _)
    intro hz
    apply hn
    rw [ht]
    change b.val z * t.val z = 0
    rw [hz, zero_mul]
  exact ⟨a, b, hb, not_congr (IsFractionRing.num_eq_zero (A := R) f),
    fun z => ⟨hreg z, fun hz => ⟨a, b, hz, hf⟩⟩,
    fun z hz => rationalValueAt_eq hz (hreg z hz) hf⟩

/-- A fraction clears the value even where its displayed denominator vanishes,
provided the rational function is regular there. -/
private theorem rationalValueAt_clears_fraction {f : L} {a b : R} (hb : b ≠ 0)
    (hf : f = algebraMap R L a / algebraMap R L b)
    {z : unramifiedCharacters νH} (hz : RationalFunctionRegularAt H hp hH f z) :
    b.val z * rationalValueAt f hz = a.val z := by
  have h := hz
  obtain ⟨m, n, hn, hmn⟩ := h
  let i := algebraMap R L
  have hi := rationalUnramifiedFunctionField_algebraMap_injective H hp hH
  have hb' : i b ≠ 0 := (map_ne_zero_iff i hi).mpr hb
  have hn' : i n ≠ 0 := (map_ne_zero_iff i hi).mpr (fun h => hn (by rw [h]; rfl))
  have he : a * n = m * b := hi (by
    simpa only [map_mul] using (div_eq_div_iff hb' hn').mp (hf.symm.trans hmn))
  rw [rationalValueAt_eq hz hn hmn, ← mul_div_assoc, div_eq_iff hn]
  exact (congrArg (fun d : R => d.val z) (mul_comm b m)).trans
    (congrArg (fun d : R => d.val z) he.symm)

end ReducedFraction

section Package

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviPresentations DynamicCommonLeviComposition RationalPlancherelDensity RationalDynamicSource
open DynamicInducedOrbit

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ζ : cocharacterLattice T}
  {hRefl : RelativeRootReflectionExistenceStatement.{u}}
  {hCST : CentralSplitTorusCharacterStatement.{u}} {hG : IsConnectedReductive G}

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i

variable {A : SmoothRep.{0, u, uV} ℂ (levi χ)}
  (P : DensityPackage i ζ hRefl hCST hG A)

set_option hygiene false in
local notation "L" => parameterScheme χ
set_option hygiene false in
local notation "hp" => parameterProjection_continuous χ
set_option hygiene false in
local notation "hL" => parameterScheme_isConnectedReductive χ hG

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))} {sc : Tc.toGrp ⟶ L}
  (hs : IsSplitComponent sc)
  (C : Subgroup (levi χ)) [hCN : C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [mC : MeasurableSpace (levi χ ⧸ C)] [bC : BorelSpace (levi χ ⧸ C)]
  (mu : Measure (levi χ ⧸ C)) [hmu : mu.IsHaarMeasure]

include hs in
private theorem packageCanonicalScalar_rankOne
    (hA : A.IsIrreducible) (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu)
    (hj : P.canonicalScalar ≠ 0) :
    ∃ charts : List (RankOneTranslationChart L), HasDenseRankOneProduct L hL charts P.canonicalScalar := by
  have hg := hasDenseRepresentedGalleryProduct_of_squareIntegrable hG hs A hA C hC mu hsq
    P.K P.hK (oppositeGallerySource χ) (oppositeGalleryTarget χ)
  obtain ⟨charts, hcharts⟩ := exists_denseContinuedCompositeRankOneProduct_of_gallery
    χ hRefl hCST hG hs P.K P.hK P.hPK P.hOppK A P.p P.q
    P.hDForward P.hneForward P.hDForwardΩ P.hDReverse P.hneReverse P.hDReverseΩ hg
  exact ⟨charts, hasDenseRankOneProduct_of_continuedComposite χ hRefl hCST hG
    P.K P.hK P.hPK P.hOppK A P.p P.q P.hDForward P.hneForward P.hDForwardΩ
    P.hDReverse P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr charts hj hcharts⟩

set_option hygiene false in
local notation "RL" => unramifiedRegularFunctions (normCharacters χ)
set_option hygiene false in
local notation "KL" => rationalUnramifiedFunctionField L hp hL

private theorem divide_of_inverse_identity {a b c y : ℂ} (hc : c ≠ 0) (hy : y ≠ 0)
    (he : a * y = c * b) : b * y⁻¹ = c⁻¹ * a := by
  field_simp
  exact (mul_comm b c).trans (he.symm.trans (mul_comm a y))

private theorem packageDensityInverse_clears
    (charts : List (RankOneTranslationChart L))
    (hprod : HasDenseRankOneProduct L hL charts P.canonicalScalar)
    (hΓ : rankOneGammaProduct i ζ P.K P.hK ≠ ⊤) :
    ∃ a b : RL, Nonempty (RationalUnitaryPoleFactorization L b) ∧
      ∀ z (hz : RationalFunctionRegularAt L hp hL (packageDensity P) z),
        rationalValueAt (packageDensity P) hz ≠ 0 →
          b.val z * (rationalValueAt (packageDensity P) hz)⁻¹ = a.val z := by
  let jP : KL := P.canonicalScalar
  let E := algebraMap RL KL
  obtain ⟨a, b, κ, O, fs, hf, hd, ho, hi', hv⟩ := hprod
  obtain ⟨z, hz⟩ := hd.nonempty
  have ha : a ≠ 0 := fun h => (hv z hz).1 (by rw [h]; rfl)
  have hb : b ≠ 0 := fun h => (hv z hz).2.1 (by rw [h]; rfl)
  let q := RankOneScalarPolePresentation.ofDenseRankOneProduct L hL charts a b ha hb
    ⟨a, b, κ, O, fs, rfl, hd, ho, hi', hv⟩
  let : IsDomain RL := rationalUnramifiedRegularFunctions_isDomain L hp hL
  have hdq : q.denominator ≠ 0 := by
    rw [q.factors.factorization]
    apply mul_ne_zero
    · apply List.prod_ne_zero
      intro hz
      obtain ⟨r, _, hr⟩ := List.mem_map.mp hz
      exact r.factor_ne_zero L hL hr
    · intro he
      exact q.factors.remainder_nonzero 1 (by rw [he]; rfl)
  have hnq : q.numerator ≠ 0 := by
    intro he
    exact mul_ne_zero hdq ha (by rw [← q.cross, he, mul_zero])
  have hE := rationalUnramifiedFunctionField_algebraMap_injective L hp hL
  have hq : jP = E q.numerator / E q.denominator := by
    change P.canonicalScalar = _
    refine hf.trans ((div_eq_div_iff ((map_ne_zero_iff E hE).mpr hb)
      ((map_ne_zero_iff E hE).mpr hdq)).mpr ?_)
    have hcross : a * q.denominator = q.numerator * b :=
      (mul_comm a q.denominator).trans (q.cross.symm.trans (mul_comm b q.numerator))
    exact (map_mul E a q.denominator).symm.trans ((congrArg E hcross).trans (map_mul E q.numerator b))
  let c : ℂ := (plancherelDensityConstant i ζ P.K P.hK : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr
    (plancherelDensityConstant_pos i ζ P.K P.hK hΓ).ne'
  let cR := algebraMap ℂ RL c
  have hμ : packageDensity P = E (cR * q.denominator) / E q.numerator := by
    change E cR * jP⁻¹ = _
    rw [hq, inv_div, map_mul, mul_div_assoc]
  refine ⟨algebraMap ℂ RL c⁻¹ * q.numerator, q.denominator, ⟨q.factors⟩, ?_⟩
  intro w hw hvw
  have he := rationalValueAt_clears_fraction L hp hL hnq hμ hw
  change q.numerator.val w * rationalValueAt (packageDensity P) hw = c * q.denominator.val w at he
  change q.denominator.val w * (rationalValueAt (packageDensity P) hw)⁻¹ = c⁻¹ * q.numerator.val w
  exact divide_of_inverse_identity hc hvw he

end Package

private theorem regularProducts_clear {R : Type*} [CommSemiring R] (ev : R →+* ℂ)
    {a b c d : R} {x y : ℂ} (hx : ev b * x = ev a) (hy : ev d * y = ev c) :
    ev (b * d) * (x * y) = ev (a * c) := by
  rw [map_mul, map_mul, mul_mul_mul_comm, hx, hy]

section Weighted

open DynamicOppositeStandardIntertwining RationalPointFamily RationalDynamicSource

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance scalarPolesAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance scalarPolesLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance scalarPolesLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance scalarPolesLeviFiniteType (J : Set (characterLattice T)) :
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
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)
local instance scalarPolesPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "X" => unramifiedCharacters ν₀
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions ν₀
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => leviRationalUnramifiedCharacterHomeomorph i ν I
set_option hygiene false in
local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "g" => standardLeviParameterIso hG hi hν I hζ
set_option hygiene false in
local notation "s" => lowerParameterIso hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "zG" => standardLeviUnramifiedRestrict hG hi hν I hζ
set_option hygiene false in
local notation "zM" => fun z => (parameterTransport χs).symm
  (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)

include hG hi hν hζ hn in
private theorem lowerDensityParameter_eq (z : unramifiedCharacters νM) :
    zM z = rationalUnramifiedCharacterRestrict (s).hom ((Φ).symm z) := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro y
  let e := lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
    (rootSet_subset i ν I) ζ hζ n hn
  change z.val (e.symm (parameterHomeomorph χs y)) =
    z.val (eM (rationalPoints.map (s).hom y))
  exact congrArg (fun x : levi i ν I => z.val x)
    (Subtype.ext (leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn y).symm)

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)

open DynamicOppositeCanonicalScalar DynamicCommonLeviPresentations RationalPlancherelDensity

set_option hygiene false in
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "Ω" => Φ ⁻¹' interior D₀
/-- The exact scalar factor in `cWeightedCompactFamily`, on its published domain. -/
def cWeightedScalarAt (z : D₀) : ℂ :=
  rationalValueAt (packageDensity PG) z.property.2.1 *
    (rationalValueAt (packageDensity PM) z.property.2.2.fst)⁻¹

set_option hygiene false in
local notation "Dens(" z ")" => cWeightedScalarAt hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM z

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ M₀) (hs : IsSplitComponent sc)
set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "L" => parameterScheme χs
set_option hygiene false in
local notation "hcL" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "hL" => parameterScheme_isConnectedReductive χs hcL
set_option hygiene false in
local notation "hproj" => parameterProjection_continuous χs
set_option hygiene false in
local notation "A" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj
set_option hygiene false in
local notation "RL" => unramifiedRegularFunctions (normCharacters χs)
set_option hygiene false in
local notation "KL" => rationalUnramifiedFunctionField L hproj hL
set_option hygiene false in
local notation "PL" => lowerAmbient i ν (rootSet i ν I')

include hs in
private theorem lowerCanonicalScalar_rankOne
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu) :
    ∃ charts : List (RankOneTranslationChart L), HasDenseRankOneProduct L hL charts PM.canonicalScalar := by
  let a := lowerParameterSplitComponent hG hi hν I I' hζ n hn sc
  have ha := isSplitComponent_lowerParameterSplitComponent hG hi hν I I' hζ n hn sc hs
  let C := lowerCentral hG hi hν I I' hζ n hn CM
  let : C.Normal := lowerCentral_normal hG hi hν I I' hζ n hn CM
  let m := lowerMeasure hG hi hν I I' hζ n hn CM mu
  let hC := lowerCentral_le_center hG hi hν I I' hζ n hn CM hCM
  let hA := (lowerRepresentation hG hi hν I I' hζ n hn π).property.1
  have hq := lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq
  have hj := lowerDensityCanonicalScalarNonzero hG hi hν I I' hζ n hn sc hs π mu hRefl hCST PM hsq
  exact packageCanonicalScalar_rankOne PM (sc := a) ha C (hCN := lowerCentral_normal hG hi hν I I' hζ n hn CM)
    hC (mC := lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn CM)
    (bC := lowerQuotientBorelSpace hG hi hν I I' hζ n hn CM) m
    (hmu := lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn CM mu) hA hq hj

include hs in
private theorem lowerDensityInverse_clears
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu) :
    ∃ a b : RL, Nonempty (RationalUnitaryPoleFactorization L b) ∧
      ∀ z (hz : RationalFunctionRegularAt L hproj hL (packageDensity PM) z),
        rationalValueAt (packageDensity PM) hz ≠ 0 →
          b.val z * (rationalValueAt (packageDensity PM) hz)⁻¹ = a.val z := by
  obtain ⟨charts, hprod⟩ := lowerCanonicalScalar_rankOne hG hi hν I I' hζ n hn hRefl hCST π PM sc hs mu hsq
  let j := Standard.leviTorusHom i ν (rootSet i ν I')
  let ξ := conjugatedCocharacter i ζ n
  let : Smooth (PL).X.hom := (hcL).smooth
  let : ConnectedSpace (PL).X.left := (hcL).connectedSpace
  have hΓ := rankOneGammaProduct_ne_top_of_isSplitTorus j ξ PM.K PM.hK
    (lowerTorus_isMaximalSplitTorus hi I').1.1
  exact packageDensityInverse_clears PM charts hprod hΓ

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (normCharacters χG)
set_option hygiene false in
local notation "EG" => rationalUnramifiedRegularFunctionsEquiv (g)
set_option hygiene false in
local notation "EM" => rationalUnramifiedRegularFunctionsEquiv (s)

include hG hi hν hζ hn in
private theorem weightedCScalarAlternate_clears (aG bG : RG) (aM bM : RL)
    (z : X) (w : D₀) (hw : w.val = Φ z)
    (hg : bG.val (zG w.val) * rationalValueAt (packageDensity PG) w.property.2.1 = aG.val (zG w.val))
    (hm : bM.val (zM w.val) * (rationalValueAt (packageDensity PM) w.property.2.2.fst)⁻¹ = aM.val (zM w.val)) :
    (EG bG * EM bM).val z * Dens(w) = (EG aG * EM aM).val z := by
  have hpre : (Φ).symm w.val = z := (congrArg (Φ).symm hw).trans ((Φ).symm_apply_apply z)
  have hzg : zG w.val = rationalUnramifiedCharacterRestrict (g).hom z :=
    congrArg (rationalUnramifiedCharacterRestrict (g).hom) hpre
  have hzm : zM w.val = rationalUnramifiedCharacterRestrict (s).hom z :=
    (lowerDensityParameter_eq hG hi hν I I' hζ n hn w.val).trans
      (congrArg (rationalUnramifiedCharacterRestrict (s).hom) hpre)
  let vG := rationalValueAt (packageDensity PG) w.property.2.1
  let vM := (rationalValueAt (packageDensity PM) w.property.2.2.fst)⁻¹
  let ev := UnramifiedNormalized.evaluation ν₀ z
  have hGE (f : RG) : f.val (zG w.val) = ev (EG f) := congrArg f.val hzg
  have hME (f : RL) : f.val (zM w.val) = ev (EM f) := congrArg f.val hzm
  have hgclear : ev (EG bG) * vG = ev (EG aG) :=
    (congrArg (· * vG) (hGE bG).symm).trans (hg.trans (hGE aG))
  have hmclear : ev (EM bM) * vM = ev (EM aM) :=
    (congrArg (· * vM) (hME bM).symm).trans (hm.trans (hME aM))
  exact regularProducts_clear ev hgclear hmclear

include hs in
private theorem exists_weightedCScalarAlternate
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu) :
    ∃ a b : R, Nonempty (RationalUnitaryPoleFactorization M₀ b) ∧
      ∀ (z : X) (w : D₀), w.val = Φ z → b.val z * Dens(w) = a.val z := by
  let hLG := parameterScheme_isConnectedReductive χG hG
  let hpG := parameterProjection_continuous χG
  obtain ⟨aG, bG, _, _, hregG, hvalG⟩ := exists_reduced_regularFraction
    (parameterScheme χG) hpG hLG (packageDensity PG)
  have hreg := plancherelDensity_unitaryRegular i ζ hRefl hCST hG PG.K PG.hK PG.hPK PG.hOppK _
    PG.p PG.q PG.hneForward PG.hDForwardΩ PG.hneReverse PG.hDReverseΩ PG.hne PG.hirr PG.hreg
  have hBG := RationalUnitaryPoleFactorization.ofNonvanishing (parameterScheme χG) bG
    (fun z => (hregG (unitaryToUnramified (parameterScheme χG) z)).mp (hreg z))
  obtain ⟨aM, bM, ⟨hBM⟩, hvalM⟩ := lowerDensityInverse_clears hG hi hν I I' hζ n hn hRefl hCST π PM sc hs mu hsq
  refine ⟨EG aG * EM aM, EG bG * EM bM, ⟨(hBG.parameterPullback (g).symm).mul M₀
    (hBM.parameterPullback (s).symm)⟩, ?_⟩
  intro z w hw
  have hg : bG.val (zG w.val) * rationalValueAt (packageDensity PG) w.property.2.1 = aG.val (zG w.val) := by
    have hg0 := hvalG (zG w.val) w.property.2.1
    have hb0 := (hregG (zG w.val)).mp w.property.2.1
    rw [hg0, mul_comm, div_mul_cancel₀ _ hb0]
  have hm := hvalM (zM w.val) w.property.2.2.fst w.property.2.2.snd
  exact weightedCScalarAlternate_clears hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
    aG bG aM bM z w hw hg hm

include hs in
/-- The exact density ratio has a fraction valid on the entire weighted interior and an
alternative denominator with a unitary pole factorization. -/
theorem exists_weightedCScalarPolePresentation
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
    (hne : (Ω : Set X).Nonempty) :
    ∃ a b : R, (∀ z : (Ω : Set X), b.val z.val ≠ 0) ∧
      (∀ z : (Ω : Set X), Dens((⟨Φ z.val, interior_subset z.property⟩ : D₀)) = a.val z.val / b.val z.val) ∧
      Nonempty (RankOneScalarPolePresentation M₀ a b) := by
  obtain ⟨A₁, B₁, ⟨hB₁⟩, hclear⟩ := exists_weightedCScalarAlternate hG hi hν I I' hζ hζ' n hn
    K hK hRefl hCST π PG PM sc hs mu hsq
  obtain ⟨a₀, b₀, _, hD, hratio⟩ := weightedCScalarPresentation hG hi hν I I' hζ hζ' n hn K hK
    hRefl hCST π PG PM
  let E := unramifiedRegularFunctionsEquiv eM ν₀
  let a := E.symm a₀
  let b := E.symm b₀
  have hE (d : unramifiedRegularFunctions νM) (z : X) : (E.symm d).val z = d.val (Φ z) :=
    unramifiedRegularFunctionsEquiv_symm_apply eM ν₀ d z
  have hb (z : (Ω : Set X)) : b.val z.val ≠ 0 := by
    have h := (congrArg (fun D => Φ z.val ∈ D) hD).mp (interior_subset z.property)
    exact fun hz => h.2 ((hE b₀ z.val).symm.trans hz)
  have hfrac (z : (Ω : Set X)) : Dens((⟨Φ z.val, interior_subset z.property⟩ : D₀)) = a.val z.val / b.val z.val :=
    (hratio ⟨Φ z.val, interior_subset z.property⟩).trans
      (congrArg₂ (· / ·) (hE a₀ z.val).symm (hE b₀ z.val).symm)
  refine ⟨a, b, hb, hfrac, ⟨⟨A₁, B₁, hB₁, ?_⟩⟩⟩
  apply sub_eq_zero.mp
  exact rationalUnramifiedRegular_eq_zero_of_isOpen M₀ (continuous_rationalValuationImageProjection M₀)
    (lowerAmbient_isConnectedReductive hG hi hν I) (b * A₁ - B₁ * a)
    (isOpen_interior.preimage (Φ).continuous) hne (by
      intro w hw
      have hl := hclear w ⟨Φ w, interior_subset hw⟩ rfl
      have hr := hfrac ⟨w, hw⟩
      rw [hr] at hl
      have hh : (B₁.val w * a.val w) / b.val w = A₁.val w := (mul_div_assoc _ _ _).trans hl
      have he := (div_eq_iff (hb ⟨w, hw⟩)).mp hh
      change b.val w * A₁.val w - B₁.val w * a.val w = 0
      exact sub_eq_zero.mpr ((mul_comm _ _).trans he.symm))

end Weighted

end Langlands.HarishChandraSchwartz.WeakExpansion
