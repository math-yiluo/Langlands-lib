import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.Representation.Plancherel.RationalUnramifiedFactorization
import Langlands.Representation.Plancherel.UnramifiedOperatorTransport
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite
import Mathlib.RingTheory.Localization.NumDen

/-! # The scalar fraction and domain of the actual weighted c-family -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

universe u uV

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
private theorem exists_fraction_on_regular_locus (f : L) :
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

end ReducedFraction

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H S : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] [IsAffine S.X.left]

local instance fractionTransportTopologyH : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
local instance fractionTransportTopologyS : TopologicalSpace (rationalPoints S) := rationalPointTopology F S.X

variable {M : Type u} [Group M] [TopologicalSpace M]
  (e : H ≅ S) (eM : rationalPoints S ≃ₜ* M)

set_option hygiene false in
local notation "νS" => fun ψ => (rationalNormCharacters S ψ).toMul
set_option hygiene false in
local notation "νH" => fun ψ => (rationalNormCharacters H ψ).toMul
set_option hygiene false in
local notation "νM" => fun ψ => (νS ψ).comp eM.symm.toMulEquiv.toMonoidHom

/-- Transport regular scalars first to a scheme representative, then to its literal
point subgroup. The two precompositions are by the indicated character transports. -/
private def fractionTransport : unramifiedRegularFunctions νH ≃ₐ[ℂ] unramifiedRegularFunctions νM :=
  (rationalUnramifiedRegularFunctionsEquiv e).trans (unramifiedRegularFunctionsEquiv eM νS)

private theorem fractionTransport_val (a : unramifiedRegularFunctions νH)
    (z : unramifiedCharacters νM) :
    (fractionTransport e eM a).val z = a.val (rationalUnramifiedCharacterRestrict e.hom
      ((unramifiedCharactersHomeomorph eM νS).symm z)) := rfl

end Transport

section Weighted

open DynamicOppositeStandardIntertwining RationalPointFamily RationalDynamicSource

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weightedDomainAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weightedDomainLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weightedDomainLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weightedDomainLeviFiniteType (J : Set (characterLattice T)) :
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
local instance weightedDomainPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "X" => unramifiedCharacters νM
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions νM
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
private theorem lowerDensityParameter_eq (z : X) :
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

set_option hygiene false in
local notation "D" => cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj
set_option hygiene false in
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM

include hG hi hν hζ hn in
private theorem lowerPackageDensity_ne_zero_iff : packageDensity PM ≠ 0 ↔ PM.canonicalScalar ≠ 0 := by
  let j := Standard.leviTorusHom i ν (rootSet i ν I')
  let ξ := conjugatedCocharacter i ζ n
  let hL := lowerAmbient_isConnectedReductive hG hi hν I'
  let A := (lowerRepresentation hG hi hν I I' hζ n hn π).obj
  let : Smooth (lowerAmbient i ν (rootSet i ν I')).X.hom := hL.smooth
  let : ConnectedSpace (lowerAmbient i ν (rootSet i ν I')).X.left := hL.connectedSpace
  exact not_congr (RationalPlancherelDensity.plancherelDensity_eq_zero_iff j ξ hRefl hCST hL
    PM.K PM.hK PM.hPK PM.hOppK A PM.p PM.q PM.hneForward PM.hDForwardΩ PM.hneReverse
    PM.hDReverseΩ PM.hne PM.hirr (rankOneGammaProduct_ne_top_of_isSplitTorus j ξ PM.K PM.hK
      (lowerTorus_isMaximalSplitTorus hi I').1.1))

/-- The two density conditions of `cWeightedDomain` amount to one principal-open
condition, and the scalar weight is a regular-function quotient everywhere on that domain.
Its denominator is not identically zero exactly when the lower canonical scalar is not. -/
def WeightedCScalarPresentationStatement : Prop :=
  ∃ a b : R, (b ≠ 0 ↔ PM.canonicalScalar ≠ 0) ∧
    D₀ = D ∩ {z : X | b.val z ≠ 0} ∧
    ∀ z : D₀, rationalValueAt (packageDensity PG) z.property.2.1 *
      (rationalValueAt (packageDensity PM) z.property.2.2.fst)⁻¹ = a.val z.val / b.val z.val

private theorem density_ratio_algebra (ag bg am bm : ℂ) (hg : bg ≠ 0) (ha : am ≠ 0) (hb : bm ≠ 0) :
    ag / bg * (am / bm)⁻¹ = (ag * (bm * bm)) / (bg * (bm * am)) := by
  field_simp

/-- Choose reduced fractions, pull their regular coefficients to the literal Levi,
and keep all three original nonvanishing conditions in the denominator. -/
theorem weightedCScalarPresentation :
    WeightedCScalarPresentationStatement hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM := by
  obtain ⟨aG, bG, hbG, _, hGr, hGv⟩ := exists_fraction_on_regular_locus (parameterScheme χG)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χG)
    (parameterScheme_isConnectedReductive χG hG) (packageDensity PG)
  obtain ⟨aM, bM, hbM, haM, hMr, hMv⟩ := exists_fraction_on_regular_locus (parameterScheme χs)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χs)
    (parameterScheme_isConnectedReductive χs (lowerAmbient_isConnectedReductive hG hi hν I'))
    (packageDensity PM)
  let E_G : unramifiedRegularFunctions (normCharacters χG) ≃ₐ[ℂ] R := fractionTransport g eM
  let E_M : unramifiedRegularFunctions (normCharacters χs) ≃ₐ[ℂ] R := fractionTransport s eM
  let A_G := E_G aG
  let B_G := E_G bG
  let A_M := E_M aM
  let B_M := E_M bM
  let a := A_G * (B_M * B_M)
  let b := B_G * (B_M * A_M)
  have hM_num (z : X) : aM.val (zM z) = A_M.val z :=
    (congrArg aM.val (lowerDensityParameter_eq hG hi hν I I' hζ n hn z)).trans
      (fractionTransport_val s eM aM z).symm
  have hM_den (z : X) : bM.val (zM z) = B_M.val z :=
    (congrArg bM.val (lowerDensityParameter_eq hG hi hν I I' hζ n hn z)).trans
      (fractionTransport_val s eM bM z).symm
  have hD : D₀ = D ∩ {z : X | b.val z ≠ 0} := by
    ext z
    constructor
    · rintro ⟨hz, hrG, hrM, hvM⟩
      have hg : B_G.val z ≠ 0 := (hGr (zG z)).mp hrG
      have hm : B_M.val z ≠ 0 := hM_den z ▸ (hMr (zM z)).mp hrM
      have ha : A_M.val z ≠ 0 := by
        intro h
        apply hvM
        exact (hMv (zM z) hrM).trans (by rw [hM_num z, h, zero_div])
      exact ⟨hz, mul_ne_zero hg (mul_ne_zero hm ha)⟩
    · rintro ⟨hz, hb⟩
      change B_G.val z * (B_M.val z * A_M.val z) ≠ 0 at hb
      have hrG := (hGr (zG z)).mpr (left_ne_zero_of_mul hb)
      have hrM := (hMr (zM z)).mpr ((hM_den z).symm ▸ left_ne_zero_of_mul (right_ne_zero_of_mul hb))
      refine ⟨hz, hrG, hrM, ?_⟩
      have he := (hMv (zM z) hrM).trans (congrArg₂ (· / ·) (hM_num z) (hM_den z))
      exact fun h => div_ne_zero (right_ne_zero_of_mul (right_ne_zero_of_mul hb))
        (left_ne_zero_of_mul (right_ne_zero_of_mul hb)) (he.symm.trans h)
  refine ⟨a, b, ?_, hD, ?_⟩
  · let : IsDomain (unramifiedRegularFunctions (normCharacters χs)) :=
      rationalUnramifiedRegularFunctions_isDomain (parameterScheme χs)
        (DynamicOppositeCanonicalScalar.parameterProjection_continuous χs)
        (parameterScheme_isConnectedReductive χs (lowerAmbient_isConnectedReductive hG hi hν I'))
    let : IsDomain R := E_M.symm.toMulEquiv.isDomain _
    have hA_M : A_M ≠ 0 ↔ aM ≠ 0 := map_ne_zero_iff E_M E_M.injective
    have hB_G : B_G ≠ 0 := (map_ne_zero_iff E_G E_G.injective).mpr hbG
    have hB_M : B_M ≠ 0 := (map_ne_zero_iff E_M E_M.injective).mpr hbM
    have hB : b ≠ 0 ↔ A_M ≠ 0 := by
      exact ⟨fun h => right_ne_zero_of_mul (right_ne_zero_of_mul h),
        fun h => mul_ne_zero hB_G (mul_ne_zero hB_M h)⟩
    exact hB.trans (hA_M.trans (haM.trans (lowerPackageDensity_ne_zero_iff hG hi hν I I' hζ n hn
      hRefl hCST π PM)))
  · intro z
    have hz : z.val ∈ D ∩ {z : X | b.val z ≠ 0} :=
      Eq.mp (congrArg (fun U : Set X => z.val ∈ U) hD) z.property
    have hb : B_G.val z.val * (B_M.val z.val * A_M.val z.val) ≠ 0 := hz.2
    have hg := hGv (zG z.val) z.property.2.1
    have hm := (hMv (zM z.val) z.property.2.2.fst).trans
      (congrArg₂ (· / ·) (hM_num z.val) (hM_den z.val))
    exact (congrArg₂ (fun x y : ℂ => x * y⁻¹) hg hm).trans
      (density_ratio_algebra (A_G.val z.val) (B_G.val z.val) (A_M.val z.val) (B_M.val z.val)
        (left_ne_zero_of_mul hb) (right_ne_zero_of_mul (right_ne_zero_of_mul hb))
        (left_ne_zero_of_mul (right_ne_zero_of_mul hb)))

include hG hi hν in
private theorem dense_literalRegular_ne_zero (b : R) (hb : b ≠ 0) :
    Dense {z : X | b.val z ≠ 0} := by
  let ν₀ := fun ψ => (rationalNormCharacters M₀ ψ).toMul
  let e : unramifiedRegularFunctions ν₀ ≃ₐ[ℂ] R := unramifiedRegularFunctionsEquiv eM ν₀
  let b₀ := e.symm b
  have hb₀ := (map_ne_zero_iff e.symm e.symm.injective).mpr hb
  have hd := rationalUnramifiedRegular_dense_nonzero M₀ (continuous_rationalValuationImageProjection M₀)
    (lowerAmbient_isConnectedReductive hG hi hν I) b₀ hb₀
  apply (hd.preimage (Φ).symm.isOpenMap).mono
  intro z hz
  have he : b.val z = b₀.val ((Φ).symm z) :=
    congrArg (fun c : R => c.val z) (e.apply_symm_apply b).symm
  exact fun h => hz (he.symm.trans h)

/-- Removing the two density exceptional loci does not empty any open
convergence region, provided the lower canonical scalar is not identically
zero. Conversely both conditions are necessary. -/
theorem cWeightedDomain_interior_nonempty_iff :
    (interior D₀).Nonempty ↔ (interior D).Nonempty ∧ PM.canonicalScalar ≠ 0 := by
  obtain ⟨_, b, hb, hD, _⟩ := weightedCScalarPresentation hG hi hν I I' hζ hζ' n hn K hK hRefl
    hCST π PG PM
  let U : Set X := {z | b.val z ≠ 0}
  constructor
  · intro h
    have hs : D₀ ⊆ D := fun _ hz => hz.1
    refine ⟨h.mono (interior_mono hs), hb.mp ?_⟩
    obtain ⟨z, hz⟩ := h
    have hz' : z ∈ D ∩ U := Eq.mp (congrArg (fun S : Set X => z ∈ S) hD) (interior_subset hz)
    exact fun h0 => hz'.2 (by rw [h0]; rfl)
  · rintro ⟨h, hj⟩
    have hd := dense_literalRegular_ne_zero hG hi hν I b (hb.mpr hj)
    have ho : IsOpen U := isOpen_ne_fun (continuous_unramifiedRegularFunction νM b) continuous_const
    have hne := (dense_iff_inter_open.mp hd) (interior D) isOpen_interior h
    refine hne.mono (interior_maximal ?_ (isOpen_interior.inter ho))
    intro z hz
    exact Eq.mpr (congrArg (fun S : Set X => z ∈ S) hD) ⟨interior_subset hz.1, hz.2⟩

end Weighted

end Langlands.HarishChandraSchwartz.WeakExpansion
