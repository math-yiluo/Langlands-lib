import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketSchwartz
import Langlands.Geometry.Building.SpecialCompact
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.Geometry.Building.KPApartmentAxioms

/-! # Targets: the weighted weak-constant-term expansion (Waldspurger V.1.1, V.2.3)

Named Prop-valued targets, unproved here:

* `WeightedCRegularityStatement`: `c̃_{P'|P}(s, ·)` extends to a rational family regular on `O`
  (Corollary V.2.3);
* `WeightedWeakExpansionStatement`: at every `ω ∈ O` and `m' ∈ M'(F)`,
  `µ^G(ω)(f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω)(E^{M'}_{M'∩s·P} c̃_{P'|P}(s, ω)q_ω)(m')`
  (Proposition V.1.1 in the form of printed p.304);
* `WeightedCDecompositionStatement`: the finite decomposition of p.304 of `c̃(s, ω)q_ω` into
  smooth multiples of specializations of fixed polynomial (algebraic) lower families;
* `WeightedPacketIdentityStatement`: the orbit integral of the weighted weak constant terms is the
  sum over `s` of the `µ^{M'}`-weighted lower wave packets of the sections `sω ↦ c̃(s, ω)q_ω`.

The values of `c̃` on `O` are those of a rational continuation `WeightedCExtension` that agrees
with `c̃` on the nonempty interior of its domain `cWeightedDomain`; these values do not depend on
the continuation (`WeightedCExtension.unitaryValue_eq`, proved). `IsWeightedCSection` identifies
the lower sections. All four targets assume that `π` is square integrable modulo `A_M(F)`, that
`K` is the special maximal compact subgroup of the source (`IsSpecialVertexCompact`: the compact
stabilizer of a special vertex of an apartment of the maximal split torus satisfying the Library's
apartment axioms, with the published special compact properties) and the common source normalization (`SourceCompactNormalization`:
`µ^G` at `K`, every `µ^{M'}` at `K ∩ M'(F)`); the two identities also assume that the normalizer
lifts lie in `K` (`LiftsInCompact`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance targetsAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance targetsLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance targetsLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance targetsLeviFiniteType (J : Set (characterLattice T)) :
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

/-! ### The identity theorem on `X(M_I)` -/

section Identity

/-- **Identity theorem on `X(M_I)`**: a polynomial family of vectors on the unramified characters
of the literal standard Levi subgroup `M_I(F)` that vanishes on a nonempty open set vanishes
identically. Transported from the actual Levi scheme. -/
theorem leviPolynomial_eq_zero_of_isOpen
    (hM : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : unramifiedCharacters (leviRationalNormCharacters i ν I) → V)
    (hf : UnramifiedOperatorFamily.IsPolynomialOn Set.univ (fun χ => f χ.val))
    {D : Set (unramifiedCharacters (leviRationalNormCharacters i ν I))}
    (hD : IsOpen D) (hne : D.Nonempty) (hz : ∀ χ ∈ D, f χ = 0)
    (χ : unramifiedCharacters (leviRationalNormCharacters i ν I)) : f χ = 0 := by
  let _ : TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
    rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X
  let ν₀ := fun ψ => (rationalNormCharacters (Standard.leviScheme i ν (rootSet i ν I)) ψ).toMul
  let Φ : unramifiedCharacters ν₀ ≃ₜ* unramifiedCharacters (leviRationalNormCharacters i ν I) :=
    unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I) ν₀
  have hf' := (UnramifiedOperatorFamily.isPolynomialOn_transport_iff
    (leviRationalPointHomeomorph i ν I) ν₀ Set.univ (fun χ => f χ.val)).mpr hf
  have h0 := rationalUnramifiedPolynomial_eq_zero_of_isOpen
    (Standard.leviScheme i ν (rootSet i ν I))
    (continuous_rationalValuationImageProjection _) hM (D := Φ ⁻¹' D)
    (hD.preimage Φ.continuous)
    (by
      obtain ⟨x, hx⟩ := hne
      refine ⟨Φ.symm x, ?_⟩
      show Φ (Φ.symm x) ∈ D
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact hx)
    (fun _ _ => Set.mem_univ _) _ hf' (fun ψ hψ => hz _ hψ)
  have h1 := h0 ⟨Φ.symm χ, Set.mem_univ _⟩
  have h2 : (unramifiedParameterPreimageEquiv (leviRationalPointHomeomorph i ν I) ν₀ Set.univ
      ⟨Φ.symm χ, Set.mem_univ _⟩).val = χ := by
    rw [unramifiedParameterPreimageEquiv_apply]
    exact ContinuousMulEquiv.apply_symm_apply _ χ
  rw [← h2]
  exact h1

/-- **Uniqueness of rational continuations from an open set on `X(M_I)`**: if two pairs
`(N, d)` and `(N', d')` of a global polynomial numerator and a regular denominator both clear a
family `A` on the interior of its domain `D₀`, and that interior is nonempty, then `d' N = d N'`
everywhere, so `N/d = N'/d'` wherever both denominators are nonzero. -/
theorem leviRationalContinuation_value_eq
    (hM : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {D₀ : Set (unramifiedCharacters (leviRationalNormCharacters i ν I))}
    (hint : (interior D₀).Nonempty) (A : D₀ → V →ₗ[ℂ] W)
    (d d' : unramifiedRegularFunctions (leviRationalNormCharacters i ν I))
    (N N' : unramifiedCharacters (leviRationalNormCharacters i ν I) → V →ₗ[ℂ] W)
    (hN : UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ (fun χ => N χ.val))
    (hN' : UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ (fun χ => N' χ.val))
    (hc : ∀ z (hz : z ∈ interior D₀), N z = d.val z • A ⟨z, interior_subset hz⟩)
    (hc' : ∀ z (hz : z ∈ interior D₀), N' z = d'.val z • A ⟨z, interior_subset hz⟩)
    (z : unramifiedCharacters (leviRationalNormCharacters i ν I))
    (hd : d.val z ≠ 0) (hd' : d'.val z ≠ 0) :
    (d.val z)⁻¹ • N z = (d'.val z)⁻¹ • N' z := by
  have hcross : d'.val z • N z = d.val z • N' z := by
    apply LinearMap.ext
    intro v
    have hpoly : UnramifiedOperatorFamily.IsPolynomialOn Set.univ
        (fun χ : (Set.univ : Set (unramifiedCharacters (leviRationalNormCharacters i ν I))) =>
          d'.val χ.val • N χ.val v - d.val χ.val • N' χ.val v) :=
      UnramifiedOperatorFamily.IsPolynomialOn.sub ((hN v).regular_smul d')
        ((hN' v).regular_smul d)
    have h0 := leviPolynomial_eq_zero_of_isOpen I hM
      (fun χ => d'.val χ • N χ v - d.val χ • N' χ v) hpoly isOpen_interior hint
      (by
        intro χ hχ
        simp only [hc χ hχ, hc' χ hχ, LinearMap.smul_apply, smul_smul, mul_comm (d'.val χ)]
        exact sub_self _) z
    simpa only [LinearMap.smul_apply, sub_eq_zero] using h0
  calc (d.val z)⁻¹ • N z = (d.val z)⁻¹ • (d'.val z)⁻¹ • (d'.val z • N z) := by
        rw [smul_smul (d'.val z)⁻¹, inv_mul_cancel₀ hd', one_smul]
    _ = (d.val z)⁻¹ • (d'.val z)⁻¹ • (d.val z • N' z) := by rw [hcross]
    _ = (d'.val z)⁻¹ • N' z := by
        rw [smul_smul (d'.val z)⁻¹, smul_smul, mul_comm (d'.val z)⁻¹, ← mul_assoc,
          inv_mul_cancel₀ hd, one_mul]

end Identity

/-! ### Rational extensions of the weighted c-family -/

section Extension

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

-- `M'`, written as `lowerAmbient` (the form of the lower cocharacter `χ_s`); every lower object
-- below is written in this form.
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

/-- The compact open subgroup of the lower density package, read in `M'(F)`. -/
def lowerK : OpenSubgroup (RationalPoint F 𝐋.X) := PM.K

theorem lowerK_isCompact : IsCompact (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM :
    Set (RationalPoint F 𝐋.X)) :=
  PM.hK

/-- The Iwasawa factorization of the lower density package, for the parabolic `M' ∩ s·P` of the
lower cocharacter `χ_s`. -/
theorem lowerPackage_iwasawa (g : RationalPoint F 𝐋.X) :
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs,
      ∃ k : lowerK hG hi hν I I' hζ n hn hRefl hCST π PM,
        g = (p : RationalPoint F 𝐋.X) * (k : RationalPoint F 𝐋.X) :=
  PM.hPK g

set_option maxHeartbeats 1600000 in
/-- **The weighted c-family on the fixed compact pictures** (`cWeightedCompactFamily`), with the
lower compact open subgroup of the density package, under the common source normalization `hN`
(so that this subgroup is `K ∩ M'(F)`). -/
def weightedCompactFamily
    (z : cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM) :
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
        (SmoothRep.pullback (eₛ).symm π.obj) :=
  cWeightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
    (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
    (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM) π PG PM hN z

set_option maxHeartbeats 1600000 in
/-- **A rational extension of `c̃_{P'|P}(s, ·)` regular on the whole orbit** (Waldspurger IV.1,
V.2.3). The interior `D₀°` of the fixed domain `D₀ = cWeightedDomain` of the weighted c-family is
nonempty; a global polynomial numerator `N` and a regular denominator `d` satisfy
`N(z) = d(z) c̃(s, π ⊗ z)` on the compact pictures at every `z ∈ D₀°`; and `d` vanishes at no
unitary character. The domain `D₀` is the same for all extensions, and the values `N/d` of two
extensions agree wherever both denominators are nonzero (`unitaryValue_eq`). -/
structure WeightedCExtension where
  /-- The interior of the domain of the weighted c-family is nonempty. -/
  interior_nonempty :
    (interior (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)).Nonempty
  /-- The regular denominator. -/
  denominator : unramifiedRegularFunctions νM
  /-- The global polynomial numerator. -/
  numerator : unramifiedCharacters νM →
    ProductInducedCompactPicture
        (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj →ₗ[ℂ]
      ProductInducedCompactPicture (decomposition χs) (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM)
        (SmoothRep.pullback (eₛ).symm π.obj)
  polynomial : UnramifiedOperatorFamily.IsPolynomialOperatorOn Set.univ (fun χ => numerator χ.val)
  /-- The numerator clears the denominator of `c̃` on the interior of its domain. -/
  clears : ∀ z (hz : z ∈ interior (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)),
    numerator z = denominator.val z •
      weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN
        ⟨z, interior_subset hz⟩
  /-- Regularity at every point of the unitary orbit. -/
  unitary_regular : ∀ z : unitaryUnramifiedCharacters νM,
    denominator.val ⟨z.val, z.property.1⟩ ≠ 0

namespace WeightedCExtension

variable {hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN}

/-- The value `c̃(s, π ⊗ z) = d(z)⁻¹ N(z)` of the extension at a unitary character `z`, on the
compact pictures. -/
def unitaryValue
    (E : WeightedCExtension hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN)
    (z : unitaryUnramifiedCharacters νM) :=
  (E.denominator.val ⟨z.val, z.property.1⟩)⁻¹ • E.numerator ⟨z.val, z.property.1⟩

set_option maxHeartbeats 1600000 in
/-- **The unitary values do not depend on the extension**: two rational extensions of
`c̃(s, ·)` have the same value at every unitary character. -/
theorem unitaryValue_eq
    (E E' : WeightedCExtension hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN)
    (z : unitaryUnramifiedCharacters νM) :
    E.unitaryValue z = E'.unitaryValue z :=
  leviRationalContinuation_value_eq I (lowerAmbient_isConnectedReductive hG hi hν I)
    E.interior_nonempty
    (fun z => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN z)
    E.denominator E'.denominator E.numerator E'.numerator E.polynomial E'.polynomial
    E.clears E'.clears _ (E.unitary_regular z) (E'.unitary_regular z)

end WeightedCExtension

end Extension

/-! ### Compact pictures of sections for an actual dynamic parabolic -/

section Dynamic

variable {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H) (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H)
  {K : OpenSubgroup (RationalPoint F H.X)} (hK : IsCompact (K : Set (RationalPoint F H.X)))
  (hPK : ∀ g : RationalPoint F H.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F H.X) * (k : RationalPoint F H.X))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi χ))

/-- The compact picture `Ψ_{π ⊗ z}|_{K × K}` of a section of `C^∞(O, P(χ))` (module
`DynamicInducedOrbitWavePacket`) at the unitary character of `Z_H(χ)(F)` with circle coordinates
`w` (`DynamicInducedOrbit.leviUnitaryCoordinates`): the Library's compact restriction of the
parameter pullback of the section. -/
def dynamicSectionCompactPicture
    (Ψ : DynamicInducedOrbit.inducedSmoothOrbitSections hH χ hK hPK π)
    (w : Fin (rationalImageRank (parameterScheme χ)) → Circle) :
    ProductInducedCompactPicture (decomposition χ) K π.obj :=
  productInducedFamilyRestriction (leviNormCharacters χ)
    (DynamicInducedOrbit.leviUnitaryCoordinates hH χ).toMulEquiv (decomposition χ) K
    (DynamicOppositeCanonicalScalar.parabolic_isClosed χ) hK
    (DynamicInducedOrbit.leviNormCharacters_continuous χ)
    (DynamicOppositeCanonicalScalar.projection_continuous χ) (radical_isClosed χ) hPK π.obj
    (productInducedOrbitPullback (leviNormCharacters χ) π
      (DynamicInducedOrbit.leviUnitaryCoordinates hH χ).toMulEquiv (decomposition χ)
      (radical_isClosed χ) Ψ.val) w

end Dynamic

/-! ### Compact pictures of upper and lower sections -/

section Sections

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

/-- The compact picture `q_{π ⊗ z}|_{K × K}` of a section `q ∈ C^∞(O, P)` at the unitary
character `z` of `M_I(F)`: the Library's compact restriction of the parameter pullback of `q`,
at the circle coordinates of `z`. -/
def sectionCompactPicture (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (z : unitaryUnramifiedCharacters νM) :
    ProductInducedCompactPicture
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K π.obj :=
  productInducedFamilyRestriction νM eM
    (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
    (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) π.obj
    (productInducedOrbitPullback νM π eM
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (rootSet i ν I)) q.val) (eM z)

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

/-- The lower smooth sections `C^∞(sO, M' ∩ s·P)` (module `DynamicInducedOrbitWavePacket` for
`H = M'`, the lower cocharacter `χ_s`, the representation `sπ` and the compact open subgroup of
the lower density package). -/
abbrev LowerSectionsAt :=
  DynamicInducedOrbit.inducedSmoothOrbitSections (H := 𝐋) hM' χs
    (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
    (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM)
    (lowerRepresentation hG hi hν I I' hζ n hn π)

set_option maxHeartbeats 2000000 in
/-- **The lower section `sω ↦ c̃_{P'|P}(s, ω) q_ω`** (Waldspurger p.304): `Ψ` is the lower section
of `c̃(s, ·) q` for the extension `E` when, for every unitary character `z` of `M_I(F)`, the
compact picture of `Ψ` at the conjugate `sz` (`lowerCharacterConjugation`, read in the circle
coordinates of `Im X(s·M)`) is the value at `z` of the extension applied to the compact picture
of `q` at `z`. -/
def IsWeightedCSection
    (E : WeightedCExtension hG hi hν I I' hζ hζ' n hn K hKc hRefl hCST hPK π PG PM hN)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (Ψ : LowerSectionsAt hG hi hν I I' hζ π n hn hRefl hCST PM) : Prop :=
  ∀ z : unitaryUnramifiedCharacters νM,
    dynamicSectionCompactPicture (H := 𝐋) hM' χs
        (lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM)
        (lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM)
        (lowerRepresentation hG hi hν I I' hζ n hn π) Ψ
        (DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hM' χs
          (lowerCharacterConjugation hG hi hν I I' hζ n hn z)) =
      E.unitaryValue z (sectionCompactPicture hG hi hν I hKc hPK π q z)

end Sections

/-! ### The special maximal compact subgroup -/

section Special

variable (ν) in
/-- **`K` is the special maximal compact subgroup of the source** (Waldspurger I.1, printed
p.240: the fixer of a special point of the apartment of `A_0` in the building): there are the
actual centralizer `C` of the maximal split torus `i` and apartment data `D` for `i` satisfying
the Kaletha–Prasad apartment axioms of the Library (`SatisfiesApartmentAxioms C`, and Axiom 4.1.2
`HasBoundedOpenStabilizers`), and a special vertex `x` of the apartment whose compact stabilizer
`K_x = G(F)^1 ∩ Stab(x)` has the published special compact properties (bounded, compact, open and
maximal, Weyl representatives in `K_x`, and `K_x ∩ P_J = (K_x ∩ M_J)(K_x ∩ U_J)` for every `J`),
and `K = K_x`. These are the conjuncts of the published existence target
`SpecialMaximalCompactExistence` (without its Levi clause). The properties of `K_x` are required
because the Library proves none of them from the apartment data. -/
def IsSpecialVertexCompact (K : OpenSubgroup (rationalPoints G)) : Prop :=
  haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  ∃ (C : Langlands.Geometry.Building.CentralizerDatum i)
    (D : Langlands.Geometry.Building.KPApartmentData i
      (Langlands.Geometry.Building.localFieldOrder F)),
    D.SatisfiesApartmentAxioms C ∧ D.HasBoundedOpenStabilizers ∧
      ∃ x : D.Apartment,
        D.IsSpecialApartmentVertex x ∧
          SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
          D.specialCompactSubgroup x = (K : Subgroup (rationalPoints G))

end Special

/-! ### The targets -/

section Targets

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine Tc.X.left]
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)
  (hindex : (RenardCartan.splitValuationImage sc).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [(rationalPoints.map sc).range.Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)
set_option hygiene false in
local notation "Wπ" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  PG.K PG.hK PG.hPK PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse
  PG.hneReverse PG.hDReverseΩ PG.hD PG.hne PG.hirr PG.hreg
set_option hygiene false in
local notation "χ_" s => lowerCocharacter i ν (rootSet i ν I') ζ (R.normalizer s)

/-- The lower smooth sections `C^∞(sO, M' ∩ s·P)` for the Weyl index `s`. -/
abbrev LowerSections (s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
  LowerSectionsAt hG hi hν I I' hζ π (R.normalizer s) (R.levi_le s) hRefl hCST (PM s)

set_option hygiene false in
local notation "nₛ" => R.normalizer
set_option hygiene false in
local notation "hnₛ" => R.levi_le

/-- **The common source normalization for every Weyl index** (Waldspurger I.1, printed p.240):
for every `s`, the density `µ^G` is formed with `K` and the lower density `µ^{M'}` with
`K ∩ M'(F)` (`CommonCompactNormalization`), so that one compact `K` normalizes every measure and
pairing, and `E^{M'}` is formed with `K ∩ M'(F)`. -/
def SourceCompactNormalization : Prop :=
  ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    CommonCompactNormalization hG hi hν I I' hζ (nₛ s) (hnₛ s) K hRefl hCST π PG (PM s)

/-- **Regularity target (Waldspurger, Corollary V.2.3, printed pp.293–294).** For `π` square
integrable modulo `A_M(F)` (the first premise), `K` the special maximal compact subgroup of the
source and the common source normalization, for every `s ∈ W(M'|G|M)` the weighted family `c̃_{P'|P}(s, ·)`
has a rational extension that agrees with it on the nonempty interior of its domain and whose
denominator vanishes at no unitary character, that is, it extends to a rational family regular on
the whole orbit `O`. -/
def WeightedCRegularityStatement : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    Nonempty (WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl
      hCST hPK π PG (PM s) (hN s))

/-- **Normalizer lifts in `K`**: every chosen representative of a Weyl index lies in the fixed
compact open subgroup `K`, as in the source, where representatives of Weyl elements are taken in
the special maximal compact subgroup. Two such lifts of one Weyl element differ by
`a ∈ M_∅(F) ∩ K`, with `δ_P(a) = 1`, so the summands of the expansion do not depend on the
choice; for arbitrary lifts they change by `δ_P(a)⁻¹`. Such systems exist when `K` has the
published property `HasWeylRepresentatives`. -/
def LiftsInCompact : Prop :=
  ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    ((nₛ s : normalizerPoints i) : rationalPoints G) ∈ K

set_option maxHeartbeats 3000000 in
/-- **Pointwise weighted expansion target (Waldspurger V.1.1 in the form used on printed p.304).**
Assume that `K` is the special maximal compact subgroup of the source, that the normalizer lifts
lie in `K`, and the common source normalization (`µ^G` at `K`, the lower densities at
`K ∩ M'(F)`). For every section `q`, the weighted c-families have rational extensions regular on
`O` with lower sections `Ψ_s : sω ↦ c̃_{P'|P}(s, ω) q_ω`, and at **every** `ω ∈ O` (G-regular or
not) and every `m' ∈ M'(F)`:
`µ^G(ω) (f_ω)^w_{P'}(m') = Σ_s µ^{M'}(sω) (E^{M'}_{M'∩s·P} c̃_{P'|P}(s, ω) q_ω)(m')`. -/
def WeightedWeakExpansionStatement : Prop :=
  letI : Fintype (WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
    @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  LiftsInCompact I I' (K := K) R →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    ∃ (E : ∀ s, WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π
        PG (PM s) (hN s))
      (Ψ : ∀ s, LowerSections hG hi hν I I' hζ π hRefl hCST R PM s),
      (∀ s, IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s)
        (hN s) (E s) q (Ψ s)) ∧
      ∀ (ω : Oπ) (m : RationalPoint F 𝐋.X),
        Wπ ω * rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA q ω
            (leviRationalPointHomeomorph i ν I' m) =
          ∑ s, lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST
              (PM s) (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq ω) *
            DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋) hM' (χ_ s)
              (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
              (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
              (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π)
              (lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM)
              (lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM)
              (lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu)
              (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π
                hsq) (Ψ s)
              (lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq ω) m

set_option maxHeartbeats 3000000 in
/-- **Finite decomposition into algebraic lower families (printed p.304).** For `π` square
integrable modulo `A_M(F)` (the first premise), `K` the special maximal compact subgroup of the
source and the common source normalization, for every section `q` and every `s` there are a
rational extension of `c̃_{P'|P}(s, ·)` regular on `O`, a finite family of **polynomial** families
`ψ'_k` on the complex unramified characters `X(s·M)` with values in the fixed lower compact
picture (the compact picture of the algebraic families `L^{M'}(sω_B, M' ∩ s·P)` of the source,
specialized at each point) and smooth functions `φ_k` on `Im X(s·M)` such that for every
`χ ∈ Im X(M_I)`, with `ω_0 = π` as base point:
`c̃_{P'|P}(s, π ⊗ χ) q_{π⊗χ} = Σ_k φ_k(sχ) sp_{sχ} ψ'_k`, read in the fixed compact pictures.
The families and the functions depend only on `q`, `s` and the base point `π`. -/
def WeightedCDecompositionStatement : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I')),
    ∃ (E : WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π PG (PM s)
        (hN s))
      (N : ℕ)
      (ψ' : Fin N → unramifiedCharacters (leviNormCharacters (χ_ s)) →
        ProductInducedCompactPicture (decomposition (χ_ s))
          (lowerK hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
          (SmoothRep.pullback (lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
            (rootSet_subset i ν I) ζ hζ (nₛ s) (hnₛ s)).symm π.obj))
      (φ : Fin N → unitaryUnramifiedCharacters (leviNormCharacters (χ_ s)) → ℂ),
      (∀ k, UnramifiedOperatorFamily.IsPolynomialOn Set.univ (fun χ => ψ' k χ.val)) ∧
      (∀ k, IsSmoothFiniteTorusFunction fun c =>
        φ k ((DynamicInducedOrbit.leviUnitaryCoordinates (H := 𝐋) hM' (χ_ s)).symm c)) ∧
      ∀ z : unitaryUnramifiedCharacters νM,
        E.unitaryValue z (sectionCompactPicture hG hi hν I hKc hPK π q z) =
          ∑ k, φ k (lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s) z) •
            ψ' k ⟨(lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s) z).val,
              (lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s) z).property.1⟩

set_option maxHeartbeats 3000000 in
/-- **Packet identity target (printed pp.303–304).** Assume that `K` is the special maximal
compact subgroup of the source, that the normalizer lifts lie in `K`, and the common source
normalization (`µ^G` at `K`, the lower densities at `K ∩ M'(F)`). For every section `q` and every
`m' ∈ M'(F)`, the orbit integral `∫_O µ^G(ω) (f_ω)^w_{P'}(m') dω` with the source-normalized orbit
measure (the transported I.1 character measure) equals the sum over `s` of the actual
`µ^{M'}`-weighted lower wave packets on `M'` of the lower sections `Ψ_s : sω ↦ c̃_{P'|P}(s, ω) q_ω`,
each with the image of that measure under `χ ↦ sχ`. -/
def WeightedPacketIdentityStatement : Prop :=
  letI : Fintype (WeylIndex i ν (rootSet i ν I) (rootSet i ν I')) :=
    @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I) (rootSet i ν I') hG hi)
  letI := finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu
    (discreteSeriesClass CM hCM mu π hsq)
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  LiftsInCompact I I' (K := K) R →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    ∃ (E : ∀ s, WeightedCExtension hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π
        PG (PM s) (hN s))
      (Ψ : ∀ s, LowerSections hG hi hν I I' hζ π hRefl hCST R PM s),
      (∀ s, IsWeightedCSection hG hi hν I I' hζ hζ' hKc hPK π (nₛ s) (hnₛ s) hRefl hCST PG (PM s)
        (hN s) (E s) q (Ψ s)) ∧
      ∀ m : RationalPoint F 𝐋.X,
        ∫ ω, Wπ ω * rationalOrbitWeakConstantTerm hG hi hν I hKc hPK π CM hCM mu hsq I' hA q ω
            (leviRationalPointHomeomorph i ν I' m)
          ∂discreteSeriesOrbitMeasure νM CM hCM mu (discreteSeriesClass CM hCM mu π hsq)
            (standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex) =
          ∑ s, haveI := finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
            DynamicInducedOrbit.inducedOrbitWavePacket (H := 𝐋) hM' (χ_ s)
              (lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
              (lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s))
              (lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π)
              (lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM)
              (lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM)
              (lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu)
              (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π
                hsq)
              (lowerCharacterMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s)
                (standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex))
              (lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST
                (PM s)) (Ψ s) m

end Targets

end WeakExpansion

end Langlands.HarishChandraSchwartz
