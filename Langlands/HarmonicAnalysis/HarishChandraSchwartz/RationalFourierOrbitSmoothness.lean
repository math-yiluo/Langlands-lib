import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitFourierPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitLaurentSmoothness

/-! # Proposition VII.1.3 on actual points: `ψ_f[O, P] ∈ C^∞(O, P)`

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module instantiates the Library's
`fourierOrbitLaurentSmoothSectionLinear` on actual rational points: the linear map
`f ↦ ψ_f[O, P]` from `C(G)` into `C^∞(O, P)` (`rationalFourierOrbitSmoothSectionLinear`), whose
underlying section is `rationalFourierOrbitSection f`. With formula (1) of
`RationalInducedOrbitFourierPairing` this gives `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`
with no further hypothesis on `ψ_f[O, P]`.

It proves on actual points the Levi-side inputs: Lemma II.1.4 for `M_J`
(`rationalLeviXi_inv`, through the Levi scheme), the translation weights of `M_J`
(`rationalLeviTranslationWeights`), and the identification of the Laurent exponent of the circle
coordinates of `Im X(M_I)` with the valuation coordinates of the Levi scheme
(`laurentExponent_leviRationalUnitaryCoordinates`). The remaining inputs are hypotheses: measure
normalizations, Lemma II.1.5 for `M_I`, temperedness, the conclusion of Proposition II.4.5,
`K ∩ P = (K ∩ M)(K ∩ U)`, a height bound for `H_{M_I}` and an integrability condition.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section LeviWeights

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {K : Subgroup (rationalPoints G)}

/-- **Waldspurger, Lemme II.1.4 for `M_J`** on actual points: `Ξ^{M_J}(m⁻¹) = Ξ^{M_J}(m)`. Through
`rationalXi_leviScheme`, this is `rationalXi_inv` for the Levi scheme, which is connected
reductive with maximal split torus `leviTorusHom` and generic cocharacter `ν`. -/
theorem rationalLeviXi_inv (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (m : standardLeviPoints i ν J) :
    rationalLeviXi hKc hM m⁻¹ = rationalLeviXi hKc hM m := by
  have := leviScheme_isAffineHom i ν J
  have := leviScheme_locallyOfFiniteType i ν J
  obtain ⟨x, rfl⟩ := (leviSchemePointsEquiv i ν J).surjective m
  rw [← map_inv, ← rationalXi_leviScheme hG hi hν hJ hKo hKc hM,
    ← rationalXi_leviScheme hG hi hν hJ hKo hKc hM]
  exact rationalXi_inv
    (BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi) (isGenericCocharacter_leviTorusHom hν)
    (isOpen_leviSchemeCompact hKo) (isCompact_leviSchemeCompact hKc)
    (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM) x

/-- **Translation weights on `M_J(F)`** (Lemma II.1.2 for `M_J`, with `d = 0`): `Ξ^{M_J} > 0`,
`σ|_{M_J} ≥ 0`, two-sided translations change `Ξ^{M_J}` by bounded factors (the Library's
`xi_uniformTranslationBound`, since `δ₀^{M_J} = 1` on `P₀(F) ∩ M_J(F) ∩ K`), and `σ` is
subadditive. -/
theorem rationalLeviTranslationWeights (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) :
    TranslationWeights (rationalLeviXi hKc hM)
      (fun m : standardLeviPoints i ν J => rationalHeight (F := F) ρ m) := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  have : SecondCountableTopology (standardLeviPoints i ν J) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hKMo : IsOpen ((K.subgroupOf (standardLeviPoints i ν J) : Subgroup _) :
      Set (standardLeviPoints i ν J)) := hKo.preimage continuous_subtype_val
  refine ⟨rationalLeviXi_pos hKo hKc hG hi hν hJ hM, fun m => rationalHeight_nonneg ρ m, ?_, ?_⟩
  · exact (xi_uniformTranslationBound
      (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
      hKMo).translationBound _
  · exact heightTranslationBound_of_le_add (fun m => rationalHeight_nonneg ρ m)
      (fun g h => rationalHeight_mul_le ρ g h)

end LeviWeights

section Smooth

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

local instance instRationalFourierOrbitSmoothness1
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalFourierOrbitSmoothness2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalFourierOrbitSmoothness3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

omit [LocallyOfFiniteType G.X.hom] in
/-- **The Laurent exponent of the circle coordinates of `Im X(M_I)`** is the lattice coordinate
vector `n_{M_I}` of the valuation image: for `m ∈ M_I(F)`, the exponent with
`χ(m) = ∏ⱼ zⱼ^{n_j}` for the character `χ` with coordinates `z` is
`rationalValuationCoordinates` of the Levi scheme at the point corresponding to `m`. -/
theorem laurentExponent_leviRationalUnitaryCoordinates
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) :
    laurentExponent (RationalPointFamily.leviRationalNormCharacters i ν I)
        (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
        (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I) m =
      rationalValuationCoordinates (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
        (isConnectedReductive_leviScheme_rootSet hG hi hν I)
        ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m) := by
  refine laurentExponent_eq_of_forall _ _ _ fun z => ?_
  have h1 : (((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm z).val m : ℂ) =
      ((((rationalCanonicalUnitaryUnramifiedCharacterCoordinates _
        (isConnectedReductive_leviScheme_rootSet hG hi hν I)).symm z).val
          ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m) : ℂˣ) : ℂ) := rfl
  rw [h1, rationalUnitaryUnramifiedCharacter_apply]

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

-- The root set `J` of `I`.
set_option hygiene false in
local notation "𝐉" => RationalPointFamily.rootSet i ν I

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν 𝐉)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

variable [μG.IsInvInvariant] [SigmaFinite μG]
  (hμK : μG (K : Set (rationalPoints G)) = 1)
  {μL : Measure 𝐌} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv 𝐌]
  [μL.IsInvInvariant] [SFinite μL]
  (hswM : SquareIntegrableWeight μL (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (hTπ : IsRationalLeviTempered hKc ρ hM π.obj)
  {νU : Measure (standardUnipotentPoints i ν 𝐉)} [νU.IsHaarMeasure]
  [νU.IsMulRightInvariant] [SFinite νU]
  (hE : ConstantTermEstimate νU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (hPKiw : ∀ (m : standardLeviPoints i ν 𝐉) (u : standardUnipotentPoints i ν 𝐉),
    (m : rationalPoints G) * u ∈ K ↔ (m : rationalPoints G) ∈ K ∧ (u : rationalPoints G) ∈ K)
  (hMK : μL {m : 𝐌 | (m : rationalPoints G) ∈ K} = 1)
  (hUK : νU {u : standardUnipotentPoints i ν 𝐉 | (u : rationalPoints G) ∈ K} = 1)
  {Cn : ℝ}
  (hnσ : ∀ m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I),
    ‖rationalValuationCoordinates (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      (isConnectedReductive_leviScheme_rootSet hG hi hν I)
      ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m)‖ ≤
      Cn * (1 + rationalHeight (F := F) ρ m))
  (hint : ∀ (f : RationalSchwartzSpace hKc hPK ρ)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π)
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A.val.obj),
    Integrable
      (fun x : rationalPoints G × K => conj (CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν 𝐉) A.val.obj K x.1 ψ x.2) * f x.1)
      (μG.prod (CompactInduction.measure K hKc)))

/-- **Proposition VII.1.3 on actual rational points** (smoothness and linearity): the linear
map `f ↦ ψ_f[O, P]` from `C(G)` into `C^∞(O, P)`, the Library's
`fourierOrbitLaurentSmoothSectionLinear` on the actual data of `P_I(F)`. -/
def rationalFourierOrbitSmoothSectionLinear :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  haveI : Nonempty (CompactOpenSubgroup 𝐌) :=
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr this⟩⟩
  fourierOrbitLaurentSmoothSectionLinear (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (compactOpenCofinal_standardLevi I hKc) C hC μM
    (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq)
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) hsq hμK
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    ⟨rationalLeviXi_pos K.isOpen hKc hG hi hν (RationalPointFamily.rootSet_subset i ν I) hM,
      fun m => rationalHeight_nonneg ρ m, by obtain ⟨d, hd⟩ := hswM; exact ⟨d, hd⟩⟩
    hTπ hTA (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
    (fun m => rationalHeight_inv ρ m)
    (rationalConstantTermData νU) (rationalIsConjModulus νU) hE
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc
      hM ρ)
    hPKiw hMK hUK (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (fun m => by rw [laurentExponent_leviRationalUnitaryCoordinates]; exact hnσ m) hint

/-- The section `ψ_f[O, P] ∈ C^∞(O, P)` is `rationalFourierOrbitSection f`. -/
theorem rationalFourierOrbitSmoothSectionLinear_val (f : RationalSchwartzSpace hKc hPK ρ) :
    (rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw
        hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f).val =
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f := by
  unfold rationalFourierOrbitSmoothSectionLinear rationalFourierOrbitSection
  rfl

variable [Finite (discreteSeriesStabilizer C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC μM π hsq))]
  (ρX : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC μM π hsq) → ℂ)

/-- **Formula (1) of the proof of Proposition VII.2.2 on actual points, with `ψ_f[O, P]` from
Proposition VII.1.3**: `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`, where the section
`ω ↦ f̂(ω, P)` is `rationalFourierOrbitSmoothSectionLinear … f ∈ C^∞(O, P)`. -/
theorem pairing_rationalInducedOrbitWavePacket_eq_integral_fourier [SFinite μG]
    [IsFiniteMeasure ρX]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
        (discreteSeriesClass C hC μM π hsq) ρX))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    pairing μG (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX w q) f =
      ∫ ω, conj (w ω) *
        (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
        unitaryOrbitProductPairing (G := rationalPoints G)
          (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
          (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
          (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
          (fun g =>
            RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
          (modularCharacter_standardParabolicPoints hG hi hν I rfl
            (RationalPointFamily.rootSet_subset i ν I))
          π (compactOpenCofinal_standardLevi I hKc) C hC μM hsq
          (RationalPointFamily.leviRationalNormCharacters i ν I)
          (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
          (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv q
          (rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq
            hTA hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f) ω)
        ∂discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
          (discreteSeriesClass C hC μM π hsq) ρX :=
  pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing hG hi hν I hKc hPK ρ hρ hKρ hM
    π C hC μM hsq hTA hsw ρX w hwm hwb hcoeff q
    (rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw
      hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f) f
    (rationalFourierOrbitSmoothSectionLinear_val hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA
      hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f)

end Smooth

end Langlands.HarishChandraSchwartz
