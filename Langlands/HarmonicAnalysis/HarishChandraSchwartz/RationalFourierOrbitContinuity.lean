import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitContinuity

/-! # Proposition VII.1.3 on actual points: continuity of `f ↦ ψ_f[O, P]`

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module instantiates the Library's
`fourierOrbitLaurentSectionCLM` (`FourierOrbitContinuity`) on actual rational points: the map
`f ↦ ψ_f[O, P]` from `C(G)`, with the topology of III.6, to `C^∞(O, P)`, with the topology of
VI.3, is a continuous linear map (`rationalFourierOrbitSectionCLM`), whose underlying linear map
is `rationalFourierOrbitSmoothSectionLinear` (`RationalFourierOrbitSmoothness`). It also proves
on actual points that `ψ_f[O, P]` is fixed by `H × H` when `f` is bi-invariant under `H`
(Lemma VII.1.1 (i)), so that `ψ_f[O, P]` lies in the level `C^∞(O, P)^{H × H}`.

The hypotheses are those of `rationalFourierOrbitSmoothSectionLinear`: measure normalizations,
Lemma II.1.5 for `G` and `M_I`, temperedness, the conclusion of Proposition II.4.5,
`K ∩ P = (K ∩ M)(K ∩ U)`, a height bound for `H_{M_I}` and an integrability condition.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Continuity

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

local instance instRationalFourierOrbitContinuity1
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalFourierOrbitContinuity2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalFourierOrbitContinuity3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

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

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

/-- **The space `C^∞(O, P)` with the topology of VI.3** for an actual standard parabolic: the
Library's `OrbitSectionSpace` (smooth sections over the unitary unramified orbit of `π`, with
the locally convex inductive-limit topology of the levels `C^∞(O, P)^{H × H}`, `H ⊆ K` compact
open) on the actual data of `P_I(F)`. Its elements are those of
`rationalInducedSmoothOrbitSections` (`OrbitSectionSpace.toSections`). -/
abbrev rationalInducedOrbitSectionSpace :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  OrbitSectionSpace (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))

variable (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **`ψ_f[O, P]` is fixed by `H × H` when `f` is bi-invariant under `H`** (consequence of
Lemma VII.1.1 (i), as in the proof of Proposition VII.1.3), on actual points: for
`x = (x₁, x₂)` with `x₁, x₂ ∈ H`, the action of `x` on the orbit section `ψ_f[O, P]` (by
`(I_P^G ω)(x₁) ⊗ (I_P^G ω)ˇ(x₂)` at every representative `ω`) fixes it. -/
theorem productInducedOrbitRepresentation_rationalFourierOrbitSection
    {H : Subgroup (rationalPoints G)} {f : RationalSchwartzSpace hKc hPK ρ}
    (hf : IsBiInvariant H f) (x : rationalPoints G × rationalPoints G) (hx₁ : x.1 ∈ H)
    (hx₂ : x.2 ∈ H) :
    productInducedOrbitRepresentation (G := rationalPoints G)
        (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
        (RationalPointFamily.leviRationalNormCharacters i ν I) π x
        (rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f) =
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := productInducedOrbitRepresentation_fourierOrbitSection (G := rationalPoints G)
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
    (rationalTranslationWeights K.isOpen hKc hPK ρ) hf x hx₁ hx₂
  unfold rationalFourierOrbitSection
  with_reducible_and_instances exact h

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

/-- **`ψ_f[O, P]` lies in the level `C^∞(O, P)^{H × H}`** when `f ∈ C(G)` is bi-invariant
under the open subgroup `H`: the section of `rationalFourierOrbitSmoothSectionLinear` is smooth
and fixed by `H × H` (`productInducedOrbitRepresentation_rationalFourierOrbitSection`). -/
theorem rationalFourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule
    (H : OpenSubgroup (rationalPoints G)) {f : RationalSchwartzSpace hKc hPK ρ}
    (hf : IsBiInvariant H.toSubgroup f) :
    (rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw
        hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f).val ∈
      (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
      orbitSectionLevelSubmodule (G := rationalPoints G)
        (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
        (RationalPointFamily.leviRationalNormCharacters i ν I) π
        (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
        (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
        (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
        (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
        (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) H) := by
  refine ⟨(rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq
    hTA hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f).property, fun x => ?_⟩
  rw [rationalFourierOrbitSmoothSectionLinear_val]
  exact productInducedOrbitRepresentation_rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ
    hKρ hM π C hC μM hsq hTA hsw hf x.val x.property.1 x.property.2

/-- **Proposition VII.1.3 on actual rational points** (continuity): the map
`f ↦ ψ_f[O, P]` from `C(G)` (topology of III.6) to `C^∞(O, P)` (topology of VI.3) as a
continuous linear map; the Library's `fourierOrbitLaurentSectionCLM` on the actual data of
`P_I(F)`. -/
def rationalFourierOrbitSectionCLM :
    RationalSchwartzSpace hKc hPK ρ →L[ℂ] rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  haveI : Nonempty (CompactOpenSubgroup 𝐌) :=
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr this⟩⟩
  fourierOrbitLaurentSectionCLM (G := rationalPoints G)
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
    hPKiw hMK hUK hint (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (fun m => by rw [laurentExponent_leviRationalUnitaryCoordinates]; exact hnσ m)

/-- The continuous linear map is `f ↦ ψ_f[O, P]`: its underlying element of `C^∞(O, P)` is
`rationalFourierOrbitSmoothSectionLinear … f`. -/
theorem toSections_rationalFourierOrbitSectionCLM (f : RationalSchwartzSpace hKc hPK ρ) :
    (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
    OrbitSectionSpace.toSections (G := rationalPoints G)
      (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
      (RationalPointFamily.leviRationalNormCharacters i ν I) π
      (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      (rationalFourierOrbitSectionCLM hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw hμK
        hswM hTπ hE hPKiw hMK hUK hnσ hint f)) =
      rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw
        hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f := by
  unfold rationalFourierOrbitSectionCLM rationalFourierOrbitSmoothSectionLinear
  rfl

/-- The section underlying `rationalFourierOrbitSectionCLM … f` is
`ψ_f[O, P] = rationalFourierOrbitSection f`. -/
theorem rationalFourierOrbitSectionCLM_apply_val (f : RationalSchwartzSpace hKc hPK ρ) :
    (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
    OrbitSectionSpace.toSections (G := rationalPoints G)
      (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
      (RationalPointFamily.leviRationalNormCharacters i ν I) π
      (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      (rationalFourierOrbitSectionCLM hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw hμK
        hswM hTπ hE hPKiw hMK hUK hnσ hint f)).val =
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f := by
  rw [toSections_rationalFourierOrbitSectionCLM]
  exact rationalFourierOrbitSmoothSectionLinear_val hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq
    hTA hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f

end Continuity

end Langlands.HarishChandraSchwartz
