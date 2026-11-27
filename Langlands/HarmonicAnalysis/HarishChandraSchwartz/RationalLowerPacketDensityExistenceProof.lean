import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketDensityExistence
import Langlands.Representation.Plancherel.ActualOppositeFullDomainContinuationProof
import Langlands.Representation.Unitary.CentralSubgroupForm
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # Lower packet densities on the actual full convergence domains -/

noncomputable section

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

universe u uV uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.Plancherel

section CenterQuotientHaar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (C : Subgroup G) [C.Normal] (hC : C ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ C)] [BorelSpace (G ⧸ C)]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

omit [T2Space G] in
/-- Square integrability of an irreducible representation modulo a central
subgroup makes the pushforward of the quotient Haar measure to the full central
quotient a Haar measure. -/
theorem centralQuotientProjection_map_isHaarMeasure_of_isSquareIntegrable
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hirr : Representation.IsIrreducible ρ)
    (m : Measure (G ⧸ C)) [m.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ m) :
    (m.map (centralQuotientProjection C hC)).IsHaarMeasure := by
  obtain ⟨hadm, c, hL2⟩ := hsq
  obtain ⟨ℓ, hℓ⟩ :=
    exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hadm.1 hirr
  obtain ⟨v, hv⟩ : ∃ v, ℓ.1 v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  exact centralQuotientProjection_map_isHaarMeasure C hC c hadm.1 ℓ.1 v hv m (hL2 ℓ v)

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The same pushforward keeps square integrability, now modulo the full center. -/
theorem isSquareIntegrableModCenter_map_centralQuotientProjection
    (m : Measure (G ⧸ C)) [m.IsHaarMeasure]
    [(m.map (centralQuotientProjection C hC)).IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ m) :
    IsSquareIntegrableModCentralSubgroup (Subgroup.center G) le_rfl ρ
      (m.map (centralQuotientProjection C hC)) := by
  obtain ⟨hadm, c, hL2⟩ := hsq
  refine ⟨hadm, c, fun ℓ v => ?_⟩
  have h := centralSubgroupCoefficientNorm_memLp_map C hC c hadm.1 ℓ.1 v m (hL2 ℓ v)
  have he : centralSubgroupCoefficientNorm (Subgroup.center G) le_rfl c ℓ v =
      c.coefficientNorm ℓ v := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H g => rfl
  rw [he]
  exact h

omit [SecondCountableTopology G] in
/-- On the full central quotient of a unimodular group, every regular Haar
measure is invariant under inversion. -/
theorem centerQuotientHaar_isInvInvariant
    (hmod : ∀ g : G, Measure.modularCharacter g = 1)
    (ν : Measure (G ⧸ Subgroup.center G)) [ν.IsHaarMeasure] [ν.Regular] :
    ν.IsInvInvariant := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : ν.IsMulRightInvariant := Haar.centralQuotient_isMulRightInvariant hmod ν
  exact isInvInvariant_of_isMulRightInvariant ν

end CenterQuotientHaar

section FullDomainHaar

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The whole-domain continuations of the actual opposite compact families
exist for an irreducible representation square integrable modulo a central
subgroup with respect to any quotient Haar measure, without an inversion
invariance premise on that measure. -/
theorem actualOppositeFullDomainContinuation_of_isHaarMeasure
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (hi : A.IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu) :
    (Nonempty (ForwardContinuation χ relativeRootReflectionExistence centralSplitTorusCharacter
        hG K hK hPK hOppK A) ∧
      ∃ D : Set (unramifiedCharacters (normCharacters χ)),
        IsOpen D ∧ D.Nonempty ∧ D ⊆ forwardFullDomainRegion χ K hK A) ∧
    (Nonempty (ReverseContinuation χ relativeRootReflectionExistence centralSplitTorusCharacter
        hG K hK hPK hOppK A) ∧
      ∃ D : Set (unramifiedCharacters (normCharacters χ)),
        IsOpen D ∧ D.Nonempty ∧ D ⊆ reverseFullDomainRegion χ K hK A) := by
  let : SecondCountableTopology (levi χ) :=
    TopologicalSpace.Subtype.secondCountableTopology (levi χ : Set (RationalPoint F G.X))
  let : LocallyCompactSpace (levi χ) := (levi_isClosed χ).locallyCompactSpace
  let : MeasurableSpace (levi χ ⧸ Subgroup.center (levi χ)) := borel _
  let : BorelSpace (levi χ ⧸ Subgroup.center (levi χ)) := ⟨rfl⟩
  let : IsClosed ((Subgroup.center (levi χ) : Subgroup (levi χ)) : Set (levi χ)) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set (levi χ)))
  let muZ := mu.map (centralQuotientProjection C hC)
  let : muZ.IsHaarMeasure :=
    centralQuotientProjection_map_isHaarMeasure_of_isSquareIntegrable C hC
      (compactOpenCofinal_of_nonarchimedean (levi χ)) hi mu hsq
  let : muZ.IsInvInvariant := centerQuotientHaar_isInvInvariant
    (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG) muZ
  exact actualOppositeFullDomainContinuation χ hG K hK hPK hOppK A hi
    (Subgroup.center (levi χ)) le_rfl muZ
    (isSquareIntegrableModCenter_map_centralQuotientProjection C hC mu hsq)

end FullDomainHaar

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
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
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerDensityProofLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerDensityProofLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance lowerDensityProofLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "L'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "χ'" => lowerCocharacter i ν (rootSet i ν I') ζ n

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "K'" => LowerChamber.lowerCompact I' K.isOpen
set_option hygiene false in
local notation "hK'" => isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootSet i ν I') hKc
set_option hygiene false in
local notation "π'" => lowerRepresentation hG hi hν I I' hζ n hn π

open DynamicCommonLeviComposition DynamicCommonLeviContinuation ActualCommonLeviV3

attribute [local instance] ActualCommonLeviV3.leviMeasurable
  ActualCommonLeviV3.leviBorel ActualCommonLeviV3.leviLocallyCompact

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (ha : IsSplitComponent a)

set_option hygiene false in
local notation "C" => rationalLeviSplitCenter I a
set_option hygiene false in
local notation "hC" => rationalLeviSplitCenter_le_center I a ha

variable [(C).Normal] [MeasurableSpace (𝐌 ⧸ C)] [hBorel : BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

omit hBorel in
set_option synthInstance.maxHeartbeats 150000 in
set_option maxHeartbeats 8000000 in
/-- Square integrability and the standard Levi Iwasawa products give the
literal lower density package, with continuations on both entire actual
convergence domains. -/
theorem lowerPacketDensityAtCompact :
    LowerPacketDensityAtCompactStatement hG hi hν I I' hζ n hn π
      (K := K) (a := a) (ha := ha) (mu := mu) hRefl hCST := by
  intro _ hKc hsq hFactors
  let C' := lowerCentral hG hi hν I I' hζ n hn C
  let hC' := lowerCentral_le_center hG hi hν I I' hζ n hn C hC
  let : C'.Normal := lowerCentral_normal hG hi hν I I' hζ n hn C
  let : MeasurableSpace (levi χ' ⧸ C') := lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn C
  let : BorelSpace (levi χ' ⧸ C') := lowerQuotientBorelSpace hG hi hν I I' hζ n hn C
  let mu' : Measure (levi χ' ⧸ C') := lowerMeasure hG hi hν I I' hζ n hn C mu
  let : mu'.IsHaarMeasure := lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn C mu
  have hsq' := lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq
  have hG' := lowerAmbient_isConnectedReductive hG hi hν I'
  have hP' (g : rationalPoints L') :
      ∃ p : parabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := parabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') χ') g
  have hOpp' (g : rationalPoints L') :
      ∃ p : oppositeParabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := oppositeParabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') (Dynamic.inverseCocharacter χ')) g
  obtain ⟨⟨⟨p⟩, DF, hDF, hneF, hsubF⟩, ⟨⟨q⟩, DR, hDR, hneR, hsubR⟩⟩ :=
    actualOppositeFullDomainContinuation_of_isHaarMeasure χ' hG' K' hK' hP' hOpp' (π').obj
      (π').property.1 C' hC' mu' hsq'
  exact ⟨lowerDensityFromOppositeContinuations hG hi hν I I' hζ n hn a ha π mu hsq hRefl hCST
    hKc hFactors p q hDF hneF hsubF hDR hneR hsubR, rfl⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
