import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight
import Langlands.Representation.Plancherel.DynamicOppositeUniformNonvanishing
import Langlands.Representation.Plancherel.OppositeIntertwiningHermitianAdjunction
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # The Plancherel weight at the full simple-root index

When the centralizer of `ζ ∘ i` is all of `G(F)`, the Library's canonical scalar `j_P` of the
actual opposite standard integrals is `1`: the radicals are trivial, so the standard integrals
are evaluation and the continued composite is the identity. When moreover `ζ` has no positive
relative roots, the density constant `∏_α γ(M_α|M)²` is the empty product. Hence the
Plancherel weight is the constant `1`, in particular at the full simple-root index
(`standardLeviPlancherelWeight_eq_one_of_rootSet_eq_simpleRelativeRoots`).
-/

noncomputable section

universe u uG uI uV uW uX

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Continued composites acting as the identity -/

section ContinuedIdentity

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {Ω Λ D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}
  (p : RationalOperatorContinuationData Ω A)
  (q : RationalOperatorContinuationData Λ B)

include hp hL in
/-- If, after injective linear maps `eV`, `eW` into a common space, the operators `A w` and
`B w` act as the identity on nonempty open subsets of their domains, then the composite of
their rational continuations is the identity at every common regular point. -/
theorem continuedComposite_eq_id_of_eqOn
    (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ)
    (eV : V →ₗ[ℂ] X) (heV : Function.Injective eV) (eW : W →ₗ[ℂ] X)
    (hA : ∀ (w) (hw : w ∈ D) (v : V), eW (A ⟨w, hDΩ hw⟩ v) = eV v)
    (hB : ∀ (w) (hw : w ∈ E) (x : W), eV (B ⟨w, hEΛ hw⟩ x) = eW x)
    (z : ↥(p.regularRegion ∩ q.regularRegion)) :
    p.continuedComposite q z = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply heV
  have h1 := continuedOperator_map_eq_of_eqOn L hp hL p hD hneD hDΩ eW v (eV v)
    (fun w hw => hA w hw v) ⟨z.val, z.property.1⟩
  have h2 := continuedOperator_map_eq_of_eqOn L hp hL q hE hneE hEΛ eV
    (p.continuedOperator ⟨z.val, z.property.1⟩ v)
    (eW (p.continuedOperator ⟨z.val, z.property.1⟩ v))
    (fun w hw => hB w hw _) ⟨z.val, z.property.2⟩
  change eV (q.continuedOperator ⟨z.val, z.property.2⟩
    (p.continuedOperator ⟨z.val, z.property.1⟩ v)) = eV v
  rw [h2, h1]

include hp hL in
/-- If the continued composite is the identity at every common regular point, its extracted
rational scalar is `1`, for every normalized coefficient `ℓ v = 1`. -/
theorem continuedCompositeRationalScalar_eq_one_of_eq_id
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (hid : ∀ z : ↥(p.regularRegion ∩ q.regularRegion),
      p.continuedComposite q z = LinearMap.id) :
    continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ = 1 := by
  obtain ⟨a, b, hb, hbR, hfrac, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ℓ
  have hR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  have hneR := continuedCompositeRegion_nonempty L hp hL p q hΩ hΛ
  have hab : a - b = 0 := by
    apply rationalUnramifiedRegular_eq_zero_of_isOpen L hp hL _ hR hneR
    intro χ hχ
    have h := hval ⟨χ, hχ⟩
    have hs : p.continuedCompositeScalar q v ℓ ⟨χ, hχ⟩ = 1 := by
      change ℓ (p.continuedComposite q ⟨χ, hχ⟩ v) = 1
      rw [hid]
      exact hℓ
    rw [hs, eq_div_iff (hbR ⟨χ, hχ⟩), one_mul] at h
    change a.val χ - b.val χ = 0
    rw [h, sub_self]
  rw [sub_eq_zero] at hab
  rw [hfrac, hab]
  exact div_self ((map_ne_zero_iff _
    (rationalUnramifiedFunctionField_algebraMap_injective L hp hL)).mpr hb)

end ContinuedIdentity

/-! ### Standard integrals over a trivial radical -/

section TrivialRadical

open Aubert.General Induction StandardIntertwining
open OppositeIntertwiningHermitianAdjunction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) {U' : Subgroup G}
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]

/-- **The standard integral over a trivial radical is evaluation.** If `U' = 1` and the Haar
measures on `U'` and on `U ∩ U'` give these trivial groups mass one, then a vector `J f(g)`
representing the integral of `u' ↦ f(u' g)` over the compatible quotient `(U ∩ U') \ U'` is
`f(g)`. -/
theorem HasIntegral.eq_eval_of_eq_bot
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular]
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {qν : Measure (QuotientSpace (U := U) U')}
    (hbot : U' = ⊥) (hμU' : μU' Set.univ = 1) (hμI : μI Set.univ = 1)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
    (hM : IsClosed (M : Set G))
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A} {Jf : G → A}
    (hJ : HasIntegral h hU U' A qν f Jf) (g : G) :
    Jf g = eval P (leviInflatedInducingRepresentation h hU A) f g := by
  subst hbot
  have hU' : IsClosed (((⊥ : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have : LocallyCompactSpace (⊥ : Subgroup G) := hU'.locallyCompactSpace
  have : IsFiniteMeasure μI := ⟨by rw [hμI]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure μU' := ⟨by rw [hμU']; exact ENNReal.one_lt_top⟩
  have hone : ∀ u' : (⊥ : Subgroup G), u' = 1 := fun u' =>
    Subtype.ext (Subgroup.mem_bot.mp u'.property)
  have hbot' := subgroupOf_eq_one (A := U) (B := (⊥ : Subgroup G)) (by rw [inf_bot_eq])
  have hH : IsClosed ((U.subgroupOf ⊥ : Subgroup (⊥ : Subgroup G)) : Set (⊥ : Subgroup G)) :=
    hU.preimage continuous_subtype_val
  have hself : HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation qν
      (integrand h hU ⊥ A g f) (eval P (leviInflatedInducingRepresentation h hU A) f g) := by
    intro ℓ
    have hfun : (fun u' : (⊥ : Subgroup G) => ℓ.val (integrand h hU ⊥ A g f (Quotient.mk _ u'))) =
        fun _ => ℓ.val (eval P (leviInflatedInducingRepresentation h hU A) f g) := by
      funext u'
      rw [integrand_mk, hone u']
      simp
    refine ⟨(integrable_trivialQuotient_iff (U.subgroupOf ⊥) hbot' hH hμI hqν _).mpr ?_, ?_⟩
    · rw [hfun]
      exact integrable_const _
    · rw [integral_trivialQuotient (U.subgroupOf ⊥) hbot' hH hμI hqν
        (fun q => ℓ.val (integrand h hU ⊥ A g f q)), hfun, integral_const]
      simp [Measure.real, hμU']
  exact HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique (compactCofinal hM)
    A.isSmooth (hJ g) hself

end TrivialRadical

/-! ### Compact pictures of standard integrals over a trivial radical -/

section CompactTrivialRadical

open Aubert.General Induction StandardIntertwining

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- The values on `K` of a section in the fixed compact picture, as a linear map. -/
def compactPictureValues (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    CompactInductionPicture h K A →ₗ[ℂ] (K → A) where
  toFun φ k := eval _ _ φ k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G] in
/-- A section in the compact picture is determined by its values on `K`. -/
theorem compactPictureValues_injective (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    Function.Injective (compactPictureValues h K A) :=
  fun _ _ hφψ => Subtype.ext (Subtype.ext (funext fun k => congrFun hφψ k))

/-- **Over a trivial radical the compact picture of a standard integral is the identity on
values.** If `J` is an intertwiner between the two inductions whose values represent the
standard integrals over `(U ∩ U') \ U'` for a compatible quotient measure, and `U' = 1` with
the Haar measures on `U'` and `U ∩ U'` of mass one, then the compact picture of `J` keeps the
values on `K` of every section. -/
theorem compactIntertwiningOperator_values_of_eq_bot (χ : unramifiedCharacters ν)
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular]
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {qν : Measure (QuotientSpace (U := U) U')}
    (hbot : U' = ⊥) (hμU' : μU' Set.univ = 1) (hμI : μI Set.univ = 1)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
    (hM : IsClosed (M : Set G))
    (J : (UnramifiedLeviInduction h hU ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ A).representation)
    (hJ : ∀ f, HasIntegral h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν f
      (eval P' (leviInflatedInducingRepresentation h' hU'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) (J f)))
    (φ : CompactInductionPicture h K A) :
    compactPictureValues h' K A (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' χ A J φ) =
      compactPictureValues h K A φ := by
  funext k
  have e := HasIntegral.eq_eval_of_eq_bot h hU _ hbot hμU' hμI hqν hM
    (hJ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm φ)) (k : G)
  have e2 := unramifiedLeviInductionCompactEquiv_eval h hU hδ K hP hK hPK ν hν hr χ A
    ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm φ) k
  rw [LinearEquiv.apply_symm_apply] at e2
  exact e.trans e2.symm

end CompactTrivialRadical

/-- The Haar measure on a trivial closed subgroup, normalized by the common compact open, gives
the whole subgroup mass one. -/
theorem subgroupCompactOpenHaar_univ_of_eq_bot {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))
    (U : Subgroup G) (hU : IsClosed (U : Set G)) [MeasurableSpace U] [BorelSpace U]
    (hbot : U = ⊥) : Haar.subgroupCompactOpenHaar Q hQ U hU Set.univ = 1 := by
  have hset : {u : U | (u : G) ∈ Q} = Set.univ :=
    Set.eq_univ_of_forall fun u => by
      change (u : G) ∈ Q
      rw [(Subgroup.eq_bot_iff_forall U).mp hbot u u.property]
      exact Q.one_mem
  rw [← hset]
  exact Haar.subgroupCompactOpenHaar_mass Q hQ U hU

/-! ### The canonical scalar of a central cocharacter -/

section DynamicCentral

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open OppositeIntertwiningHermitianAdjunction

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
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace3
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace4
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace5
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace6
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace6

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- If the centralizer of `χ` is all of `G(F)`, the radical of `χ` is trivial. -/
theorem radical_eq_bot_of_levi_eq_top (hlevi : levi χ = ⊤) : radical χ = ⊥ :=
  (decomposition χ).unipotent_eq_bot_of_levi_eq_top hlevi

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- If the centralizer of `χ` is all of `G(F)`, the opposite radical is trivial. -/
theorem oppositeRadical_eq_bot_of_levi_eq_top (hlevi : levi χ = ⊤) : oppositeRadical χ = ⊥ :=
  (oppositeDecomposition χ).unipotent_eq_bot_of_levi_eq_top hlevi

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- For a central cocharacter, every forward compact-picture value keeps the values on `K`. -/
theorem conditionalForwardCompactFamily_values_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z : forwardFullDomainRegion χ K hK A) (φ : CompactInductionPicture (decomposition χ) K A) :
    compactPictureValues (oppositeDecomposition χ) K A
        (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) =
      compactPictureValues (decomposition χ) K A φ :=
  compactIntertwiningOperator_values_of_eq_bot (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (projection_continuous χ) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadical_unimodular χ hG) (oppositeParabolic_isClosed χ) hOppK
    (oppositeProjection_continuous χ) (parameterTransport χ z.val) A
    (oppositeRadical_eq_bot_of_levi_eq_top χ hlevi)
    (subgroupCompactOpenHaar_univ_of_eq_bot K hK _ _
      (oppositeRadical_eq_bot_of_levi_eq_top χ hlevi))
    (sourceIntersectionHaar_univ K hK _ _ _ _ (radical_inf_oppositeRadical χ))
    (forwardQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalForwardFamily χ K hK hRefl hCST hG A z)
    (conditionalForwardFamily_spec χ K hK hRefl hCST hG A z) φ

/-- For a central cocharacter, every reverse compact-picture value keeps the values on `K`. -/
theorem conditionalReverseCompactFamily_values_of_levi_eq_top (hlevi : levi χ = ⊤)
    (z : reverseFullDomainRegion χ K hK A)
    (φ : CompactInductionPicture (oppositeDecomposition χ) K A) :
    compactPictureValues (decomposition χ) K A
        (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) =
      compactPictureValues (oppositeDecomposition χ) K A φ :=
  compactIntertwiningOperator_values_of_eq_bot (oppositeDecomposition χ)
    (oppositeRadical_isClosed χ) (oppositeRadical_unimodular χ hG) K
    (oppositeParabolic_isClosed χ) hK hOppK (leviNormCharacters χ)
    (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
    (oppositeProjection_continuous χ) (decomposition χ) (radical_isClosed χ)
    (radical_unimodular χ hG) (parabolic_isClosed χ) hPK
    (projection_continuous χ) (parameterTransport χ z.val) A
    (radical_eq_bot_of_levi_eq_top χ hlevi)
    (subgroupCompactOpenHaar_univ_of_eq_bot K hK _ _ (radical_eq_bot_of_levi_eq_top χ hlevi))
    (sourceIntersectionHaar_univ K hK _ _ _ _
      ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)))
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalReverseFamily χ K hK hRefl hCST hG A z)
    (conditionalReverseFamily_spec χ K hK hRefl hCST hG A z) φ

variable
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

include hDForward hDReverse hD in
/-- **`j_P = 1` for a central cocharacter.** If the centralizer of `χ` is all of `G(F)`, the
canonical rational scalar of the actual opposite standard integrals, at the intrinsic source
Haar scale `K`, is the constant `1`, for every choice of continuations and loci. -/
theorem conditionalCanonicalRationalScalar_eq_one_of_levi_eq_top (hlevi : levi χ = ⊤) :
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
      p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr = 1 := by
  obtain ⟨v, ℓ, hℓ⟩ := exists_normalized_compactCoefficient (χ := χ) (hG := hG)
    (K := K) (hK := hK) (hPK := hPK) (A := A) (hne := hne) (hi := hirr)
  rw [conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK A
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr v ℓ hℓ]
  refine continuedCompositeRationalScalar_eq_one_of_eq_id _ (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) p q _ _ v ℓ hℓ fun z => ?_
  exact continuedComposite_eq_id_of_eqOn _ (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ
    (compactPictureValues (decomposition χ) K A)
    (compactPictureValues_injective (decomposition χ) K A)
    (compactPictureValues (oppositeDecomposition χ) K A)
    (fun w hw φ => conditionalForwardCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK
      hPK hOppK A hlevi ⟨w, hDForwardΩ hw⟩ φ)
    (fun w hw φ => conditionalReverseCompactFamily_values_of_levi_eq_top χ hRefl hCST hG K hK
      hPK hOppK A hlevi ⟨w, hDReverseΩ hw⟩ φ) z

end DynamicCentral

/-! ### No positive roots at the full simple-root index -/

section FullRootSigns

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every relative root pairs to zero with a standard cocharacter of the full simple-root
index: such a cocharacter has the relative-root signs of the zero cocharacter. -/
theorem latticePairing_eq_zero_of_isStandardCocharacter_simple
    (hν : IsGenericCocharacter i ν) (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (simpleRelativeRoots i ν) ζ)
    {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    latticePairing T α ζ = 0 :=
  ((IsStandardCocharacter.haveSameRelativeRootSigns i ν hν hneg hζ
    (isStandardCocharacter_simple_zero i ν)) α hα).2.1.mpr (map_zero _)

/-- A standard cocharacter of the full simple-root index has no positive relative roots. -/
theorem positiveRelativeRoots_eq_empty_of_isStandardCocharacter_simple
    (hν : IsGenericCocharacter i ν) (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (simpleRelativeRoots i ν) ζ) :
    positiveRelativeRoots i ζ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hα =>
    hα.2.ne' (latticePairing_eq_zero_of_isStandardCocharacter_simple i ν hν hneg hζ hα.1)

end FullRootSigns

/-! ### The Plancherel weight of a central cocharacter -/

section FullRootWeight

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity

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
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)

/-- With no positive relative roots the product `∏_α γ(M_α|M)` is empty, hence `1`. -/
theorem rankOneGammaProduct_eq_one_of_positiveRelativeRoots_eq_empty
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hpos : positiveRelativeRoots i ζ = ∅) :
    rankOneGammaProduct i ζ K hK = 1 := by
  unfold rankOneGammaProduct rankOneCocharacterSet
  rw [hpos, Set.image_empty, finprod_mem_empty]

/-- With no positive relative roots the density constant `∏_α γ(M_α|M)²` is `1`. -/
theorem plancherelDensityConstant_eq_one_of_positiveRelativeRoots_eq_empty
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hpos : positiveRelativeRoots i ζ = ∅) :
    plancherelDensityConstant i ζ K hK = 1 := by
  unfold plancherelDensityConstant
  rw [rankOneGammaProduct_eq_one_of_positiveRelativeRoots_eq_empty i ζ K hK hpos]
  simp

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG

include hDForward hDReverse hD in
/-- For a central cocharacter `ζ ∘ i`, the rational function `j_P⁻¹ = 1` is regular at every
unitary unramified character. -/
theorem rationalFunctionUnitaryRegular_inv_of_levi_eq_top (hlevi : levi χ = ⊤) :
    RationalFunctionUnitaryRegular MS hMS (jP)⁻¹ := by
  rw [conditionalCanonicalRationalScalar_eq_one_of_levi_eq_top χ hRefl hCST hG K hK hPK hOppK A
    p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hlevi,
    inv_one]
  simpa using rationalFunctionUnitaryRegular_algebraMap MS hMS 1

include hDForward hDReverse hD in
/-- **The Plancherel weight of a central cocharacter is `1`.** If the centralizer of `ζ ∘ i` is
all of `G(F)` and `ζ` has no positive relative roots, then `μ(π ⊗ z) = 1` for every unitary
unramified character `z`: the density constant is an empty product and `j_P = 1`. -/
theorem plancherelWeight_eq_one_of_levi_eq_top (hlevi : levi χ = ⊤)
    (hpos : positiveRelativeRoots i ζ = ∅)
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (z : UL) :
    plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
      hDReverseΩ hne hirr hreg z = 1 := by
  have hj := conditionalCanonicalRationalScalar_eq_one_of_levi_eq_top χ hRefl hCST hG K hK hPK
    hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hlevi
  rw [plancherelWeight_eq, plancherelDensityConstant_eq_one_of_positiveRelativeRoots_eq_empty
    i ζ K hK hpos, rationalUnitaryValue_eq MS hMS hreg z (m := 1) (n := 1) (by simp)
      (by rw [hj]; simp)]
  simp

end FullRootWeight

/-! ### The Plancherel weight at the full simple-root index -/

section StandardFullRoot

open MeasureTheory
open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity

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
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] standardLeviPlancherelWeightLeviClosed
  standardLeviPlancherelWeightLeviAffine standardLeviPlancherelWeightLeviTopology

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
-- `M_I(F)` as a subtype of `G(F)`, written as in the wave-packet consumers.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- At the full simple-root index, the centralizer of a standard cocharacter `ζ ∘ i` is all
of `G(F)`. -/
theorem levi_eq_top_of_rootSet_eq_simpleRelativeRoots
    (hI : RationalPointFamily.rootSet i ν I = simpleRelativeRoots i ν) : levi χ = ⊤ := by
  have h1 := (Jacquet.standardLevi_eq_dynamic hG hi hν hζ).1
  have h0 := (Jacquet.standardLevi_eq_dynamic hG hi hν (ζ := 0)
    (J := RationalPointFamily.rootSet i ν I)
    (by rw [hI]; exact isStandardCocharacter_simple_zero i ν)).1
  rw [groupHom_zero_comp_eq_trivialCocharacter, Dynamic.centralizer_trivialCocharacter] at h0
  change (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) = ⊤
  rw [← h1, h0]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- At the full simple-root index, a standard cocharacter has no positive relative roots. -/
theorem positiveRelativeRoots_eq_empty_of_rootSet_eq_simpleRelativeRoots
    (hI : RationalPointFamily.rootSet i ν I = simpleRelativeRoots i ν) :
    positiveRelativeRoots i ζ = ∅ :=
  positiveRelativeRoots_eq_empty_of_isStandardCocharacter_simple i ν hν
    (relativeRootNegation F G hG S i hi) (hI ▸ hζ)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

-- The inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
-- The orbit `O = {π ⊗ z ; z ∈ Im X(M_I)}` of the class of `π`.
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitMapπ" => discreteSeriesOrbitMap C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `π ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

include hDForward hDReverse hD in
/-- At the full simple-root index `j_P⁻¹ = 1` is regular at every unitary character, so the
hypothesis of `standardLeviPlancherelWeight` holds. -/
theorem rationalFunctionUnitaryRegular_inv_of_rootSet_eq_simpleRelativeRoots
    (hI : RationalPointFamily.rootSet i ν I = simpleRelativeRoots i ν) :
    RationalFunctionUnitaryRegular MS hMS (jP)⁻¹ :=
  rationalFunctionUnitaryRegular_inv_of_levi_eq_top i ζ hRefl hCST hG K hK hPK hOppK Aπ p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    (levi_eq_top_of_rootSet_eq_simpleRelativeRoots hG hi hν I hζ hI)

include hDForward hDReverse hD in
/-- **The Plancherel weight at the full simple-root index is `1`.** If the index `I` is the
whole set of simple relative roots (so `M_I = P_I = G` and `U_I = 1`), then the Plancherel
weight `π ⊗ z ↦ μ(π ⊗ z)` on the orbit of `π`, built from the actual canonical scalar `j_P` at
the scale `K`, is the constant `1`. -/
theorem standardLeviPlancherelWeight_eq_one_of_rootSet_eq_simpleRelativeRoots
    (hI : RationalPointFamily.rootSet i ν I = simpleRelativeRoots i ν)
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (ω : Oπ) :
    standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg ω =
      1 := by
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (discreteSeriesClass C hC mu π hsq)).surjective ω
  rw [standardLeviPlancherelWeight_orbitMap]
  exact plancherelWeight_eq_one_of_levi_eq_top i ζ hRefl hCST hG K hK hPK hOppK Aπ p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    (levi_eq_top_of_rootSet_eq_simpleRelativeRoots hG hi hν I hζ hI)
    (positiveRelativeRoots_eq_empty_of_rootSet_eq_simpleRelativeRoots hG hi hν I hζ hI) hreg _

end StandardFullRoot

end Langlands.Plancherel
