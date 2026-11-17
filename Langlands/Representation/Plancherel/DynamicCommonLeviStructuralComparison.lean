import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationComparison

/-! # Canonical maps from complete presentations to actual common-Levi data -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW uA uB uI uJ

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviStructuralComparison

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviPresentationComparison

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
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

section EqualSubgroups

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup H}
  (eP : P₀ = P₁) (eM : M₀ = M₁) (eU : U₀ = U₁)
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (K : OpenSubgroup H) (A : SmoothRep.{0, u, uV} ℂ M₁)

/-- Equal literal subgroups give the same compact sections and K action. -/
def compactPictureComparisonOfEq :
    (smoothInduced (P₀.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h₀ K (representationOfEq eM A))).Equiv
    (smoothInduced (P₁.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h₁ K A)) := by
  subst P₁
  subst M₁
  subst U₁
  exact smoothInducedEquiv _ (equivOfRepresentationEq (by rfl))

@[simp]
theorem compactPictureComparisonOfEq_eval
    (f : CompactInductionPicture h₀ K (representationOfEq eM A)) (k : K) :
    eval _ _ (compactPictureComparisonOfEq eP eM eU h₀ h₁ K A f) k = eval _ _ f k := by
  subst P₁
  subst M₁
  subst U₁
  rfl

variable (hU₀ : IsClosed (U₀ : Set H)) (hU₁ : IsClosed (U₁ : Set H))

include eU in
/-- Semidirect projections agree on the actual ambient elements. -/
theorem projectionComparisonOfEq (p : P₀) :
    subgroupHomeomorphOfEq eM (h₀.projection p) =
      h₁.projection (subgroupHomeomorphOfEq eP p) := by
  subst P₁
  subst M₁
  subst U₁
  rfl

include eP eU in
/-- Equality transports the actual positive Haar half-modulus. -/
theorem halfCharacterComparisonOfEq (m : M₀) :
    HaarModulus.closedHalfCharacter U₀ hU₀ M₀ h₀.levi_le_normalizer m =
      HaarModulus.closedHalfCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer
        (subgroupHomeomorphOfEq eM m) := by
  subst P₁
  subst M₁
  subst U₁
  rfl

/-- The actual positive Levi half character and projection transport together.
Both normalized inductions consist of the same ambient functions. -/
def leviInductionComparisonOfEq :
    ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM A)).representation.Equiv
    ((DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A).representation := by
  subst P₁
  subst M₁
  subst U₁
  exact smoothInducedEquiv _ (equivOfRepresentationEq (by rfl))

@[simp]
theorem leviInductionComparisonOfEq_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM A)) (x : H) :
    eval _ _ (leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f) x =
      eval _ _ f x := by
  subst P₁
  subst M₁
  subst U₁
  rfl

end EqualSubgroups

section EqualMeasures

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {U₀ V₀ U₁ V₁ : Subgroup H}

local instance equalitySubgroupMeasurable (U : Subgroup H) : MeasurableSpace U := borel _
local instance equalitySubgroupBorel (U : Subgroup H) : BorelSpace U := ⟨rfl⟩
local instance equalityIntersectionMeasurable (U V : Subgroup H) :
    MeasurableSpace (U.subgroupOf V) := borel _
local instance equalityIntersectionBorel (U V : Subgroup H) :
    BorelSpace (U.subgroupOf V) := ⟨rfl⟩
local instance equalityQuotientMeasurable (U V : Subgroup H) :
    MeasurableSpace (QuotientSpace (U := U) V) := borel _
local instance equalityQuotientBorel (U V : Subgroup H) :
    BorelSpace (QuotientSpace (U := U) V) := ⟨rfl⟩

/-- The actual intersection map only changes proofs of subgroup membership. -/
def intersectionComparisonOfEq (eU : U₀ = U₁) (eV : V₀ = V₁) :
    U₀.subgroupOf V₀ ≃ₜ* U₁.subgroupOf V₁ := by
  subst U₁
  subst V₁
  exact ContinuousMulEquiv.refl _

@[simp]
theorem intersectionComparisonOfEq_coe (eU : U₀ = U₁) (eV : V₀ = V₁)
    (x : U₀.subgroupOf V₀) :
    (intersectionComparisonOfEq eU eV x).val.val = x.val.val := by
  subst U₁
  subst V₁
  rfl

/-- The actual left quotient map is induced by the identity ambient element. -/
def quotientComparisonOfEq (eU : U₀ = U₁) (eV : V₀ = V₁) :
    QuotientSpace (U := U₀) V₀ ≃ₜ QuotientSpace (U := U₁) V₁ := by
  subst U₁
  subst V₁
  exact Homeomorph.refl _

@[simp]
theorem quotientComparisonOfEq_mk (eU : U₀ = U₁) (eV : V₀ = V₁) (x : V₀) :
    quotientComparisonOfEq eU eV (Quotient.mk _ x) =
      Quotient.mk _ (subgroupHomeomorphOfEq eV x) := by
  subst U₁
  subst V₁
  rfl

/-- Pull back the specified source measure, with its scale unchanged. -/
def subgroupMeasureOfEq (eV : V₀ = V₁) (μV : Measure V₁) : Measure V₀ :=
  Measure.map (subgroupHomeomorphOfEq eV).symm μV

def intersectionMeasureOfEq (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μV : Measure (U₁.subgroupOf V₁)) : Measure (U₀.subgroupOf V₀) :=
  Measure.map (intersectionComparisonOfEq eU eV).symm μV

def quotientMeasureOfEq (eU : U₀ = U₁) (eV : V₀ = V₁)
    (ν : Measure (QuotientSpace (U := U₁) V₁)) :
    Measure (QuotientSpace (U := U₀) V₀) :=
  Measure.map (quotientComparisonOfEq eU eV).symm ν

@[simp]
theorem subgroupMeasureOfEq_map (eV : V₀ = V₁) (μV : Measure V₁) :
    Measure.map (subgroupHomeomorphOfEq eV) (subgroupMeasureOfEq eV μV) = μV := by
  subst V₁
  change Measure.map id (Measure.map id μV) = μV
  simp only [Measure.map_id]

@[simp]
theorem intersectionMeasureOfEq_map (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μI : Measure (U₁.subgroupOf V₁)) :
    Measure.map (intersectionComparisonOfEq eU eV) (intersectionMeasureOfEq eU eV μI) =
      μI := by
  subst U₁
  subst V₁
  change Measure.map id (Measure.map id μI) = μI
  simp only [Measure.map_id]

@[simp]
theorem quotientMeasureOfEq_map (eU : U₀ = U₁) (eV : V₀ = V₁)
    (ν : Measure (QuotientSpace (U := U₁) V₁)) :
    Measure.map (quotientComparisonOfEq eU eV) (quotientMeasureOfEq eU eV ν) = ν := by
  subst U₁
  subst V₁
  change Measure.map id (Measure.map id ν) = ν
  simp only [Measure.map_id]

instance subgroupMeasureOfEq_isHaar (eV : V₀ = V₁) (μV : Measure V₁)
    [IsHaarMeasure μV] : IsHaarMeasure (subgroupMeasureOfEq eV μV) := by
  subst V₁
  change IsHaarMeasure (Measure.map id μV)
  simpa only [Measure.map_id] using
    (inferInstance : IsHaarMeasure μV)

instance subgroupMeasureOfEq_regular (eV : V₀ = V₁) (μV : Measure V₁)
    [μV.Regular] : (subgroupMeasureOfEq eV μV).Regular := by
  subst V₁
  change (Measure.map id μV).Regular
  simpa only [Measure.map_id] using
    (inferInstance : μV.Regular)

instance subgroupMeasureOfEq_rightInvariant (eV : V₀ = V₁) (μV : Measure V₁)
    [IsMulRightInvariant μV] : IsMulRightInvariant (subgroupMeasureOfEq eV μV) := by
  subst V₁
  change IsMulRightInvariant (Measure.map id μV)
  simpa only [Measure.map_id] using
    (inferInstance : IsMulRightInvariant μV)

instance intersectionMeasureOfEq_isHaar (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μV : Measure (U₁.subgroupOf V₁)) [IsHaarMeasure μV] :
    IsHaarMeasure (intersectionMeasureOfEq eU eV μV) := by
  subst U₁
  subst V₁
  change IsHaarMeasure (Measure.map id μV)
  simpa only [Measure.map_id] using
    (inferInstance : IsHaarMeasure μV)

instance intersectionMeasureOfEq_regular (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μV : Measure (U₁.subgroupOf V₁)) [μV.Regular] :
    (intersectionMeasureOfEq eU eV μV).Regular := by
  subst U₁
  subst V₁
  change (Measure.map id μV).Regular
  simpa only [Measure.map_id] using
    (inferInstance : μV.Regular)

instance intersectionMeasureOfEq_rightInvariant (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μV : Measure (U₁.subgroupOf V₁)) [IsMulRightInvariant μV] :
    IsMulRightInvariant (intersectionMeasureOfEq eU eV μV) := by
  subst U₁
  subst V₁
  change IsMulRightInvariant (Measure.map id μV)
  simpa only [Measure.map_id] using
    (inferInstance : IsMulRightInvariant μV)

/-- All fields of complex Weil compatibility survive the constructed maps. -/
theorem quotientMeasureOfEq_isCompatible (eU : U₀ = U₁) (eV : V₀ = V₁)
    (μV : Measure V₁) (μI : Measure (U₁.subgroupOf V₁))
    [IsMulRightInvariant μI] (ν : Measure (QuotientSpace (U := U₁) V₁))
    (hν : QuotientIntegration.IsCompatible (U₁.subgroupOf V₁) μV μI ν) :
    QuotientIntegration.IsCompatible (U₀.subgroupOf V₀)
      (subgroupMeasureOfEq eV μV) (intersectionMeasureOfEq eU eV μI)
      (quotientMeasureOfEq eU eV ν) := by
  subst U₁
  subst V₁
  haveI : IsMulRightInvariant (Measure.map id μI) := by
    simpa only [Measure.map_id] using (inferInstance : IsMulRightInvariant μI)
  change QuotientIntegration.IsCompatible (U₀.subgroupOf V₀)
    (Measure.map id μV) (Measure.map id μI) (Measure.map id ν)
  simpa only [Measure.map_id] using hν

end EqualMeasures

section ActualPresentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : T.toGrp ⟶ M} {n : U ⟶ P}
  (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (r : ParabolicRootPresentation p l a) (s : Realizes χ ψ p l n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))
  (K : OpenSubgroup (rationalPoints G))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- The canonical common-Levi action on the presentation's original carrier. -/
abbrev presentationRepresentation :=
  representationOfEq (leviPoints_eq χ ψ s) A

/-- Identity on compact sections, with the literal source and dynamic target. -/
def compactPictureComparison :
    (smoothInduced
      (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))).comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K (presentationRepresentation χ ψ s A))).Equiv
    (smoothInduced ((parabolic ψ).comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation (commonDecomposition χ ψ hψ) K A)) :=
  compactPictureComparisonOfEq (parabolicPoints_eq χ ψ s) (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ s) h (commonDecomposition χ ψ hψ) K A

@[simp]
theorem compactPictureComparison_eval
    (f : CompactInductionPicture h K (presentationRepresentation χ ψ s A)) (k : K) :
    eval _ _ (compactPictureComparison χ ψ hψ s h K A f) k = eval _ _ f k :=
  compactPictureComparisonOfEq_eval _ _ _ _ _ _ _ _ _

/-- Actual positive Levi-normalized functions compare by the ambient identity. -/
def leviInductionComparison :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj
      (presentationRepresentation χ ψ s A)).representation.Equiv
    ((DynamicNormalization.leviTwistedInductionFunctor
      (commonDecomposition χ ψ hψ) (radical_isClosed ψ)).obj A).representation :=
  leviInductionComparisonOfEq (parabolicPoints_eq χ ψ s) (leviPoints_eq χ ψ s)
    (radicalPoints_eq χ ψ s) h (commonDecomposition χ ψ hψ) A hU (radical_isClosed ψ)

@[simp]
theorem leviInductionComparison_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj
      (presentationRepresentation χ ψ s A)) (x : rationalPoints G) :
    eval _ _ (leviInductionComparison χ ψ hψ s h hU A f) x = eval _ _ f x :=
  leviInductionComparisonOfEq_eval _ _ _ _ _ _ _ _ _ _

/-- Both unramified characters act by the same scalar on each original
Levi element. Their norm-index sets need not coincide. -/
theorem characterComparison_parameterTransport
    (z : unramifiedCharacters (normCharacters χ)) (m : parabolicLeviPointSubgroup p l) :
    (characterComparison χ ψ r s z).val m =
      (parameterTransport χ z).val (leviPointComparison χ ψ s m) := rfl

/-- Transporting the twist preserves the actual inducing linear action. -/
theorem twistedRepresentation_eq (z : unramifiedCharacters (normCharacters χ)) :
    (presentationRepresentation χ ψ s
      (A.twist (parameterTransport χ z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))).representation =
    ((presentationRepresentation χ ψ s A).twist (characterComparison χ ψ r s z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r)
        (characterComparison χ ψ r s z))).representation := rfl

/-- At corresponding characters the varying induced spaces have the same
ambient functions, including their positive normalization. -/
def unramifiedInductionComparison (z : unramifiedCharacters (normCharacters χ)) :
    (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r)
      (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)).representation.Equiv
    (UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z) A).representation :=
  leviInductionComparison χ ψ hψ s h hU
    (A.twist (parameterTransport χ z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))

@[simp]
theorem unramifiedInductionComparison_eval (z : unramifiedCharacters (normCharacters χ))
    (f : UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r)
      (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A))
    (x : rationalPoints G) :
    eval _ _ (unramifiedInductionComparison χ ψ hψ r s h hU A z f) x = eval _ _ f x :=
  leviInductionComparison_eval _ _ _ _ _ _ _ _ _

/-- The source and canonical compact restrictions form the actual square. -/
theorem compactRestriction_comparison
    (hδ : IsUnimodularModulus _ hU)
    (hP : IsClosed (((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _))) :
      Set (rationalPoints G)))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : ∀ g : rationalPoints G,
      ∃ p₀ : (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)), ∃ k : K,
        g = (p₀ : rationalPoints G) * (k : rationalPoints G))
    (hr : Continuous h.projection) (hG : IsConnectedReductive G)
    (hψK : ∀ g : rationalPoints G, ∃ p₀ : parabolic ψ, ∃ k : K,
      g = (p₀ : rationalPoints G) * (k : rationalPoints G))
    (z : unramifiedCharacters (normCharacters χ))
    (f : UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r)
      (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A)) :
    compactPictureComparison χ ψ hψ s h K A
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
        (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
        hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A) f) =
    compactEquiv χ hG K hK ψ hψ hψK z A
      (unramifiedInductionComparison χ ψ hψ r s h hU A z f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change eval _ _ (compactPictureComparison χ ψ hψ s h K A
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK
      (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
      hr (characterComparison χ ψ r s z) (presentationRepresentation χ ψ s A) f)) k =
    eval _ _ (compactEquiv χ hG K hK ψ hψ hψK z A
      (unramifiedInductionComparison χ ψ hψ r s h hU A z f)) k
  rw [compactPictureComparison_eval, unramifiedLeviInductionCompactEquiv_eval,
    compactEquiv_eval, unramifiedInductionComparison_eval]

attribute [local instance] equalitySubgroupMeasurable equalitySubgroupBorel
  equalityIntersectionMeasurable equalityIntersectionBorel
  equalityQuotientMeasurable equalityQuotientBorel

variable {P' U' : GroupScheme (Spec (CommRingCat.of F))}
  {p' : P' ⟶ G} {l' : M ⟶ P'} {n' : U' ⟶ P'}
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (s' : Realizes χ ψ' p' l' n')
  (hK : IsCompact (K : Set (rationalPoints G)))

/-- Source target-radical Haar is pulled back from the actual scale `K`. -/
def presentationRadicalHaar :
    Measure ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))) :=
  subgroupMeasureOfEq (radicalPoints_eq χ ψ' s') (radicalHaar ψ' K hK)

/-- Source intersection Haar is pulled back from the same actual scale. -/
def presentationIntersectionHaar :
    Measure (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))).subgroupOf
      ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))) :=
  intersectionMeasureOfEq (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s')
    (pairIntersectionHaar K hK ψ ψ')

/-- Source quotient measure is the inverse image of the actual pair measure,
not a newly normalized Haar choice. -/
def presentationQuotientMeasure :
    Measure (QuotientSpace
      (U := (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
      ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))) :=
  quotientMeasureOfEq (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s')
    (pairQuotientMeasure K hK ψ ψ')

@[simp]
theorem presentationRadicalHaar_map :
    Measure.map (subgroupHomeomorphOfEq (radicalPoints_eq χ ψ' s'))
      (presentationRadicalHaar χ K ψ' s' hK) = radicalHaar ψ' K hK :=
  subgroupMeasureOfEq_map _ _

@[simp]
theorem presentationIntersectionHaar_map :
    Measure.map (intersectionComparisonOfEq (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s'))
      (presentationIntersectionHaar χ ψ s K ψ' s' hK) = pairIntersectionHaar K hK ψ ψ' :=
  intersectionMeasureOfEq_map _ _ _

@[simp]
theorem presentationQuotientMeasure_map :
    Measure.map (quotientComparisonOfEq (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s'))
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) = pairQuotientMeasure K hK ψ ψ' :=
  quotientMeasureOfEq_map _ _ _

instance presentationRadicalHaar_isHaar :
    IsHaarMeasure (presentationRadicalHaar χ K ψ' s' hK) := by
  unfold presentationRadicalHaar
  infer_instance

instance presentationRadicalHaar_regular :
    (presentationRadicalHaar χ K ψ' s' hK).Regular := by
  unfold presentationRadicalHaar
  infer_instance

instance presentationRadicalHaar_rightInvariant :
    IsMulRightInvariant (presentationRadicalHaar χ K ψ' s' hK) := by
  unfold presentationRadicalHaar
  infer_instance

instance presentationIntersectionHaar_isHaar :
    IsHaarMeasure (presentationIntersectionHaar χ ψ s K ψ' s' hK) := by
  unfold presentationIntersectionHaar
  infer_instance

instance presentationIntersectionHaar_regular :
    (presentationIntersectionHaar χ ψ s K ψ' s' hK).Regular := by
  unfold presentationIntersectionHaar
  infer_instance

instance presentationIntersectionHaar_rightInvariant :
    IsMulRightInvariant (presentationIntersectionHaar χ ψ s K ψ' s' hK) := by
  unfold presentationIntersectionHaar
  infer_instance

/-- The precise three transported source measures satisfy every Weil field. -/
theorem presentationQuotientMeasure_isCompatible :
    QuotientIntegration.IsCompatible
      (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))).subgroupOf
        ((SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _))))
      (presentationRadicalHaar χ K ψ' s' hK)
      (presentationIntersectionHaar χ ψ s K ψ' s' hK)
      (presentationQuotientMeasure χ ψ s K ψ' s' hK) :=
  quotientMeasureOfEq_isCompatible (radicalPoints_eq χ ψ s) (radicalPoints_eq χ ψ' s')
    _ _ _ (pairQuotientMeasure_isCompatible K hK ψ ψ')

end ActualPresentation

end Langlands.Plancherel.DynamicCommonLeviStructuralComparison
