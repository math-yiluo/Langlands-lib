import Langlands.Representation.Plancherel.DynamicRepresentedInductionEvaluation
import Langlands.Representation.Intertwining.PQBoundaryVanishingCompactSupportProof
import Langlands.Representation.Plancherel.DynamicOppositeContinuedTests

/-! # Integral normalization under represented induction comparison -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviPresentationComparison
open DynamicCommonLeviStructuralComparison

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  equalitySubgroupMeasurable equalitySubgroupBorel

section Presentations

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ ψ₀ ψ₁ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (d₀ : ParabolicData χ ψ₀ T a) (d₁ : ParabolicData χ ψ₁ T a)
  (hψ₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ)
  (hψ₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer χ)
  (B : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "σ" => SmoothRep.pullback (parameterHomeomorph χ) B
set_option quotPrecheck false in
local notation "I₀" => (leviInductionFunctor d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic
  d₀.radical d₀.r.isCompatible.levi (multiplication_isIso hG d₀)).obj σ
set_option quotPrecheck false in
local notation "I₁" => (leviInductionFunctor d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic
  d₁.radical d₁.r.isCompatible.levi (multiplication_isIso hG d₁)).obj σ
set_option quotPrecheck false in
local notation "A₀" => (DynamicNormalization.leviTwistedInductionFunctor
  (commonDecomposition χ ψ₀ hψ₀) (radical_isClosed ψ₀)).obj B
set_option quotPrecheck false in
local notation "A₁" => (DynamicNormalization.leviTwistedInductionFunctor
  (commonDecomposition χ ψ₁ hψ₁) (radical_isClosed ψ₁)).obj B
local notation "E₀" => representedDynamicInductionEquiv hG d₀ hψ₀ B
local notation "E₁" => representedDynamicInductionEquiv hG d₁ hψ₁ B

/-- Transfer an actual common-Levi intertwiner to its represented endpoints. -/
def representedDynamicIntertwiner
    (J : (A₀).representation.IntertwiningMap (A₁).representation) :
    (I₀).representation.IntertwiningMap (I₁).representation :=
  (E₁).symm.toIntertwiningMap.comp (J.comp (E₀).toIntertwiningMap)

/-- The represented complement used when the target is opposite to the source. -/
abbrev representedOppositeComplement : Subgroup (rationalPoints G) :=
  pointImage (d₁.n ≫ d₁.p) ⊓ pointImage (d₁.n ≫ d₁.p)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem representedOppositeComplement_eq : representedOppositeComplement d₁ = radical ψ₁ :=
  (inf_idem _).trans (pointImage_radical d₁)

/-- The original literal radical Haar measure on the represented complement. -/
def representedOppositeMeasure (measure : Measure (radical ψ₁)) :
    Measure (representedOppositeComplement d₁) :=
  subgroupMeasureOfEq (representedOppositeComplement_eq d₁) measure

instance representedOppositeMeasure_isHaar (measure : Measure (radical ψ₁)) [measure.IsHaarMeasure] :
    (representedOppositeMeasure d₁ measure).IsHaarMeasure :=
  subgroupMeasureOfEq_isHaar _ _

set_option maxHeartbeats 650000 in
/-- A compact-test formula in the actual ambient functions gives Renard's
integral normalization for the represented opposite pair at the same scale. -/
theorem isIntegralIntertwiner_of_compactTest
    (hOpp : pointImage d₀.p ⊓ pointImage d₁.p = pointImage (d₀.l ≫ d₀.p))
    (measure : Measure (radical ψ₁))
    (J : (A₀).representation.IntertwiningMap (A₁).representation)
    (hJ : ∀ f : A₀, HasCompactSupport (fun x : radical ψ₁ => eval _ _ f x.val) →
      ∀ ℓ : Module.Dual ℂ B,
        Integrable (fun x : radical ψ₁ => ℓ (eval _ _ f x.val)) measure ∧
        ℓ (eval _ _ (J f) 1) = ∫ x : radical ψ₁, ℓ (eval _ _ f x.val) ∂measure) :
    IsIntegralIntertwiner d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.radical
      d₀.r.isCompatible.levi (multiplication_isIso hG d₀)
      d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.radical
      d₁.r.isCompatible.levi (multiplication_isIso hG d₁)
      (representedOppositeComplement d₁) (representedOppositeMeasure d₁ measure) σ
      (representedDynamicIntertwiner hG d₀ d₁ hψ₀ hψ₁ B J) := by
  intro f hf ℓ
  have hsame := d₀.levi_comp.trans d₁.levi_comp.symm
  obtain ⟨C, hC, hvan⟩ := (pqBoundaryVanishingCompactSupport.{u, uV} F G hG
    d₀.P (parameterScheme χ) d₀.U d₁.P d₁.U d₁.P d₁.U
    d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.r.isCompatible.levi d₀.radical
    (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi d₁.radical
    (multiplication_isIso hG d₁)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi d₁.radical
    (multiplication_isIso hG d₁) hsame hsame.symm hOpp σ f).mp hf
  let V := representedOppositeComplement d₁
  let m := subgroupHomeomorphOfEq (representedOppositeComplement_eq d₁)
  have hmem (x : V) : eval _ _ (E₀ f) (m x : rationalPoints G) = eval _ _ f x.val :=
    (representedDynamicInductionEquiv_eval hG d₀ hψ₀ B f (m x : rationalPoints G)).trans
      (congrArg (eval _ _ f) (subgroupHomeomorphOfEq_coe _ x))
  have hc : HasCompactSupport (fun y : radical ψ₁ => eval _ _ (E₀ f) y.val) := by
    refine HasCompactSupport.intro (hC.image m.continuous) (fun y hy => ?_)
    obtain ⟨x, rfl⟩ := m.surjective y
    exact (hmem x).trans (hvan x (fun hx => hy ⟨x, hx, rfl⟩))
  obtain ⟨hInt, hEval⟩ := hJ (E₀ f) hc ℓ
  have hμ : MeasurePreserving m (representedOppositeMeasure d₁ measure) measure :=
    ⟨m.continuous.measurable, subgroupMeasureOfEq_map _ _⟩
  have htest : (fun x : V => ℓ (eval _ _ (E₀ f) (m x : rationalPoints G))) =
      fun x => ℓ (eval _ _ f x.val) := funext fun x => congrArg ℓ (hmem x)
  have hout : eval _ _ (representedDynamicIntertwiner hG d₀ d₁ hψ₀ hψ₁ B J f) 1 =
      eval _ _ (J (E₀ f)) 1 :=
    (representedDynamicInductionEquiv_eval hG d₁ hψ₁ B _ 1).symm.trans
      (congrArg (fun g : A₁ => eval _ _ g 1) ((E₁).apply_symm_apply (J (E₀ f))))
  refine ⟨htest ▸ (hμ.integrable_comp_emb m.toHomeomorph.measurableEmbedding).mpr hInt, ?_⟩
  exact (congrArg ℓ hout).trans (hEval.trans
    ((hμ.integral_comp m.toHomeomorph.measurableEmbedding _).symm.trans
      (congrArg (fun b : V → ℂ => ∫ x, b x ∂representedOppositeMeasure d₁ measure) htest)))

end Presentations

section ActualOpposite

open DynamicOppositeCanonicalScalar DynamicOppositeContinuedTests
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningMeasurableSpace2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningBorelSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (d : ParabolicData χ χ T a) (d' : ParabolicData χ (Dynamic.inverseCocharacter χ) T a)

local notation "hOppLevi" => Dynamic.centralizer_inverseCocharacter χ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The represented endpoint parabolics intersect in the original Levi. -/
theorem pointImage_inter_opposite :
    pointImage d.p ⊓ pointImage d'.p = pointImage (d.l ≫ d.p) := by
  calc
    _ = parabolic χ ⊓ oppositeParabolic χ :=
      congrArg₂ (· ⊓ ·) (pointImage_parabolic d) (pointImage_parabolic d')
    _ = levi χ := congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      (Dynamic.parabolic_inf_opposite_eq_centralizer χ)
    _ = _ := (pointImage_levi d).symm

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option quotPrecheck false in
local notation "twisted" => (fun z : unramifiedCharacters (normCharacters χ) =>
  A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z)))

section Forward

variable (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ forwardFullDomainRegion χ K hK A)

local notation "J" => forwardIntertwiner χ hRefl hCST hG K hK hPK hOppK A p hD hne hDΩ
local notation "haar" => oppositeRadicalHaar χ K hK

set_option maxHeartbeats 650000 in
/-- The original forward continuation satisfies Renard's formula at the
original radical Haar scale throughout its regular region. -/
theorem forwardIntertwiner_isIntegral (z : p.regularRegion) :
    IsIntegralIntertwiner d.p d.l d.n d.r.isCompatible.parabolic d.radical
      d.r.isCompatible.levi (multiplication_isIso hG d)
      d'.p d'.l d'.n d'.r.isCompatible.parabolic d'.radical
      d'.r.isCompatible.levi (multiplication_isIso hG d')
      (representedOppositeComplement d') (representedOppositeMeasure d' haar)
      (SmoothRep.pullback (parameterHomeomorph χ) (twisted z.val))
      (representedDynamicIntertwiner hG d d' rfl hOppLevi (twisted z.val) (J z)) := by
  exact isIntegralIntertwiner_of_compactTest hG d d' rfl hOppLevi
    (twisted z.val) (pointImage_inter_opposite d d') haar (J z)
    (fun f hf ℓ => forwardIntertwiner_compactTest χ hRefl hCST hG K hK hPK hOppK A
      p hD hne hDΩ z f hf ℓ)

end Forward

section Reverse

variable (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ reverseFullDomainRegion χ K hK A)

local notation "J" => reverseIntertwiner χ hRefl hCST hG K hK hPK hOppK A q hD hne hDΩ
local notation "haar" => radicalHaar χ K hK

set_option maxHeartbeats 650000 in
/-- The original reverse continuation satisfies Renard's formula at the
original radical Haar scale throughout its regular region. -/
theorem reverseIntertwiner_isIntegral (z : q.regularRegion) :
    IsIntegralIntertwiner d'.p d'.l d'.n d'.r.isCompatible.parabolic d'.radical
      d'.r.isCompatible.levi (multiplication_isIso hG d')
      d.p d.l d.n d.r.isCompatible.parabolic d.radical
      d.r.isCompatible.levi (multiplication_isIso hG d)
      (representedOppositeComplement d) (representedOppositeMeasure d haar)
      (SmoothRep.pullback (parameterHomeomorph χ) (twisted z.val))
      (representedDynamicIntertwiner hG d' d hOppLevi rfl (twisted z.val) (J z)) := by
  have hOpp : pointImage d'.p ⊓ pointImage d.p = pointImage (d'.l ≫ d'.p) :=
    (inf_comm _ _).trans ((pointImage_inter_opposite d d').trans
      ((pointImage_levi d).trans (pointImage_levi d').symm))
  exact isIntegralIntertwiner_of_compactTest hG d' d hOppLevi rfl
    (twisted z.val) hOpp haar (J z)
    (fun f hf ℓ => reverseIntertwiner_compactTest χ hRefl hCST hG K hK hPK hOppK A
      q hD hne hDΩ z f hf ℓ)

end Reverse

end ActualOpposite

end Langlands.Plancherel.DynamicCommonLeviPresentations
