import Langlands.Representation.Plancherel.ActualConjugateLeviFiberTransport
import Langlands.Representation.Plancherel.WaldspurgerSourceNormalization

/-! # Closed V.3.2 target for the actual translated coefficient comparisons -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types true

universe u uV uS uM uT

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviCoherence

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open ActualCommonLeviCoherence ActualConjugateLeviFiberTransport
open ActualParabolicTranslation ActualParabolicUnitaryTranslation WaldspurgerSourceNormalization

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
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Cochar" => (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
set_option hygiene false in
local notation "Gpts" => RationalPoint F G.X

private abbrev conjugateAnchor (χ : Cochar) (g : Gpts) : Cochar := χ ≫ (G.innerIso g).hom

local instance leviLocallyCompact (χ : Cochar) : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

/-- The inducing discrete series and the split-central quotient Haar data
used to define its positive form and coefficients. -/
structure LeviNormalization (χ : Cochar) (A : SmoothRep.{0, u, uV} ℂ (levi χ)) where
  center : Subgroup (levi χ)
  central : center ≤ Subgroup.center (levi χ)
  [normal : center.Normal]
  [quotientMeasurable : MeasurableSpace (levi χ ⧸ center)]
  [quotientBorel : BorelSpace (levi χ ⧸ center)]
  quotientMeasure : Measure (levi χ ⧸ center)
  [quotientHaar : quotientMeasure.IsHaarMeasure]
  [quotientInversion : quotientMeasure.IsInvInvariant]
  splitCenter : ActualCommonLeviV3.IsActualSplitCenter χ center
  squareIntegrable : IsSquareIntegrableModCentralSubgroup center central A.representation quotientMeasure
  irreducible : A.representation.IsIrreducible

attribute [local instance] LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

section NormalizedFiber

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (d : LeviNormalization χ A)
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts))
  (P : ParabolicPresentation χ K)
  (z : unitaryUnramifiedCharacters (normCharacters χ))

/-- The actual special compact for the anchor Levi and the absolute Weil
quotient Haar scale on that Levi. -/
def HasSourceNormalization : Prop :=
  IsSourceCompactFor χ K.toSubgroup ∧ IsSourceQuotientHaar χ K d.center d.quotientMeasure

/-- The published coefficient map with the displayed quotient measure and
the compact Haar probability. -/
def coefficientMap : fiber χ A K P z →ₗ[ℂ] LocallyConstant Gpts ℂ :=
  ActualCommonLeviV3.coefficientMap χ hG A d.center d.central d.quotientMeasure
    d.squareIntegrable K hK P.cocharacter P.centralizer_eq P.iwasawa z

/-- The published form with inverse formal degree from the same Haar data. -/
def formalDegreeForm : InvariantPositiveForm (fiber χ A K P z).representation :=
  ActualCommonLeviV3.formalDegreeForm χ hG A d.center d.central d.quotientMeasure
    d.squareIntegrable d.irreducible K hK P.cocharacter P.centralizer_eq P.iwasawa z

end NormalizedFiber

section Arrow

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (g : K)

set_option hygiene false in
local notation "χg" => conjugateAnchor χ (g : Gpts)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ (g : Gpts) A
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ (g : Gpts)
set_option hygiene false in
local notation "hKK" => RationalDynamicSource.conjugateCompact_eq_self (g : Gpts) K g.property

variable (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)

/-- Compatibility of the exact source and target quotient Haar measures under
inverse conjugation of the literal split-central quotients. -/
def CompatibleHaar : Prop :=
  let e := (leviConjugation χ (g : Gpts)).symm
  ∃ hc : dg.center.map e.toMonoidHom = d.center,
    dg.quotientMeasure.map
      (Langlands.HarishChandraSchwartz.quotientContinuousMulEquiv e d.center dg.center hc) =
        d.quotientMeasure

/-- Actual conjugation transports the special compact and both quotient
trace normalizations for a rational point of the compact. -/
theorem hasSourceNormalization_conjugate (hd : HasSourceNormalization χ A d K)
    (hc : CompatibleHaar χ A K g d dg) : HasSourceNormalization χg Ag dg K := by
  obtain ⟨hC, hμ⟩ := hc
  exact ⟨isSourceCompactFor_conjugate χ K g K hKK hd.1,
    isSourceQuotientHaar_conjugate χ K g K hKK d.center dg.center hC
      d.quotientMeasure dg.quotientMeasure hμ hd.2⟩

variable (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χg K)

set_option hygiene false in
local notation "Pg" => conjugatePresentation χ (g : Gpts) K K hKK P

/-- The actual translated comparison between the displayed unitary fibers. -/
abbrev ComparisonFamily :=
  ∀ z : unitaryUnramifiedCharacters (normCharacters χ),
    (fiber χ A K P z).representation.IntertwiningMap
      (fiber χg Ag K Q (zg z)).representation

/-- The exact normalized coefficient and form identities on the source and
target of a translated comparison. -/
def PreservesCoefficientsAndForms (T : ComparisonFamily χ A K g P Q) : Prop :=
  ∀ (z : unitaryUnramifiedCharacters (normCharacters χ)),
    Function.Bijective (T z) ∧
    (∀ v : fiber χ A K P z,
      coefficientMap χg hG Ag dg K hK Q (zg z) (T z v) =
        coefficientMap χ hG A d K hK P z v) ∧
    ∀ v w : fiber χ A K P z,
      (formalDegreeForm χg hG Ag dg K hK Q (zg z)).inner (T z v) (T z w) =
        (formalDegreeForm χ hG A d K hK P z).inner v w

/-- A translated comparison comes from actual target-side common-Levi
continuations and the separately constructed actual left translation. -/
def IsActualComparison (T : ComparisonFamily χ A K g P Q) : Prop :=
  HasSourceNormalization χ A d K ∧ CompatibleHaar χ A K g d dg ∧
  ∃ U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq,
    ActualCommonLeviCoherence.IsActualNormalizedComparison χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK Pg Q U ∧
    HEq T (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U) ∧
    PreservesCoefficientsAndForms χ hG A K hK g d dg P Q T

/-- A family together with its actual standard-operator specification. -/
abbrev ActualComparison :=
  {T : ComparisonFamily χ A K g P Q // IsActualComparison χ hG A K hK g d dg P Q T}

end Arrow

/-- Pointwise equality through a specified fiber transport, allowing the
domain and range to be presented by definitionally equal expressions. -/
def TransportedValue {V V' : Type uS} {W W' : Type uT}
    (E : V → W) (v : V') (w : W') : Prop :=
  ∃ x : V, HEq x v ∧ HEq (E x) w

theorem transportedValue_iff {V W : Type*} (E : V → W) (v : V) (w : W) :
    TransportedValue E v w ↔ E v = w :=
  ⟨fun ⟨x, hx, hw⟩ => (congrArg E (show x = v from eq_of_heq hx)).symm.trans (eq_of_heq hw),
    fun h => ⟨v, HEq.rfl, heq_of_eq h⟩⟩

/-- Pointwise composition when the intermediate fiber has two
definitionally equal presentations. -/
def TransportedComposite {U U' : Type uS} {V V' : Type uM} {W W' : Type uT}
    (E : V → W) (T : U → V') (x : U') (w : W') : Prop :=
  ∃ v : U, HEq v x ∧ TransportedValue E (T v) w

theorem transportedComposite_iff {U V W : Type*} (E : V → W) (T : U → V) (x : U) (w : W) :
    TransportedComposite E T x w ↔ E (T x) = w := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact (congrArg (E ∘ T) (eq_of_heq hv)).symm.trans ((transportedValue_iff E _ _).mp h)
  · intro h
    exact ⟨x, HEq.rfl, (transportedValue_iff E _ _).mpr h⟩

/-- The two inverse equations through a specified return transport. -/
def TransportedInverse {U U' : Type uS} {V V' : Type uM} {W W' : Type uT}
    (E : V → W) (S : U → V') (T : W' → U') : Prop :=
  (∀ w : W', TransportedComposite E S (T w) w) ∧
    ∀ u : U, ∃ w : W', TransportedComposite E S u w ∧ HEq (T w) u

theorem transportedInverse_iff {U V W : Type*} (E : V → W) (S : U → V) (T : W → U) :
    TransportedInverse E S T ↔
      Function.LeftInverse (E ∘ S) T ∧ Function.RightInverse (E ∘ S) T := by
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨fun w => (transportedComposite_iff E S _ _).mp (hL w), ?_⟩
    intro u
    obtain ⟨w, hw, h⟩ := hR u
    exact (congrArg T ((transportedComposite_iff E S _ _).mp hw)).trans (eq_of_heq h)
  · rintro ⟨hL, hR⟩
    exact ⟨fun w => (transportedComposite_iff E S _ _).mpr (hL w),
      fun u => ⟨E (S u), (transportedComposite_iff E S _ _).mpr rfl, heq_of_eq (hR u)⟩⟩

section Coherence

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts))
  (d : LeviNormalization χ A)

local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)

/-- The continuations and regular translated families are conclusions for
each displayed pair of normalized conjugate data. -/
def ExistenceLaw : Prop :=
  ∀ (g : K) (dg : LeviNormalization (conjugateAnchor χ g) (conjugateRepresentation χ g A))
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation (conjugateAnchor χ g) K),
    CompatibleHaar χ A K g d dg → Nonempty (ActualComparison χ hG A K hK g d dg P Q)

/-- Continuation presentations for the same actual comparison give the
same map even when chosen independently. -/
def PresentationIndependence : Prop :=
  ∀ (g : K) (dg : LeviNormalization (conjugateAnchor χ g) (conjugateRepresentation χ g A))
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation (conjugateAnchor χ g) K)
    (T S : ActualComparison χ hG A K hK g d dg P Q), T.val = S.val

/-- The actual identity comparison after the canonical original-fiber
identification. -/
def IdentityLaw : Prop :=
  ∀ (d₁ : LeviNormalization (conjugateAnchor χ (1 : Gpts)) (conjugateRepresentation χ 1 A))
    (P : ParabolicPresentation χ K)
    (T : ActualComparison χ hG A K hK 1 d d₁ P (identityTarget χ P))
    (z : Xu) (v : fiber χ A K P z),
    TransportedValue (identityEquiv χ hG A hK P z) (T.val z v) v

section Composition

variable (s t : K)

set_option hygiene false in
local notation "χt" => conjugateAnchor χ (t : Gpts)
set_option hygiene false in
local notation "χts" => conjugateAnchor χt (s : Gpts)
set_option hygiene false in
local notation "χst" => conjugateAnchor χ ((s * t : K) : Gpts)
set_option hygiene false in
local notation "At" => conjugateRepresentation χ (t : Gpts) A
set_option hygiene false in
local notation "Ats" => conjugateRepresentation χt (s : Gpts) At
set_option hygiene false in
local notation "Ast" => conjugateRepresentation χ ((s * t : K) : Gpts) A

variable (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χt K)
  (R : ParabolicPresentation χst K)

/-- The pointwise composite of the two displayed maps is the product map
after the constructed comparison of the target fibers. -/
def Composes (Tt : ComparisonFamily χ A K t P Q)
    (Ts : ComparisonFamily χt At K s Q (multiplicationTarget χ s t R))
    (Tst : ComparisonFamily χ A K (s * t) P R) : Prop :=
  ∀ (z : Xu) (v : fiber χ A K P z),
    TransportedComposite (multiplicationEquiv χ s t hG A hK R z)
      (Ts (ActualConjugateLeviV3.unitaryConjugateParameter χ t z))
      (Tt z v) (Tst z v)

end Composition

/-- V.3.2 for rational points of the common compact, in the actual order s*t. -/
def CompositionLaw : Prop :=
  ∀ (s t : K)
    (dt : LeviNormalization (conjugateAnchor χ t) (conjugateRepresentation χ t A))
    (dts : LeviNormalization (conjugateAnchor (conjugateAnchor χ t) s)
      (conjugateRepresentation (conjugateAnchor χ t) s (conjugateRepresentation χ t A)))
    (dst : LeviNormalization (conjugateAnchor χ ((s * t : K) : Gpts))
      (conjugateRepresentation χ ((s * t : K) : Gpts) A))
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation (conjugateAnchor χ t) K)
    (R : ParabolicPresentation (conjugateAnchor χ ((s * t : K) : Gpts)) K)
    (Tt : ActualComparison χ hG A K hK t d dt P Q)
    (Ts : ActualComparison (conjugateAnchor χ t) hG (conjugateRepresentation χ t A)
      K hK s dt dts Q (multiplicationTarget χ s t R))
    (Tst : ActualComparison χ hG A K hK (s * t) d dst P R),
    Composes χ hG A K hK s t P Q R Tt.val Ts.val Tst.val

section Inverse

variable (g : K)

set_option hygiene false in
local notation "χg" => conjugateAnchor χ (g : Gpts)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ (g : Gpts) A
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ (g : Gpts)

variable (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χg K)

/-- Both inverse identities with the actual canonical return map. -/
def AreInverses (T : ComparisonFamily χ A K g P Q)
    (S : ComparisonFamily χg Ag K g⁻¹ Q (inverseTarget χ g P)) : Prop :=
  ∀ z : Xu, TransportedInverse (inverseEquiv χ g hG A hK P z) (S (zg z)) (T z)

end Inverse

/-- The certified comparison for the inverse point gives the inverse map. -/
def InverseLaw : Prop :=
  ∀ (g : K)
    (dg : LeviNormalization (conjugateAnchor χ g) (conjugateRepresentation χ g A))
    (db : LeviNormalization (conjugateAnchor (conjugateAnchor χ g) ((g⁻¹ : K) : Gpts))
      (conjugateRepresentation (conjugateAnchor χ g) ((g⁻¹ : K) : Gpts)
        (conjugateRepresentation χ g A)))
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation (conjugateAnchor χ g) K)
    (T : ActualComparison χ hG A K hK g d dg P Q)
    (S : ActualComparison (conjugateAnchor χ g) hG (conjugateRepresentation χ g A)
      K hK g⁻¹ dg db Q (inverseTarget χ g P)),
    AreInverses χ hG A K hK g P Q T.val S.val

/-- Closed actual translated V.3.2 target with identity, inverse, and
independence for arbitrary choices of the particular standard continuations. -/
def ClosedV32Statement : Prop :=
  HasSourceNormalization χ A d K →
  ExistenceLaw χ hG A K hK d ∧ PresentationIndependence χ hG A K hK d ∧
    IdentityLaw χ hG A K hK d ∧ CompositionLaw χ hG A K hK d ∧ InverseLaw χ hG A K hK d

end Coherence

end Langlands.Plancherel.ActualConjugateLeviCoherence
