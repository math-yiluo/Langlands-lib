import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement

/-! # Closed common-Levi coherence of the actual normalized comparisons -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCoherence

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualCommonLeviV3 UnramifiedOperatorFamily

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
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)

local instance ambientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance ambientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance leviMeasurable : MeasurableSpace (levi χ) := borel _
local instance leviBorel : BorelSpace (levi χ) := ⟨rfl⟩
local instance leviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace
/-- A structural common-Levi parabolic with the displayed actual compact
factorization. This bundle does not define another semistandard index. -/
structure ParabolicPresentation
    (K : OpenSubgroup (RationalPoint F G.X)) where
  cocharacter : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
  centralizer_eq : Dynamic.centralizer cocharacter = Dynamic.centralizer χ
  iwasawa : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic cocharacter, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X)

variable
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "Par" => ParabolicPresentation χ K

/-- The actual coefficient fiber, indexed only by the displayed structural
parabolic and the full unitary parameter. -/
abbrev fiber (P : Par) (z : Xu) :=
  coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z)

/-- Actual product-action intertwiners for every ordered pair of parabolics. -/
abbrev ComparisonSystem :=
  ∀ P Q : Par,
    UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq

/-- A comparison is tied to the actual standard tensor by an existential
rational presentation, dense genuine generic locus, and its unique regular
germ. All continuation and scalar data are witnesses, not structural inputs. -/
def IsActualNormalizedComparison (P Q : Par)
    (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq) : Prop :=
  ∃ (p : ContinuedPair χ hG K hK
        P.cocharacter P.centralizer_eq P.iwasawa
        Q.cocharacter Q.centralizer_eq Q.iwasawa A)
    (q : ContinuedPair χ hG K hK
        Q.cocharacter Q.centralizer_eq Q.iwasawa
        P.cocharacter P.centralizer_eq P.iwasawa A.contragredient),
    Nonempty (ScalarInverseData χ hG K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa A p q) ∧
    HasDenseGenericLocus χ hG A K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa p q ∧
    IsRationalOperatorOn
      (genericLocus χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa
        Q.cocharacter Q.centralizer_eq Q.iwasawa A p q)
      (compactComparison χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa
        Q.cocharacter Q.centralizer_eq Q.iwasawa A p q) ∧
    IsRegularUnitaryExtension χ hG A K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa p q T ∧
    AgreesOnUnitaryGeneric χ hG A K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa p q T ∧
    IsUniqueByRationalGerm χ hG A K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa p q T ∧
    PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa T

/-- With the actual split-center identification, the existential packaging
is exactly the already stated closed pairwise V.3.1 target. -/
theorem closedV31_iff_exists (hcenter : IsActualSplitCenter χ C) (P Q : Par) :
    ClosedV31Statement χ hG A C hC qMeasure hsq hi K hK
        P.cocharacter P.centralizer_eq P.iwasawa
        Q.cocharacter Q.centralizer_eq Q.iwasawa ↔
      ∃ T, IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q T := by
  constructor
  · intro h
    obtain ⟨p, q, hd, hD, hr, T, hT, ha, hu, hp⟩ := h hcenter
    exact ⟨T, p, q, hd, hD, hr, hT, ha, hu, hp⟩
  · rintro ⟨T, p, q, hd, hD, hr, hT, ha, hu, hp⟩ _
    exact ⟨p, q, hd, hD, hr, T, hT, ha, hu, hp⟩

/-- The identity is on the actual coefficient fiber at every unitary point. -/
def IdentityLaw (T : ComparisonSystem χ A K) : Prop :=
  ∀ (P : Par) (z : Xu) (v : fiber χ A K P z), T P P z v = v

/-- The common-Levi `s = t = 1` specialization of V.3.2. -/
def CompositionLaw (T : ComparisonSystem χ A K) : Prop :=
  ∀ (P Q R : Par) (z : Xu) (v : fiber χ A K P z),
    T Q R z (T P Q z v) = T P R z v

/-- Both inverse identities display their different actual source fibers. -/
def InverseLaw (T : ComparisonSystem χ A K) : Prop :=
  (∀ (P Q : Par) (z : Xu) (v : fiber χ A K P z),
    T Q P z (T P Q z v) = v) ∧
  (∀ (P Q : Par) (z : Xu) (w : fiber χ A K Q z),
    T P Q z (T Q P z w) = w)

/-- The inverse laws are elementary consequences of identity and composition;
this implication does not prove those substantive standard-operator laws. -/
theorem inverseLaw_of_identity_composition
    (T : ComparisonSystem χ A K)
    (hid : IdentityLaw χ A K T) (hcomp : CompositionLaw χ A K T) :
    InverseLaw χ A K T := by
  constructor
  · intro P Q z v
    exact (hcomp P Q P z v).trans (hid P z v)
  · intro P Q z w
    exact (hcomp Q P Q z w).trans (hid Q z w)

/-- The displayed two-sided inverse acts on the actual fibers. -/
theorem bijective_of_inverseLaw (T : ComparisonSystem χ A K)
    (hinv : InverseLaw χ A K T) (P Q : Par) (z : Xu) :
    Function.Bijective (T P Q z) :=
  ⟨fun x y h => (hinv.1 P Q z x).symm.trans
      ((congrArg (T Q P z) h).trans (hinv.1 P Q z y)),
    fun w => ⟨T Q P z w, hinv.2 P Q z w⟩⟩

/-- Independence includes different continued presentations, starting regions,
whole-operator denominators, and scalar inverse witnesses. The comparison
must satisfy the full actual-germ specification above. -/
def PresentationIndependenceStatement : Prop :=
  ∀ (P Q : Par)
    (T S : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq),
    IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q T →
    IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q S →
    T = S

/-- Closed common-Levi coherence target. Existence, all pairwise V.3.1
properties, identity, composition, inverse and continued-presentation
independence are conclusions from the displayed structural data alone. -/
def ClosedCommonLeviCoherenceStatement : Prop :=
  IsActualSplitCenter χ C →
    (∃ T : ComparisonSystem χ A K,
      (∀ P Q : Par,
        IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK
          P Q (T P Q)) ∧
      IdentityLaw χ A K T ∧ CompositionLaw χ A K T ∧ InverseLaw χ A K T) ∧
    PresentationIndependenceStatement χ hG A C hC qMeasure hsq hi K hK

end Langlands.Plancherel.ActualCommonLeviCoherence
