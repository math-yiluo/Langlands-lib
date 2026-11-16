import Langlands.Representation.Plancherel.DynamicCommonLeviCompact
import Langlands.Representation.Plancherel.ContinuedIntertwiningNaturality

/-! # Actual restricted continuation for dynamic common-Levi standard families -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviContinuation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact UnramifiedOperatorFamily

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance radicalMeasurable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (radical ψ) := borel _
local instance radicalBorel (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (radical ψ) := ⟨rfl⟩
local instance intersectionMeasurable (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace ((radical ψ).subgroupOf (radical ψ')) := borel _
local instance intersectionBorel (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace ((radical ψ).subgroupOf (radical ψ')) := ⟨rfl⟩
local instance quotientMeasurable (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (QuotientSpace (U := radical ψ) (radical ψ')) := borel _
local instance quotientBorel (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (QuotientSpace (U := radical ψ) (radical ψ')) := ⟨rfl⟩

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (Ω : Set (unramifiedCharacters (normCharacters χ)))
  (hΩ : Ω ⊆ pairFullDomainRegion χ K hK ψ hψ ψ' A)

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "hν" => DynamicOppositeCanonicalScalar.normCharacters_continuous χ
local notation "L" => parameterScheme χ
local notation "hp" => DynamicOppositeCanonicalScalar.parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG

/-- The actual compact integral family restricted to the displayed convergence region. -/
def restrictedCompactFamily (z : Ω) :
    CompactInductionPicture h₀ K A →ₗ[ℂ] CompactInductionPicture h₁ K A :=
  compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A ⟨z.val, hΩ z.property⟩

/-- One denominator for the whole restricted actual compact operator. -/
abbrev PairContinuation :=
  RationalOperatorContinuationData Ω
    (restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ)

set_option quotPrecheck false in
local notation "J" => (fun z : Ω =>
  pairFamily χ K hK ψ hψ ψ' hψ' hδ A ⟨z.val, hΩ z.property⟩)
local notation "C" => restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ
local notation "PC" => PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ

/-- Construct continuation data from rationality on Ω and one nonempty open subset. -/
def pairContinuation {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hJ : IsRationalOperatorOn Ω C) : PC :=
  compactInductionContinuationData L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ) hν A J hD hne hDΩ hJ

variable (p : PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ) {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)

/-- The continued actual ambient standard intertwiner on the chosen regular locus. -/
def continuedFamily (z : p.regularRegion) :
    (UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ) (parameterTransport χ z.val)
      A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁ (leviNormCharacters χ) (parameterTransport χ z.val)
      A).representation :=
  continuedInductionIntertwiner L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ) hν A J p hD hne hDΩ z

local notation "Jext" => continuedFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ p hD hne hDΩ

/-- Compact conjugacy, stated using the actual restriction/extension maps. -/
theorem continuedFamily_compact (z : p.regularRegion) :
    (compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).toLinearMap.comp
      ((Jext z).toLinearMap.comp
        (compactEquiv χ hG K hK ψ hψ hψK z.val A).symm.toLinearMap) =
      p.continuedOperator z :=
  continuedInductionIntertwiner_compact L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ) hν A J p hD hne hDΩ z

/-- On Ω the ambient continuation is precisely the original pair integral. -/
theorem continuedFamily_agrees (z : Ω) :
    Jext ⟨z.val, p.subset_regularRegion z.property⟩ =
      pairFamily χ K hK ψ hψ ψ' hψ' hδ A ⟨z.val, hΩ z.property⟩ :=
  continuedInductionIntertwiner_agrees L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ) hν A J p hD hne hDΩ z

/-- Recovery retains the original carrier, quotient measure and all ambient arguments. -/
theorem continuedFamily_spec (z : Ω)
    (f : UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ z.val) A) :
    HasIntegral h₀ hU₀ (radical ψ')
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (pairQuotientMeasure K hK ψ ψ') f
      (eval _ _ (Jext ⟨z.val, p.subset_regularRegion z.property⟩ f)) := by
  have he := continuedFamily_agrees χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ p hD hne hDΩ z
  exact (congrArg (fun T => HasIntegral h₀ hU₀ (radical ψ')
    (A.twist (parameterTransport χ z.val).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
    (pairQuotientMeasure K hK ψ ψ') f (eval _ _ (T f))) he).mpr
    (pairFamily_spec χ K hK ψ hψ ψ' hψ' hδ A ⟨z.val, hΩ z.property⟩ f)

/-- Numerator and denominator choices do not affect common regular values. -/
theorem continuedFamily_unique (q : PC) (z : ↥(p.regularRegion ∩ q.regularRegion)) :
    Jext ⟨z.val, z.property.1⟩ =
      continuedFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ q hD hne hDΩ
        ⟨z.val, z.property.2⟩ :=
  continuedInductionIntertwiner_unique L hp hL h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hψK hψ'K hr₀ hr₁ (parameterHomeomorph χ) hν A J p hD hne hDΩ q z

section Representatives

variable (B : SmoothRep.{0, u, uW} ℂ (levi χ))
  (Λ : Set (unramifiedCharacters (normCharacters χ)))
  (hΛ : Λ ⊆ pairFullDomainRegion χ K hK ψ hψ ψ' B)
  (q : PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ B Λ hΛ)
  (hDΛ : D ⊆ Λ) (e : A.representation.Equiv B.representation)

/-- Independently chosen continued representatives commute on common regular values.
The common nonempty open starting set D is explicitly displayed. -/
theorem continuedFamily_natural (z : ↥(p.regularRegion ∩ q.regularRegion))
    (f : UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ z.val) A) :
    continuedFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ B Λ hΛ q hD hne hDΛ
        ⟨z.val, z.property.2⟩
        (inducedMap h₀ hU₀
          (twistEquiv (parameterTransport χ z.val).val.toMonoidHom e).toIntertwiningMap f) =
      inducedMap h₁ hU₁
        (twistEquiv (parameterTransport χ z.val).val.toMonoidHom e).toIntertwiningMap
        (Jext ⟨z.val, z.property.1⟩ f) := by
  exact continuedInductionIntertwiner_natural L hp hL
    h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK hP₀ hP₁ hψK hψ'K hr₀ hr₁
    (parameterHomeomorph χ) hν A B J
    (fun w : Λ => pairFamily χ K hK ψ hψ ψ' hψ' hδ B ⟨w.val, hΛ w.property⟩)
    p q hD hne hDΩ hDΛ e
    (fun w hw => pairFamily_natural χ K hK ψ hψ ψ' hψ' hδ e
      ⟨w, hΩ (hDΩ hw)⟩) z f

end Representatives

end Langlands.Plancherel.DynamicCommonLeviContinuation
