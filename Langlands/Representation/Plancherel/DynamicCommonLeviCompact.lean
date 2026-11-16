import Langlands.Representation.Plancherel.DynamicCommonLeviComposition
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.StandardInductionRepresentativeContinuation

/-! # Actual compact standard families for two dynamic parabolics with a common Levi -/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviCompact

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition

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

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Continuity of the dynamic projection with values in the literal base Levi. -/
theorem commonProjection_continuous
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ) :
    Continuous (commonDecomposition χ ψ hψ).projection := by
  have hc := DynamicOppositeCanonicalScalar.projection_continuous ψ
  have transport (M : Subgroup (RationalPoint F G.X))
      (hM : levi ψ = M)
      (h : IsSemidirectDecomposition (parabolic ψ) M (radical ψ)) :
      Continuous h.projection := by
    subst M
    exact hc
  exact transport _ (by simp only [levi, hψ]) _

variable (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic ψ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

/-- Actual restriction/extension between the varying normalized induction and its fixed
compact picture, using all rational characters of the base centralizer scheme. -/
def compactEquiv (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z) A ≃ₗ[ℂ]
        CompactInductionPicture (commonDecomposition χ ψ hψ) K A :=
  unramifiedLeviInductionCompactEquiv (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) K
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) hK hψK (leviNormCharacters χ)
    (fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
      (parameterHomeomorph χ).symm.continuous)
    (commonProjection_continuous χ ψ hψ) (parameterTransport χ z) A

@[simp]
theorem compactEquiv_eval (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z) A) (k : K) :
    eval _ _ (compactEquiv χ hG K hK ψ hψ hψK z A f) k = eval _ _ f (k : RationalPoint F G.X) :=
  rfl

variable (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic ψ', ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- Compact conjugation of precisely the published actual common-Levi pair integral. -/
def compactFamily (z : pairFullDomainRegion χ K hK ψ hψ ψ' A) :
    CompactInductionPicture (commonDecomposition χ ψ hψ) K A →ₗ[ℂ]
      CompactInductionPicture (commonDecomposition χ ψ' hψ') K A :=
  compactIntertwiningOperator (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) K
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) hK hψK (leviNormCharacters χ)
    (fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
      (parameterHomeomorph χ).symm.continuous)
    (commonProjection_continuous χ ψ hψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG)
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ') hψ'K
    (commonProjection_continuous χ ψ' hψ') (parameterTransport χ z.val) A
    (pairFamily χ K hK ψ hψ ψ' hψ' hδ A z)

@[simp]
theorem compactFamily_eval (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (f : CompactInductionPicture (commonDecomposition χ ψ hψ) K A) (k : K) :
    eval _ _ (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z f) k =
      eval _ _ (pairFamily χ K hK ψ hψ ψ' hψ' hδ A z
        ((compactEquiv χ hG K hK ψ hψ hψK z.val A).symm f))
          (k : RationalPoint F G.X) := rfl

/-- Extending the compact output recovers the original weak integral on every ambient
argument, with values represented in the original inducing carrier. -/
theorem compactFamily_spec (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (f : CompactInductionPicture (commonDecomposition χ ψ hψ) K A) :
    HasIntegral (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (radical ψ')
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (pairQuotientMeasure K hK ψ ψ')
      ((compactEquiv χ hG K hK ψ hψ hψK z.val A).symm f)
      (eval _ _ ((compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).symm
        (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z f))) := by
  have he : (compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).symm
      (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z f) =
      pairFamily χ K hK ψ hψ ψ' hψ' hδ A z
        ((compactEquiv χ hG K hK ψ hψ hψK z.val A).symm f) :=
    (compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).symm_apply_apply _
  rw [he]
  exact pairFamily_spec χ K hK ψ hψ ψ' hψ' hδ A z _

section Representatives

variable {A} {B : SmoothRep.{0, u, uW} ℂ (levi χ)}

/-- Equivalent inducing representatives have the same entire actual convergence domain. -/
theorem pairFullDomainRegion_equiv (e : A.representation.Equiv B.representation) :
    pairFullDomainRegion χ K hK ψ hψ ψ' A = pairFullDomainRegion χ K hK ψ hψ ψ' B :=
  standardIntertwiningFullDomainRegion_equiv (commonDecomposition χ ψ hψ)
    (radical_isClosed ψ) (radical ψ') (parameterHomeomorph χ) (normCharacters χ)
    (pairQuotientMeasure K hK ψ ψ') e

/-- The original integral commutes with the actual twisted inducing equivalence. -/
theorem pairFamily_natural (e : A.representation.Equiv B.representation)
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    pairFamily χ K hK ψ hψ ψ' hψ' hδ B
        ⟨z.val, pairFullDomainRegion_equiv χ K hK ψ hψ ψ' e ▸ z.property⟩
        (inducedMap (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
          (twistEquiv (parameterTransport χ z.val).val.toMonoidHom e).toIntertwiningMap f) =
      inducedMap (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
        (twistEquiv (parameterTransport χ z.val).val.toMonoidHom e).toIntertwiningMap
        (pairFamily χ K hK ψ hψ ψ' hψ' hδ A z f) :=
  standardInductionIntertwinerFamily_representative_natural
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (radical ψ')
    (parameterHomeomorph χ) (normCharacters χ) (pairQuotientMeasure K hK ψ ψ')
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    (radicalHaar ψ' K hK) (pairIntersectionHaar K hK ψ ψ')
    (pairQuotientMeasure_isCompatible K hK ψ ψ') (levi_isClosed χ) hδ e z f

/-- The compact representative square uses the fixed pointwise equivalences. -/
theorem compactFamily_natural (e : A.representation.Equiv B.representation)
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (f : CompactInductionPicture (commonDecomposition χ ψ hψ) K A) :
    compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ B
        ⟨z.val, pairFullDomainRegion_equiv χ K hK ψ hψ ψ' e ▸ z.property⟩
        (compactInductionPictureEquiv (commonDecomposition χ ψ hψ) K e f) =
      compactInductionPictureEquiv (commonDecomposition χ ψ' hψ') K e
        (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A z f) := by
  apply compactIntertwiningOperator_natural
  exact pairFamily_natural χ K hK ψ hψ ψ' hψ' hδ e z

end Representatives

/-- Specialization to the published opposite compact family with its conditional
squared-modulus witness. Proof irrelevance identifies the two literal decompositions. -/
theorem compactFamily_inverse_eq_conditionalForwardCompactFamily
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (z : forwardFullDomainRegion χ K hK A) :
    compactFamily χ hG K hK χ rfl hPK (Dynamic.inverseCocharacter χ)
        (Dynamic.centralizer_inverseCocharacter χ) hOppK
        (conditionalSquaredModulus χ hRefl hCST hG) A z =
      DynamicOppositeCanonicalScalar.conditionalForwardCompactFamily
        χ hRefl hCST hG K hK hPK hOppK A z := rfl

end Langlands.Plancherel.DynamicCommonLeviCompact
