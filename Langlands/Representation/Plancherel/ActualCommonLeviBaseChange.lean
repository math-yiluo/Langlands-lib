import Langlands.Representation.Plancherel.DynamicCommonLeviCompact
import Langlands.Representation.Plancherel.ContinuedIntertwiningBaseChange

/-! # Actual original common-Levi integrals under translated base change -/

noncomputable section

set_option maxRecDepth 4096

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviBaseChange

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact

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
  DynamicCommonLeviCompact.radicalMeasurable
  DynamicCommonLeviCompact.radicalBorel
  DynamicCommonLeviCompact.intersectionMeasurable
  DynamicCommonLeviCompact.intersectionBorel
  DynamicCommonLeviCompact.quotientMeasurable
  DynamicCommonLeviCompact.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  {A : SmoothRep.{0, u, uV} ℂ (levi χ)} {B : SmoothRep.{0, u, uW} ℂ (levi χ)}

/-- The actual inducing equivalence at left-translated full parameters. -/
def inducingEquiv (τ z : unramifiedCharacters (normCharacters χ))
    (a : (A.twist (parameterTransport χ τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ τ))).representation.Equiv
        B.representation) :
    (A.twist (parameterTransport χ (τ * z)).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
        (parameterTransport χ (τ * z)))).representation.Equiv
      (B.twist (parameterTransport χ z).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z))).representation :=
  transportedBaseTwistEquiv (parameterHomeomorph χ) (normCharacters χ) τ z a

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)

/-- The entire actual original-integral domain translates exactly under a
change of the orbit base object, with the same source quotient measure. -/
theorem fullDomain_iff (τ z : unramifiedCharacters (normCharacters χ))
    (a : (A.twist (parameterTransport χ τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ τ))).representation.Equiv
        B.representation) :
    τ * z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A ↔
      z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' B :=
  standardIntertwiningFullDomainRegion_translation_iff
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (radical ψ')
    (parameterHomeomorph χ) (normCharacters χ) (pairQuotientMeasure K hK ψ ψ') τ z a

variable
  (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))

/-- The original actual standard integrals obey the translated base-object
square. Full-domain membership on the other side is proved, not assumed. -/
theorem originalSquare (τ z : unramifiedCharacters (normCharacters χ))
    (a : (A.twist (parameterTransport χ τ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ τ))).representation.Equiv
        B.representation)
    (hz : z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' B)
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ (τ * z)) A) :
    pairFamily χ K hK ψ hψ ψ' hψ' hδ B ⟨z, hz⟩
      (inducedMap (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
        (inducingEquiv χ τ z a).toIntertwiningMap f) =
      inducedMap (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
        (inducingEquiv χ τ z a).toIntertwiningMap
        (pairFamily χ K hK ψ hψ ψ' hψ' hδ A
          ⟨τ * z, (fullDomain_iff χ K hK ψ hψ ψ' τ z a).mpr hz⟩ f) :=
  standardInductionIntertwinerFamily_natural
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (radical ψ')
    (parameterHomeomorph χ) (normCharacters χ) (pairQuotientMeasure K hK ψ ψ')
    (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    (radicalHaar ψ' K hK) (pairIntersectionHaar K hK ψ ψ')
    (pairQuotientMeasure_isCompatible K hK ψ ψ') (levi_isClosed χ) hδ τ z a hz f

end Langlands.Plancherel.ActualCommonLeviBaseChange
