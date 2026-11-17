import Langlands.Representation.Plancherel.ActualConjugateLeviTensor

/-! # Original actual standard integrals under rational conjugation -/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviConjugation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualConjugateLeviTwist

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
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

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Literal common-centralizer equalities persist under actual rational conjugation. -/
theorem conjugateCentralizer
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ) (g : RationalPoint F G.X) :
    Dynamic.centralizer (ψ ≫ (G.innerIso g).hom) =
      Dynamic.centralizer (χ ≫ (G.innerIso g).hom) := by
  have hp : Dynamic.centralizer (ψ ≫ (G.innerIso g).hom) =
      (Dynamic.centralizer ψ).comap (G.innerIso g).inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      Dynamic.centralizer_eq_comap_of_iso (ψ ≫ (G.innerIso g).hom) (G.innerIso g).symm
  have hc : Dynamic.centralizer (χ ≫ (G.innerIso g).hom) =
      (Dynamic.centralizer χ).comap (G.innerIso g).inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      Dynamic.centralizer_eq_comap_of_iso (χ ≫ (G.innerIso g).hom) (G.innerIso g).symm
  exact hp.trans ((congrArg (fun H => H.comap (G.innerIso g).inv) hψ).trans hc.symm)

/-- Actual vector left translation for any parabolic with the displayed
common Levi, followed by the canonical full conjugate-twist identification. -/
def commonLeftTranslation
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (g : RationalPoint F G.X) (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unramifiedCharacters (normCharacters χ)) :
    ((DynamicNormalization.leviTwistedInductionFunctor
      (commonDecomposition χ ψ hψ) (radical_isClosed ψ)).obj
        (twistObject χ z A)).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor
        (commonDecomposition (χ ≫ (G.innerIso g).hom) (ψ ≫ (G.innerIso g).hom)
          (conjugateCentralizer χ ψ hψ g))
        (radical_isClosed (ψ ≫ (G.innerIso g).hom))).obj
        (twistObject (χ ≫ (G.innerIso g).hom) (conjugateParameter χ g z)
          (conjugateRepresentation χ g A))).representation :=
  (CoefficientConjugation.leviLeftTranslation (commonDecomposition χ ψ hψ)
    (commonDecomposition (χ ≫ (G.innerIso g).hom) (ψ ≫ (G.innerIso g).hom)
      (conjugateCentralizer χ ψ hψ g)) g
    (DynamicCoefficientConjugation.parabolic_mem_conjugation ψ g)
    (DynamicCoefficientConjugation.levi_mem_conjugation χ g)
    (DynamicCoefficientConjugation.radical_mem_conjugation ψ g)
    (radical_isClosed ψ) (radical_isClosed (ψ ≫ (G.innerIso g).hom))
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG)
    (DynamicOppositeCanonicalScalar.radical_unimodular (ψ ≫ (G.innerIso g).hom) hG)
    (twistObject χ z A)).trans
    (CoefficientConjugation.leviInductionCongr
      (commonDecomposition (χ ≫ (G.innerIso g).hom) (ψ ≫ (G.innerIso g).hom)
        (conjugateCentralizer χ ψ hψ g))
      (radical_isClosed (ψ ≫ (G.innerIso g).hom))
      (DynamicOppositeCanonicalScalar.radical_unimodular (ψ ≫ (G.innerIso g).hom) hG)
      (conjugateTwistEquiv χ g z A))

/-- The actual squared-modulus proposition for the two conjugate parabolics. -/
def ConjugateModulus
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ) (g : RationalPoint F G.X) : Prop :=
  SquaredModulusCompatibility
    (commonDecomposition (χ ≫ (G.innerIso g).hom) (ψ ≫ (G.innerIso g).hom)
      (conjugateCentralizer χ ψ hψ g)) (radical_isClosed (ψ ≫ (G.innerIso g).hom))
    (commonDecomposition (χ ≫ (G.innerIso g).hom) (ψ' ≫ (G.innerIso g).hom)
      (conjugateCentralizer χ ψ' hψ' g)) (radical_isClosed (ψ' ≫ (G.innerIso g).hom))

/-- Pull back the actual conjugate original integral domain through full
parameter conjugation; no new convergence criterion is introduced. -/
def conjugateFullDomainRegion
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (g : RationalPoint F G.X) (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    Set (unramifiedCharacters (normCharacters χ)) :=
  conjugateParameter χ g ⁻¹'
    pairFullDomainRegion (χ ≫ (G.innerIso g).hom)
      (RationalDynamicSource.conjugateCompact g K)
      (RationalDynamicSource.conjugateCompact_isCompact g K hK)
      (ψ ≫ (G.innerIso g).hom) (conjugateCentralizer χ ψ hψ g)
      (ψ' ≫ (G.innerIso g).hom) (conjugateRepresentation χ g A)

/-- The particular actual conjugate pairFamily, parametrized on the
pullback of its full original domain. -/
def conjugatePairFamily
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (g : RationalPoint F G.X) (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hδg : ConjugateModulus χ ψ hψ ψ' hψ' g)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : conjugateFullDomainRegion χ ψ hψ ψ' g K hK A) :=
  pairFamily (χ ≫ (G.innerIso g).hom)
    (RationalDynamicSource.conjugateCompact g K)
    (RationalDynamicSource.conjugateCompact_isCompact g K hK)
    (ψ ≫ (G.innerIso g).hom) (conjugateCentralizer χ ψ hψ g)
    (ψ' ≫ (G.innerIso g).hom) (conjugateCentralizer χ ψ' hψ' g)
    hδg (conjugateRepresentation χ g A)
    (Set.restrictPreimage
      (pairFullDomainRegion (χ ≫ (G.innerIso g).hom)
        (RationalDynamicSource.conjugateCompact g K)
        (RationalDynamicSource.conjugateCompact_isCompact g K hK)
        (ψ ≫ (G.innerIso g).hom) (conjugateCentralizer χ ψ hψ g)
        (ψ' ≫ (G.innerIso g).hom) (conjugateRepresentation χ g A))
      (conjugateParameter χ g) z)

/-- Exact open prerequisite for conjugating the actual original standard
integrals, with their actual conjugate source measures and full domains. -/
def OriginalConjugationStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (g : RationalPoint F G.X)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')),
    ∃ hδg : ConjugateModulus χ ψ hψ ψ' hψ' g,
      pairFullDomainRegion χ K hK ψ hψ ψ' A =
        conjugateFullDomainRegion χ ψ hψ ψ' g K hK A ∧
      (∀ (z : unramifiedCharacters (normCharacters χ))
        (hz : z ∈ pairFullDomainRegion χ K hK ψ hψ ψ' A)
        (hzg : z ∈ conjugateFullDomainRegion χ ψ hψ ψ' g K hK A)
        (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
          (leviNormCharacters χ) (parameterTransport χ z) A),
        conjugatePairFamily χ ψ hψ ψ' hψ' g K hK hδg A ⟨z, hzg⟩
          (commonLeftTranslation χ ψ hψ g hG A z f) =
          commonLeftTranslation χ ψ' hψ' g hG A z
            (pairFamily χ K hK ψ hψ ψ' hψ' hδ A ⟨z, hz⟩ f))

end Langlands.Plancherel.ActualCommonLeviConjugation
