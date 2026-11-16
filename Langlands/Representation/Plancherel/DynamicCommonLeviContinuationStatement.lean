import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation

/-! # Remaining actual common-Levi rational-start existence target -/

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

attribute [local instance] radicalMeasurable radicalBorel intersectionMeasurable
  intersectionBorel quotientMeasurable quotientBorel

/-- Exact remaining analytic existence assertion for fixed actual common-Levi data. -/
def CommonLeviContinuationExists
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) : Prop :=
  ∃ (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
        (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
    (Ω : Set (unramifiedCharacters (normCharacters χ))),
    IsOpen Ω ∧ Ω.Nonempty ∧
    ∃ (hΩ : Ω ⊆ pairFullDomainRegion χ K hK ψ hψ ψ' A),
      IsRationalOperatorOn Ω
        (restrictedCompactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ) ∧
      Nonempty (PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K hδ A Ω hΩ)

/-- The common-Levi existence consequence of IV.1.1. Every analytic assertion,
including the squared-modulus identity, is in the conclusion. -/
def ConditionalDynamicCommonLeviContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)),
    A.IsAdmissible → A.HasFiniteLength →
      CommonLeviContinuationExists χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A

end Langlands.Plancherel.DynamicCommonLeviContinuation
