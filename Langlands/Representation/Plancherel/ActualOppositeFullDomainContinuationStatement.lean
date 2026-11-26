import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Whole-domain continuation targets for the actual opposite integrals -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open DynamicOppositeCanonicalScalar DynamicOppositeStandardIntertwining

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

set_option maxRecDepth 4096 in
/-- An irreducible square-integrable inducing representation has continuations
clearing the actual opposite compact families on their entire convergence
domains. Both domains contain a nonempty open subset. -/
def ActualOppositeFullDomainContinuationStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X, ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (_hi : A.IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure] [mu.IsInvInvariant]
    (_hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu),
    (Nonempty (ForwardContinuation χ relativeRootReflectionExistence centralSplitTorusCharacter
        hG K hK hPK hOppK A) ∧
      ∃ D : Set (unramifiedCharacters (normCharacters χ)),
        IsOpen D ∧ D.Nonempty ∧ D ⊆ forwardFullDomainRegion χ K hK A) ∧
    (Nonempty (ReverseContinuation χ relativeRootReflectionExistence centralSplitTorusCharacter
        hG K hK hPK hOppK A) ∧
      ∃ D : Set (unramifiedCharacters (normCharacters χ)),
        IsOpen D ∧ D.Nonempty ∧ D ⊆ reverseFullDomainRegion χ K hK A)

end Langlands.Plancherel
