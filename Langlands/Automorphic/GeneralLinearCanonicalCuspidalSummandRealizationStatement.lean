import Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement
import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Cuspidal summands on the canonical general linear quotient

The summand-to-realization direction of Getz–Hahn, Theorem 9.7.3, on the canonical quotient.
The class map also intertwines the actions of the finite local matrix groups. -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.DiscreteHeckeIsolation

open Langlands.Global Langlands.GroupScheme RestrictionSplitCentre

local instance (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- An irreducible summand in canonical cuspidal `L²([GL_{r+1}])` has a cuspidal operator
realization whose faithful class map has dense image in the summand and intertwines the local
matrix actions at every finite place. -/
def GeneralLinearCanonicalCuspidalSummandRealizationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ),
    let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
    let hG := isConnectedReductive_generalLinear F (Fin (r + 1))
    let H := Lp ℂ 2 (canonicalMeasure F G)
    ∀ P : Submodule ℂ H,
      Langlands.Analysis.IsIrreducibleSubrepresentation
        (canonicalL2RightAction F G centralSplitTorusCharacter hG) P →
      P ≤ canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter parabolicDynamic hG →
      ∃ (S : CuspidalOperatorRealization F r) (j : S.Space →ₗ[ℂ] H),
        Function.Injective j ∧
        (∀ f, IsCanonicalGeneralLinearFormClass F r (j f) (S.realization.toContinuous f)) ∧
        (LinearMap.range j).topologicalClosure = P ∧
        ∀ (p : Global.FinitePlace F) (g : FiniteLocalGL F (r + 1) p) (f : S.Space),
          j (S.realization.localRepresentation p g f) = canonicalL2LocalAction F r p g (j f)

end Langlands.Automorphic.DiscreteHeckeIsolation
