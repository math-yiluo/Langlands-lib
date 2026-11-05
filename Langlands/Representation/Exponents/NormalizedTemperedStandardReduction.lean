import Langlands.Representation.Exponents.NormalizedTemperedStandardReductionStatement
import Langlands.Representation.Exponents.ArbitraryParabolicTemperedConjugation
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation

/-! # Conditional assembly of normalized-exponent standard reduction

The actual structural inputs are retained. This internal adapter does not
prove that arbitrary prescribed parabolic and Levi maps admit the required
simultaneous dynamic realization.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section FixedFamily

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance reductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Admissibility and the full normalized-exponent cone condition for all
actual maps representing one fixed standard family. -/
def SatisfiesStandardNormalizedExponentTests
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
    haveI := hG.smooth
    IsAdmissible π.representation ∧
        ∀ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
          IsStandardCocharacter i ν J ζ →
          ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (ha : IsSplitComponent a),
            SubgroupFunctor.range p = standardParabolic i ν J →
            SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
            SubgroupFunctor.range p =
              Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) →
            SubgroupFunctor.range (l ≫ p) =
              Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) →
            SatisfiesNormalizedExponentConeCondition p l a hp hl ha π

/-- For a fixed actual standard family, simultaneous dynamic realization of
all prescribed parabolic and Levi maps, maximal split torus conjugacy and the
actual relative root system imply the standard-testing equivalence. -/
theorem normalizedTempered_iff_standard_of_dynamicRealizations
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T}
    (hroot : letI := hi.isSplitSubtorus.mono; HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hreal : ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
        ∃ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
          SubgroupFunctor.range p = Dynamic.parabolic z ∧
          SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer z)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    IsNormalizedExponentTempered hG π ↔
      SatisfiesStandardNormalizedExponentTests hG T i ν π := by
  have := hG.smooth
  constructor
  · intro h
    exact IsNormalizedExponentTempered.standardRestriction hG π h T i ν
  · rintro ⟨hadm, hstd⟩
    refine ⟨hadm, ?_⟩
    intro P M A p l a hp hl ha
    obtain ⟨z, hP, hM⟩ := hreal P M p l hp hl
    obtain ⟨g, J, ζ, hζ, hPstd, hMstd, hPdyn, hMdyn⟩ :=
      exists_simultaneousStandardConjugate_of_dynamicRealization
        hconj hG hi hroot hν p l z hP hM
    have hcondition := hstd J ζ hζ P M A (p ≫ (G.innerIso g).hom) l a
      (hp.comp_iso (G.innerIso g)) hl ha hPstd hMstd hPdyn hMdyn
    exact (satisfiesNormalizedExponentConeCondition_comp_innerIso_iff
      p l a hp hl ha g π).mp hcondition

end FixedFamily

/-- The exact Library reduction statement follows from the three retained
structural inputs. No claim that these inputs are discharged is made here. -/
theorem normalizedTemperedStandardReduction_of_structural_inputs
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hroot : RelativeRootSystemStatement.{u})
    (hreal : ∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (_hG : IsConnectedReductive G)
      (P M : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
        ∃ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
          SubgroupFunctor.range p = Dynamic.parabolic z ∧
          SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer z) :
    NormalizedTemperedStandardReductionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i ν hi hν _ π
  exact normalizedTempered_iff_standard_of_dynamicRealizations
    hconj hG hi (hroot k G hG T i hi) hν (hreal k G hG) π

end Langlands.Aubert.General.RepresentedParabolic
