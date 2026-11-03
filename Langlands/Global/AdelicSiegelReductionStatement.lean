import Langlands.Global.AdelicStandardSiegelFactors
import Langlands.Global.AdelicIwasawaStatement
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Actual algebraic setup and adelic Siegel coverage -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The actual canonical standard subgroups and split tori in the setup of
Getz–Hahn §2.7. This predicate supplies no existence theorem. -/
def IsSiegelAlgebraicSetup : Prop :=
  letI : IsAffineHom (Standard.parabolicScheme i ν ∅).X.hom :=
    (Standard.isClosedSubgroup_parabolicHom i ν ∅).isAffineHom
  IsMaximalSplitTorus i ∧
    IsGenericCocharacter i ν ∧
    IsMinimalParabolicSubgroup (Standard.parabolicHom i ν ∅) ∧
    IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) ∧
    LeviSubgroup.IsGeometricUnipotentRadical (Standard.unipotentToParabolic i ν ∅) ∧
    standardLevi i ν ∅ = torusCentralizer i ∧
    relativeRoots (torusToStandardParabolic F G T i ν) = positiveRelativeRoots i ν ∧
    (∃ (D : GroupScheme (Spec (CommRingCat.of F))) (d : D ⟶ G)
      (t₀ : T₀.toGrp ⟶ D),
      IsDerivedSubgroup d ∧ IsMaximalSplitTorus t₀ ∧
        t₀ ≫ d = CommGroupScheme.groupHom j ≫ i) ∧
    ∃ (Z₀ : CommGroupScheme (Spec (CommRingCat.of F))) (z : Z₀ ⟶ T),
      IsSplitComponent (CommGroupScheme.groupHom z ≫ i) ∧
        Surjective
          (subgroupProductMap (CommGroupScheme.groupHom j)
            (CommGroupScheme.groupHom z)).left

variable (C : CompactFactors F G
  (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

/-- The actual ordered weak Siegel product has maximal compact Iwasawa data,
and its rational left saturation is exactly the actual norm-one group. -/
def IsSiegelCover (t : ℝ≥0ˣ) : Prop :=
  IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
      C.compactSubgroup ∧
    (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
        weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t =
      (normOneSubgroup F G : Set (AdelicGroupPoints F G))

/-- The number-field connected-reductive Siegel reduction target, including
existence of the actual algebraic setup. No torus, compact subgroup, chamber
coverage, or structural comparison is supplied as a hypothesis. -/
def AdelicSiegelReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
          ∃ (C : CompactFactors F G
              (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
            (t : ℝ≥0ˣ),
            IsSiegelCover F G T i ν T₀ j C t

end Langlands.Global.AdelicSiegelFactors
