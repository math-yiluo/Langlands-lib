import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersectionUniversal
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Finite limits of actual positive-radius rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem hom_unique {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

/-- Two actual bounded restrictions over the base construct an actual restriction
to the all-products intersection, using the bounded quotient pushout. -/
def interLift {c d e : RationalChart K A} (f : c ⟶ d) (g : c ⟶ e) :
    c ⟶ d.inter e where
  restriction := RationalPresentation.RationalIntersection.pushoutLift
    (f.comp_baseMap.trans g.comp_baseMap.symm)
  comp_baseMap :=
    (RationalPresentation.RationalIntersection.pushoutLift_comp_base
      (f.comp_baseMap.trans g.comp_baseMap.symm)).trans f.comp_baseMap

@[simp]
theorem interLift_interLeft {c d e : RationalChart K A} (f : c ⟶ d) (g : c ⟶ e) :
    interLift f g ≫ interLeft d e = f :=
  hom_unique _ _

@[simp]
theorem interLift_interRight {c d e : RationalChart K A} (f : c ⟶ d) (g : c ⟶ e) :
    interLift f g ≫ interRight d e = g :=
  hom_unique _ _

/-- The chosen intersection and its actual bounded projections form a binary fan. -/
def interBinaryFan (d e : RationalChart K A) : BinaryFan d e :=
  BinaryFan.mk (interLeft d e) (interRight d e)

/-- The quotient pushout constructs every required chart lift; proved uniqueness
of bounded restrictions gives the product universal property. -/
def interBinaryFanIsLimit (d e : RationalChart K A) : IsLimit (interBinaryFan d e) :=
  BinaryFan.IsLimit.mk _ (fun f g => interLift f g)
    (fun f g => interLift_interLeft f g) (fun f g => interLift_interRight f g)
    (fun _ _ _ _ _ => hom_unique _ _)

/-- The same actual intersection is a cone over any two restrictions with a
common target. Its square commutes by proved restriction uniqueness. -/
def interPullbackCone {d e b : RationalChart K A} (f : d ⟶ b) (g : e ⟶ b) :
    PullbackCone f g :=
  PullbackCone.mk (interLeft d e) (interRight d e) (hom_unique _ _)

/-- The constructed bounded lift proves the chart-category pullback property. -/
def interPullbackConeIsLimit {d e b : RationalChart K A} (f : d ⟶ b) (g : e ⟶ b) :
    IsLimit (interPullbackCone f g) :=
  PullbackCone.IsLimit.mk _ (fun S => interLift S.fst S.snd)
    (fun S => interLift_interLeft S.fst S.snd)
    (fun S => interLift_interRight S.fst S.snd)
    (fun _ _ _ _ => hom_unique _ _)

instance hasLimit_pair (d e : RationalChart K A) : HasLimit (pair d e) :=
  ⟨⟨interBinaryFan d e, interBinaryFanIsLimit d e⟩⟩

instance hasBinaryProducts : HasBinaryProducts (RationalChart K A) :=
  hasBinaryProducts_of_hasLimit_pair (RationalChart K A)

instance hasLimit_cospan {d e b : RationalChart K A} (f : d ⟶ b) (g : e ⟶ b) :
    HasLimit (cospan f g) :=
  ⟨⟨interPullbackCone f g, interPullbackConeIsLimit f g⟩⟩

instance hasPullbacks : HasPullbacks (RationalChart K A) :=
  hasPullbacks_of_hasLimit_cospan (RationalChart K A)

instance hasTerminal : HasTerminal (RationalChart K A) :=
  (wholeIsTerminal K A).hasTerminal

/-- The actual terminal chart and constructed intersection pullbacks give all
finite limits by Mathlib's general finite-limit construction. -/
instance hasFiniteLimits : HasFiniteLimits (RationalChart K A) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
