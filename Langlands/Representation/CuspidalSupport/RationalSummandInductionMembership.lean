import Langlands.Representation.Induction.OpenNormalRestrictionSemisimple
import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.CompactCoefficient.AmbientProjector

/-!
# The compact induction of a summand of the norm-kernel restriction lies in the block

Let `π` be an irreducible smooth representation of `G(F)` and `ρ` an irreducible smooth
representation of the common norm kernel `⁰G` with an injective `⁰G`-intertwiner
`ρ → π|_{⁰G}`. Then every irreducible subquotient of `Π = c-Ind_{⁰G}^{G(F)} ρ` is an
unramified twist of `π`, i.e. `Π` lies in the inertia block of `π` (at the
function-carrier universe). This is the first step of the proof of Renard VI.4.1.

The proof needs no cuspidality and no compactness: the restriction of `Π` to the open
normal subgroup `⁰G` is semisimple, so a nonzero subquotient admits a nonzero
`⁰G`-intertwiner to `π|_{⁰G}`, and Renard VI.3.2(iii)
(`rationalNormKernelTwistEquivalence`) turns that into an unramified twist.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandInductionMembershipTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalSummandInductionMembershipTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- Every irreducible subquotient of the compact induction `c-Ind_{⁰G}^{G(F)} ρ` of an
irreducible smooth summand `ρ ↪ π|_{⁰G}` of an irreducible `π` is an unramified twist of
`π`: the compact induction lies in the inertia block of the lifted base
`rationalInertiaBaseLift G π`. -/
theorem rationalSummandInduction_mem_block (hG : GroupScheme.IsConnectedReductive G)
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (hπ : π.IsIrreducible)
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) (hρ : ρ.IsIrreducible)
    (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j)) :
    rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      ((Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj
        (SmoothRep.toRep.obj ρ)) := by
  intro D hD hDP
  obtain ⟨B, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDP
  let _ : Representation.IsIrreducible D.representation := hD
  let _ : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      D.representation.asModule
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  let e := Induction.restrictAlongEquiv (rationalCommonNormKernel G).subtype
    (SmoothRep.universeLiftEquiv.{uF} π)
  let j' : Representation.IntertwiningMap ρ.representation
      ((rationalInertiaBaseLift G π).representation.comp
        (rationalCommonNormKernel G).subtype) :=
    e.toIntertwiningMap.comp (SmoothRep.hom j)
  have hj' : Function.Injective j' := e.injective.comp hj
  obtain ⟨φ, hφ⟩ := Induction.exists_restricted_intertwiningMap_ne_zero_of_subquotient
    (rationalCommonNormKernel G) ρ.representation (isOpen_rationalCommonNormKernel G)
    ρ.isSmooth hρ (rationalInertiaBaseLift G π).representation j' hj' B.representation
    D.representation (SmoothRep.hom i) hi (SmoothRep.hom q) hq d hd
  have hπlift : (rationalInertiaBaseLift G π).IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff.{uF} π).mpr hπ
  have h3 := rationalNormKernelTwistEquivalence F G hG D (rationalInertiaBaseLift G π) hD hπlift
  obtain ⟨χ, ⟨iso⟩⟩ := h3.1.mp (h3.2.mpr ⟨φ, hφ⟩)
  exact IsRationalInertiaRelated.symm
    ⟨χ, ⟨(SmoothRep.mkIso (A := rationalUnramifiedTwist G χ D)
      (B := rationalInertiaBaseLift G π) iso).symm⟩⟩

end Langlands.CuspidalSupport
