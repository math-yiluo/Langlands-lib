import Langlands.GroupScheme.Dynamic.RealizedLeviNesting
import Langlands.GroupScheme.Rational.SemistandardProperLeviRank
import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardNestedFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants

/-! # Extension of a semistandard parabolic from a literal Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift

open RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}

/-- Extend an inner semistandard index for the inherited split torus to
an ambient semistandard index. Both the parabolic and radical products hold
on every test scheme. -/
def atInheritedTorus (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (p : SemistandardSpectralIndex i) (m : LeviModel p)
    (q : SemistandardSpectralIndex (semistandardLeviSplitTorus p m.represents)) :
    {r : SemistandardSpectralIndex i // RationalSemistandardParabolicLift p m q r ∧
      r.radical.IsPointwiseProduct (q.radical.map m.inclusion) p.radical} := by
  letI := hG.isSeparated
  let outer := CocharacterPresentation.ofCoverage hG semistandardSpectralDynamicCoverage hi p
  let inner := CocharacterPresentation.ofCoverage m.reductive semistandardSpectralDynamicCoverage
    (isMaximalSplitTorus_semistandardLeviSplitTorus p m.represents m.closed hi) q
  have hmodel : (Dynamic.centralizer outer.hom).IsRepresentedBy m.inclusion := by
    rw [outer.levi_eq]
    exact m.represents
  let lift := Dynamic.nestedRealization G hG outer.hom m.scheme m.inclusion m.closed hmodel
    inner.hom
  let ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G := lift.val
  have hP : Dynamic.parabolic ψ =
      Dynamic.extendFromCentralizer outer.hom m.inclusion hmodel q.parabolic :=
    lift.property.1.1.trans (congrArg _ inner.parabolic_eq)
  have hL : Dynamic.centralizer ψ = q.levi.map m.inclusion :=
    lift.property.1.2.1.trans (congrArg _ inner.levi_eq)
  have hU : Dynamic.unipotent ψ =
      Dynamic.extendFromCentralizer outer.hom m.inclusion hmodel q.radical :=
    lift.property.1.2.2.trans (congrArg _ inner.radical_eq)
  have htorus : SubgroupFunctor.range i ≤ Dynamic.centralizer ψ := by
    rw [hL]
    intro X x hx
    obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine ⟨s ≫ (semistandardLeviSplitTorus p m.represents).hom.hom,
      q.torus_le_levi X ⟨s, rfl⟩, ?_⟩
    change (s ≫ (semistandardLeviSplitTorus p m.represents).hom.hom) ≫
      m.inclusion.hom.hom = s ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, semistandardLeviSplitTorus_comp]
  let r : SemistandardSpectralIndex i :=
    ⟨Dynamic.parabolic ψ, Dynamic.centralizer ψ, Dynamic.unipotent ψ,
      htorus, Dynamic.isParabolicWithLeviAndRadical_of_structural parabolicDynamic
        dynamicCentralizerReductive dynamicGeometricUnipotentRadical hG ψ⟩
  refine ⟨r, ⟨?_, hL.symm, ?_⟩, ?_⟩
  · change (Dynamic.parabolic ψ).IsPointwiseProduct _ _
    rw [hP, ← outer.radical_eq]
    exact Dynamic.extendFromCentralizer_isPointwiseProduct _ _ _ _
  · change q.radical = (Dynamic.unipotent ψ).comap m.inclusion
    rw [hU, Dynamic.comap_extendFromCentralizer]
  · change (Dynamic.unipotent ψ).IsPointwiseProduct _ _
    rw [hU, ← outer.radical_eq]
    exact Dynamic.extendFromCentralizer_isPointwiseProduct _ _ _ _

section Points

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

variable [TopologicalSpace F] [IsAffineHom G.X.hom]

local instance extensionLeviAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom :=
  m.reductive.isAffineHom

variable
  {p r : SemistandardSpectralIndex i} {m : LeviModel p}
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {q : SemistandardSpectralIndex iM} (h : RationalSemistandardParabolicLift p m q r)

/-- The inner Levi is identified with the restriction of the final ambient
Levi to the literal outer Levi. -/
def innerLeviPointsEquiv : levi q ≃ₜ* (levi r).subgroupOf (levi p) := by
  apply subgroupContinuousMulEquiv m.pointHomeomorph
  intro x
  change x ∈ q.levi.carrier (Over.mk (𝟙 _)) ↔
    (m.pointHomeomorph x : rationalPoints G) ∈ r.levi.carrier (Over.mk (𝟙 _))
  rw [← h.levi_image]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    let : Mono m.inclusion.hom.hom := m.represents.1
    change y ≫ m.inclusion.hom.hom = x ≫ m.inclusion.hom.hom at he
    rwa [← (cancel_mono m.inclusion.hom.hom).mp he]

@[simp]
theorem innerLeviPointsEquiv_coe (x : levi q) :
    ((h.innerLeviPointsEquiv x : levi p) : rationalPoints G) =
      rationalPoints.map m.inclusion (x : rationalPoints m.scheme) :=
  rfl

/-- The inner radical is identified with the intersection of the final
ambient radical and the literal outer Levi. -/
def innerRadicalPointsEquiv : radical q ≃ₜ* (radical r).subgroupOf (levi p) := by
  apply subgroupContinuousMulEquiv m.pointHomeomorph
  intro x
  change x ∈ q.radical.carrier (Over.mk (𝟙 _)) ↔
    (m.pointHomeomorph x : rationalPoints G) ∈ r.radical.carrier (Over.mk (𝟙 _))
  rw [h.radical_comap]
  rfl

@[simp]
theorem innerRadicalPointsEquiv_coe (x : radical q) :
    ((h.innerRadicalPointsEquiv x : levi p) : rationalPoints G) =
      rationalPoints.map m.inclusion (x : rationalPoints m.scheme) :=
  rfl

end Points

end Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift
