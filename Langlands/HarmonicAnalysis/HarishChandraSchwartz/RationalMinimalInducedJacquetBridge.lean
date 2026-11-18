import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetStatement
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # The represented model of the normalized Jacquet module of `I_{P₀}^G 1` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.HarishChandraSchwartz

section Subgroups

variable {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

private def pullbackTrivialIso (e : H ≃ₜ* G) :
    SmoothRep.pullback e (trivialSmoothCharacter (G := G)).toSmoothRep ≅
      (trivialSmoothCharacter (G := H)).toSmoothRep :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) (fun _ => rfl))

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]

private theorem normalizedInduction_trivial_congr {P M U P' M' U' : Subgroup G}
    (hp : P = P') (hm : M = M') (hu : U = U')
    (h : IsSemidirectDecomposition P M U) (h' : IsSemidirectDecomposition P' M' U')
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) :
    (normalizedInductionFunctor h hU).obj (trivialSmoothCharacter (G := M)).toSmoothRep =
      (normalizedInductionFunctor h' hU').obj (trivialSmoothCharacter (G := M')).toSmoothRep := by
  subst P'
  subst M'
  subst U'
  rfl

private def normalizedJacquet_congr {U M U' M' : Subgroup G}
    (hu : U = U') (hm : M = M') (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMU' : M' ≤ Subgroup.normalizer U')
    (A : SmoothRep.{0, u, u} ℂ G) :
    ((normalizedJacquetFunctor U M hU hMU).obj A).representation.Equiv
      ((Jacquet.normalizedActionOfModulus A.representation U' M' hMU'
        (HaarModulus.closedRestrictCharacter U' hU' M' hMU')).comp
          (MulEquiv.subgroupCongr hm).toMonoidHom) := by
  subst U'
  subst M'
  exact twistEquiv (HaarModulus.closedInverseHalfCharacter U hU M hMU)
    (Jacquet.Localization.trivialEquiv A.representation U M hMU)

end Subgroups

private theorem centralPowers_of_equiv {G H V W : Type u} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W}
    (eM : H ≃* G) (e : σ.Equiv (ρ.comp eM.toMonoidHom)) {d : ℕ}
    (hd : ∀ z : H, (∀ m, z * m = m * z) → (σ z - 1) ^ d = 0) :
    ∀ z : G, (∀ m, z * m = m * z) → (ρ z - 1) ^ d = 0 := by
  intro z hz
  let z' := eM.symm z
  have hz' : ∀ m : H, z' * m = m * z' := by
    intro m
    apply eM.injective
    rw [map_mul, map_mul, eM.apply_symm_apply]
    exact hz (eM m)
  let E := e.toLinearEquiv.conjAlgEquiv ℂ
  have he : E (σ z') = ρ z := by
    apply LinearMap.ext
    intro x
    change e (σ z' (e.symm x)) = ρ z x
    have hequiv := LinearMap.congr_fun (e.isIntertwining' z') (e.symm x)
    change _ = ρ (eM z') (e (e.symm x)) at hequiv
    rwa [e.apply_symm_apply, eM.apply_symm_apply] at hequiv
  simpa only [map_pow, map_sub, map_one, map_zero, he] using congrArg E (hd z' hz')

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalXiCoefficientNonarchimedean

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local notation "P₀" => ParabolicDatum.standard i ν hG hi hν ∅ (Set.empty_subset _)
local notation "Q" => ParabolicDatum.standard i ν hG hi hν J hJ

private theorem pointImage_standard_p :
    pointImage (Q).p = standardParabolicPoints i ν J := by
  rw [pointImage_eq_range_carrier, ParabolicDatum.range_standard_p]

private theorem pointImage_standard_levi :
    pointImage ((Q).l ≫ (Q).p) = standardLeviPoints i ν J := by
  rw [pointImage_eq_range_carrier, ParabolicDatum.range_standard_l_comp_p]

private theorem pointImage_standard_radical :
    pointImage ((Q).r ≫ (Q).p) = standardUnipotentPoints i ν J := by
  rw [pointImage_eq_range_carrier, ParabolicDatum.range_standard_r_comp_p]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom]

/-- The represented Levi points identify with the literal standard subgroup of `G(F)`. -/
def representedStandardLeviPointsEquiv :
    letI := leviPointTopology (Q).l (Q).hl
    rationalPoints (Q).M ≃ₜ* standardLeviPoints i ν J :=
  letI := leviPointTopology (Q).l (Q).hl
  (leviPointsEquiv (Q).p (Q).l (Q).hp (Q).hl).trans
    (subgroupCongrContinuous (pointImage_standard_levi i ν hG hi hν J hJ))

private def representedTrivialInduced (P : ParabolicDatum G) :
    SmoothRep.{0, u, u} ℂ (rationalPoints G) :=
  letI := leviPointTopology P.l P.hl
  (leviInductionFunctor.{u, 0} P.p P.l P.r P.hp P.hr P.hl P.hmul).obj
    (trivialSmoothCharacter (G := rationalPoints P.M)).toSmoothRep

private def representedJacquetFunctor (target : ParabolicDatum G) :
    letI := leviPointTopology target.l target.hl
    SmoothRep.{0, u, u} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, u, u} ℂ (rationalPoints target.M) :=
  leviJacquetFunctor.{u, u} target.p target.l target.r target.hp target.hr target.hl target.hmul

/-- The value of the represented Jacquet–induction composite on the trivial
representation of the inducing Levi. -/
def representedTrivialInducedJacquet (source target : ParabolicDatum G) :
    Rep.{u} ℂ (rationalPoints target.M) :=
  letI := leviPointTopology target.l target.hl
  SmoothRep.toRep.obj ((representedJacquetFunctor target).obj (representedTrivialInduced source))

private def minimalInducedIso :
    letI := leviPointTopology (P₀).l (P₀).hl
    (leviInductionFunctor (P₀).p (P₀).l (P₀).r (P₀).hp (P₀).hr (P₀).hl (P₀).hmul).obj
        (trivialSmoothCharacter (G := rationalPoints (P₀).M)).toSmoothRep ≅
      rationalMinimalInduced i ν (isSemidirectDecomposition_minimalStandard hG hi hν) := by
  letI := leviPointTopology (P₀).l (P₀).hl
  rw [leviInductionFunctor_obj]
  refine (inductionFunctor (P₀).p (P₀).l (P₀).r (P₀).hp (P₀).hr (P₀).hl (P₀).hmul).mapIso
    (pullbackTrivialIso _) ≪≫ eqToIso ?_
  exact normalizedInduction_trivial_congr
    (pointImage_standard_p i ν hG hi hν ∅ (Set.empty_subset _))
    (pointImage_standard_levi i ν hG hi hν ∅ (Set.empty_subset _))
    (pointImage_standard_radical i ν hG hi hν ∅ (Set.empty_subset _)) _ _ _ _

set_option maxHeartbeats 1000000 in
private def minimalInducedJacquetEquiv :
    letI := leviPointTopology (Q).l (Q).hl
    (representedTrivialInducedJacquet P₀ Q).ρ.Equiv
      ((rationalMinimalInducedJacquet i ν (isSemidirectDecomposition_minimalStandard hG hi hν)
        J).comp (representedStandardLeviPointsEquiv i ν hG hi hν J hJ).toMonoidHom) := by
  letI := leviPointTopology (Q).l (Q).hl
  let r := representedJacquetFunctor Q
  let f₀ : representedTrivialInduced P₀ ≅
      rationalMinimalInduced i ν (isSemidirectDecomposition_minimalStandard hG hi hν) :=
    minimalInducedIso i ν hG hi hν
  let e := SmoothRep.equivOfIso (r.mapIso f₀)
  change (r.obj (representedTrivialInduced P₀)).representation.Equiv _
  refine e.trans ?_
  let eQ := leviPointsEquiv (Q).p (Q).l (Q).hp (Q).hl
  let f := normalizedJacquet_congr
    (pointImage_standard_radical i ν hG hi hν J hJ)
    (pointImage_standard_levi i ν hG hi hν J hJ)
    (isClosed_pointImage_comp (Q).p (Q).r (Q).hp.isClosedSubgroup (Q).hr.1.isClosedSubgroup)
    (isClosed_standardUnipotentPoints i ν J)
    (pointImage_le_normalizer (Q).p (Q).l (Q).r (Q).hr)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
    (rationalMinimalInduced i ν (isSemidirectDecomposition_minimalStandard hG hi hν))
  exact SmoothRep.pullbackEquiv eQ f

/-- A common nilpotence exponent for the represented center gives the same
exponent on the literal standard-center action of the normalized Jacquet module. -/
theorem rationalMinimalInducedJacquetUnipotent_of_represented {d : ℕ}
    (hd : ∀ z : rationalPoints (Q).M, (∀ m, z * m = m * z) →
      ((representedTrivialInducedJacquet P₀ Q).ρ z - 1) ^ d = 0) :
    ∀ z : standardLeviPoints i ν J, (∀ m, z * m = m * z) →
      (rationalMinimalInducedJacquet i ν (isSemidirectDecomposition_minimalStandard hG hi hν)
        J z - 1) ^ d = 0 := by
  let := leviPointTopology (Q).l (Q).hl
  exact centralPowers_of_equiv (σ := (representedTrivialInducedJacquet P₀ Q).ρ)
    (representedStandardLeviPointsEquiv i ν hG hi hν J hJ).toMulEquiv
    (minimalInducedJacquetEquiv i ν hG hi hν J hJ) hd

end Langlands.HarishChandraSchwartz
