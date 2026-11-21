import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # Rational automorphy at the full standard index -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The inducing subgroup at the full standard index is exactly the
ambient principal rational subgroup. -/
theorem parabolicQuotientSubgroup_top :
    parabolicQuotientSubgroup F (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) =
      rationalSubgroup F G := by
  let J := fam.top
  let p := fam.p J
  let r := fam.iU J
  let l := fam.l J
  have hp := (fam.isCompatible J).parabolic.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hp
  have hPt : SubgroupFunctor.range p = ⊤ := by
    rw [(fam.isCompatible J).parabolic_eq]
    exact (standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic).2.2.1
  let : IsIso p := isIso_of_full_range p (Over.mono_of_mono_left _) hPt
  let : IsIso l := (fam.isCompatible J).levi.isIso_of_isIso_parabolic (p := p) fam.connectedReductive
  have hPred : IsConnectedReductive (fam.P J) := fam.connectedReductive.of_iso (asIso p)
  have hU := (fam.isUnipotentRadical J).1
  have hrad : SubgroupFunctor.range r = ⊥ :=
    hPred.hasTrivialUnipotentRadical (fam.U J) r hU.isClosedSubgroup hU.smooth
      hU.connectedSpace hU.isUnipotent hU.isNormal
  have hUnip : parabolicUnipotentImage F p r = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot]
    have hx : x ≫ r.hom.hom ∈ (SubgroupFunctor.range r).carrier _ :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    rw [hrad] at hx
    change x ≫ r.hom.hom = 1 at hx
    change x ≫ (r ≫ p).hom.hom = 1
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
  have hRat : parabolicLeviRationalImage F p l = rationalSubgroup F G := by
    change rationalImage F (l ≫ p) = rationalSubgroup F G
    apply le_antisymm (rationalImage_le_rationalSubgroup _) ?_
    rintro _ ⟨x, rfl⟩
    let j := l ≫ p
    refine ⟨G.affinePointsTarget (inv j) (CommAlgCat.of F F) x, ?_⟩
    change map F (fam.M J) G j (rational F (fam.M J)
      (G.affinePointsTarget (inv j) (CommAlgCat.of F F) x)) = rational F G x
    rw [map_rational_affinePointsTarget, IsIso.inv_hom_id]
    change rational F G x ≫ 𝟙 G.X = rational F G x
    exact Category.comp_id _
  change parabolicUnipotentImage F p r ⊔ parabolicLeviRationalImage F p l = _
  rw [hUnip, hRat, bot_sup_eq]

/-- The parabolic automorphy predicate at the full standard index matches
the ambient rational automorphy predicate, including the center condition. -/
theorem isAutomorphicOn_top_iff {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ) :
    fam.IsAutomorphicOn hsmooth Kinf rho fam.top f ↔
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho f := by
  unfold IsAutomorphicOn
  rw [fam.parabolicQuotientSubgroup_top]

/-- The full standard quotient yields the original automorphic functions
on the rational adelic quotient. -/
def StandardTopAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ),
    fam.IsAutomorphicOn hsmooth Kinf rho fam.top f ↔
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho f

theorem standardTopAutomorphy : StandardTopAutomorphyStatement.{u} := by
  intro F _ _ G _ _ _ fam N d rho hsmooth hcalc Kinf f
  exact fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf f

end Langlands.Global.StandardParabolicFamily
