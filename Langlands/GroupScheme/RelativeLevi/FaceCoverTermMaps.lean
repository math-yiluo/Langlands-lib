import Langlands.GroupScheme.RelativeLevi.FaceCoverTermDescent

/-! # Actual successive inclusions of the descended face terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open SubgroupFunctor SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)

/-- Original ambient ranges of consecutive chart terms are nested. -/
theorem localTermFunctor_succ_le (d : ℕ) (a : D.chartCover.I₀) :
    D.localTermFunctor (d + 1) a ≤ D.localTermFunctor d a := by
  change range ((D.charts a.down).2.termInclusion (d + 1)) ≤
    range ((D.charts a.down).2.termInclusion d)
  rw [← (D.charts a.down).2.termStep_comp_inclusion d]
  exact range_comp_le _ _

/-- The actual descended all-test term conditions are nested. -/
theorem termFunctor_succ_le (d : ℕ) : D.termFunctor (d + 1) ≤ D.termFunctor d := by
  intro T x hx a V b
  exact D.localTermFunctor_succ_le d a V (hx a V b)

variable (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual global term on the original base. -/
abbrev globalTerm (d : ℕ) : GroupScheme S :=
  (D.closedTermRepresentative r hG hp hr d).group

/-- Its prescribed closed inclusion into the original ambient group. -/
def globalTermInclusion (d : ℕ) : D.globalTerm r hG hp hr d ⟶ G :=
  (D.closedTermRepresentative r hG hp hr d).hom

/-- The actual successive inclusion is induced by proved all-test containment. -/
def globalTermStep (d : ℕ) :
    D.globalTerm r hG hp hr (d + 1) ⟶ D.globalTerm r hG hp hr d :=
  (D.closedTermRepresentative r hG hp hr d).represents.liftOfLE
    (D.globalTermInclusion r hG hp hr (d + 1)) (by
      change range (D.closedTermRepresentative r hG hp hr (d + 1)).hom ≤ D.termFunctor d
      rw [(D.closedTermRepresentative r hG hp hr (d + 1)).represents.2]
      exact D.termFunctor_succ_le d)

/-- Successive inclusions preserve the original ambient maps exactly. -/
theorem globalTermStep_comp_inclusion (d : ℕ) :
    D.globalTermStep r hG hp hr d ≫ D.globalTermInclusion r hG hp hr d =
      D.globalTermInclusion r hG hp hr (d + 1) :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _

/-- The actual global successive inclusion is a closed subgroup inclusion. -/
theorem isClosedSubgroup_globalTermStep (d : ℕ) :
    IsClosedSubgroup (D.globalTermStep r hG hp hr d) := by
  let : IsClosedImmersion (D.globalTermInclusion r hG hp hr d).hom.hom.left :=
    (D.closedTermRepresentative r hG hp hr d).closed
  have : IsClosedImmersion
      ((D.globalTermStep r hG hp hr d).hom.hom.left ≫
        (D.globalTermInclusion r hG hp hr d).hom.hom.left) := by
    change IsClosedImmersion
      ((D.globalTermStep r hG hp hr d ≫ D.globalTermInclusion r hG hp hr d).hom.hom.left)
    rw [D.globalTermStep_comp_inclusion]
    exact (D.closedTermRepresentative r hG hp hr (d + 1)).closed
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (D.globalTermInclusion r hG hp hr d).hom.hom.left

/-- The original consecutive chart inclusions are recovered under the actual term isomorphisms. -/
theorem globalTermStep_chart (d : ℕ) (a : D.chartCover.I₀) :
    (baseChange (D.chartCover.f a)).map (D.globalTermStep r hG hp hr d) ≫
        (D.globalTermChartIso r hG hp hr d a).hom =
      (D.globalTermChartIso r hG hp hr (d + 1) a).hom ≫
        (D.charts a.down).2.termStep d := by
  have hrep : (D.localTermFunctor d a).IsRepresentedBy
      ((D.charts a.down).2.termInclusion d) := ⟨D.localTermInclusion_mono d a, rfl⟩
  have hs := D.globalTermStep_comp_inclusion r hG hp hr d
  change D.globalTermStep r hG hp hr d ≫
      (D.closedTermRepresentative r hG hp hr d).hom =
    (D.closedTermRepresentative r hG hp hr (d + 1)).hom at hs
  apply hrep.hom_ext
  rw [Category.assoc, D.globalTermChartIso_hom_comp, ← Functor.map_comp,
    hs, Category.assoc,
    (D.charts a.down).2.termStep_comp_inclusion, D.globalTermChartIso_hom_comp]

/-- Every descended term is affine over the original base. -/
theorem isAffineHom_globalTerm (d : ℕ) :
    IsAffineHom (D.globalTerm r hG hp hr d).X.hom := by
  let : IsClosedImmersion (D.globalTermInclusion r hG hp hr d).hom.hom.left :=
    (D.closedTermRepresentative r hG hp hr d).closed
  rw [← Over.w (D.globalTermInclusion r hG hp hr d).hom.hom]
  infer_instance

/-- Over the affine base of the final target, each actual global term is affine. -/
theorem isAffine_globalTerm [IsAffine S] (d : ℕ) :
    IsAffine (D.globalTerm r hG hp hr d).X.left := by
  let : IsAffineHom (D.globalTerm r hG hp hr d).X.hom :=
    D.isAffineHom_globalTerm r hG hp hr d
  exact isAffine_of_isAffineHom (D.globalTerm r hG hp hr d).X.hom

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
