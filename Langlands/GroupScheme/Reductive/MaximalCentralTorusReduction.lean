import Langlands.GroupScheme.Reductive.MaximalCentralTorus
import Langlands.GroupScheme.Reductive.RelativeCenterStatement
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.Torus.RelativeLargestSubtorusStatement
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Maximal central tori from the relative centre and largest-subtorus theorems -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A conditional reduction retaining both structural prerequisites as explicit premises. -/
def MaximalCentralRelativeTorusReductionStatement : Prop :=
  ReductiveRelativeCenterStatement.{u} →
    RelativeMultiplicativeTypeLargestSubtorusStatement.{u} →
      ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
        (∃ (Z : GroupScheme S) (z : Z ⟶ G), IsMaximalCentralRelativeTorus z) ∧
        ∀ (Z : GroupScheme S) (z : Z ⟶ G), IsMaximalCentralRelativeTorus z →
          ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
            IsMaximalCentralRelativeTorus ((GroupScheme.baseChange b).map z)

/-- A largest subtorus of the full centre gives existence, and range uniqueness
transfers its base-change property to every maximal central relative torus. -/
theorem maximalCentralRelativeTorusReduction :
    MaximalCentralRelativeTorusReductionStatement.{u} := by
  intro hCenter hLargest S G hG
  obtain ⟨C, c, hc, hC, hcb⟩ := hCenter S G hG
  obtain ⟨⟨T, t, ht, hT, hmax⟩, hbase⟩ := hLargest S C hC
  have htc : IsMaximalCentralRelativeTorus (t ≫ c) :=
    isMaximalCentralRelativeTorus_comp_center c hc t ht hT hmax
  refine ⟨⟨T, t ≫ c, htc⟩, ?_⟩
  intro Z z hz S' b
  have htbase := hbase T t ⟨ht, hT, hmax⟩ S' b
  have htcb : IsMaximalCentralRelativeTorus ((GroupScheme.baseChange b).map (t ≫ c)) := by
    rw [Functor.map_comp]
    exact isMaximalCentralRelativeTorus_comp_center
      ((GroupScheme.baseChange b).map c) (hcb S' b)
      ((GroupScheme.baseChange b).map t) htbase.1 htbase.2.1 htbase.2.2
  have heq :
      SubgroupFunctor.range ((GroupScheme.baseChange b).map z) =
        SubgroupFunctor.range ((GroupScheme.baseChange b).map (t ≫ c)) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
      hz.range_eq htc]
  refine ⟨hz.1.baseChange b, hz.2.1.baseChange b,
    hz.2.2.1.baseChange b, ?_⟩
  intro Z' z' hz' hcentral htorus
  rw [heq]
  exact htcb.2.2.2 Z' z' hz' hcentral htorus

end Langlands.GroupScheme
