import Langlands.GroupScheme.RelativeUnipotent.Basic
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalRigidity
import Langlands.GroupScheme.Lie.SmoothFibreRanks
import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Descent.Data

/-! # Finite termination of relative vector-bundle filtrations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S : Scheme.{u}}

/-- A smooth group with trivial geometric fibres is trivial on every test scheme. -/
theorem range_id_eq_bot_of_geometricFibres (H : GroupScheme S) [Smooth H.X.hom]
    (hH : ∀ s : S, SubgroupFunctor.range (𝟙 (geometricFiber H s)) = ⊥) :
    SubgroupFunctor.range (𝟙 H) = ⊥ := by
  have hunit (s : S) : IsIso (RelativeLevi.geometricFiberHom (kernelUnit H) s) := by
    have hrep : (⊥ : SubgroupFunctor (geometricFiber H s)).IsRepresentedBy
        (RelativeLevi.geometricFiberHom (kernelUnit H) s) := by
      simpa only [SubgroupFunctor.bot_baseChange] using
        (bot_isRepresentedBy_kernelUnit H).baseChange (geometricPoint S s)
    have hid : (⊥ : SubgroupFunctor (geometricFiber H s)).IsRepresentedBy
        (𝟙 (geometricFiber H s)) := ⟨inferInstance, hH s⟩
    let e := hrep.isoOfIsRepresentedBy hid
    have he : e.hom = RelativeLevi.geometricFiberHom (kernelUnit H) s := by
      simpa using hrep.isoOfIsRepresentedBy_hom_comp hid
    rw [← he]
    infer_instance
  let : Flat (Grp.trivial (Over S)).X.hom := by
    change Flat (𝟙 S)
    infer_instance
  let : LocallyOfFinitePresentation (Grp.trivial (Over S)).X.hom := by
    change LocallyOfFinitePresentation (𝟙 S)
    infer_instance
  let : IsIso (kernelUnit H) := RelativeLevi.isIso_of_geometricFibres _ hunit
  have hr : SubgroupFunctor.range (kernelUnit H) = SubgroupFunctor.range (𝟙 H) := by
    simpa only [CategoryTheory.asIso_hom, Category.comp_id] using
      SubgroupFunctor.range_iso_comp (asIso (kernelUnit H)) (𝟙 H)
  exact hr.symm.trans (range_kernelUnit H)

/-- A finite segment of a descending filtration gives the recursive series
predicate once its last term is trivial on every test scheme. -/
theorem hasVectorBundleSeries_of_segment
    (H : ℕ → GroupScheme S) (j : ∀ k, H (k + 1) ⟶ H k)
    (hstep : ∀ k, ∃ (V : GroupScheme S) (q : H k ⟶ V),
      IsClosedSubgroup (j k) ∧ Smooth (H (k + 1)).X.hom ∧
        (SubgroupFunctor.range (j k)).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (j k)) q ∧
        IsVectorBundleAdditive V)
    (n k : ℕ) (hterminal : SubgroupFunctor.range (𝟙 (H (k + n))) = ⊥) :
    HasVectorBundleSeries n (H k) := by
  induction n generalizing k with
  | zero =>
    change SubgroupFunctor.range (𝟙 (H k)) = ⊥
    exact hterminal
  | succ n ih =>
    obtain ⟨V, q, hc, hs, hn, hq, hv⟩ := hstep k
    refine ⟨H (k + 1), V, j k, q, hc, hs, hn, hq, hv, ?_⟩
    apply ih (k + 1)
    have heq : k + 1 + n = k + (n + 1) := by omega
    rw [heq]
    exact hterminal

/-- Fibrewise termination at a single index suffices to truncate a smooth
filtration to a finite vector-bundle normal series. -/
theorem hasFiniteVectorBundleSeries_of_geometric_termination
    (H : ℕ → GroupScheme S) (j : ∀ k, H (k + 1) ⟶ H k)
    (hstep : ∀ k, ∃ (V : GroupScheme S) (q : H k ⟶ V),
      IsClosedSubgroup (j k) ∧ Smooth (H (k + 1)).X.hom ∧
        (SubgroupFunctor.range (j k)).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (j k)) q ∧
        IsVectorBundleAdditive V)
    (n : ℕ) [Smooth (H n).X.hom]
    (hterminal : ∀ s : S, SubgroupFunctor.range (𝟙 (geometricFiber (H n) s)) = ⊥) :
    HasFiniteVectorBundleSeries (H 0) := by
  refine ⟨n, hasVectorBundleSeries_of_segment H j hstep n 0 ?_⟩
  rw [Nat.zero_add]
  exact range_id_eq_bot_of_geometricFibres (H n) hterminal

/-- The length and proof of the finite series obtained from a geometrically
terminating smooth filtration. -/
def seriesWitnessOfGeometricTermination
    (H : ℕ → GroupScheme S) (j : ∀ k, H (k + 1) ⟶ H k)
    (hstep : ∀ k, ∃ (V : GroupScheme S) (q : H k ⟶ V),
      IsClosedSubgroup (j k) ∧ Smooth (H (k + 1)).X.hom ∧
        (SubgroupFunctor.range (j k)).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (j k)) q ∧
        IsVectorBundleAdditive V)
    (n : ℕ) [Smooth (H n).X.hom]
    (hterminal : ∀ s : S, SubgroupFunctor.range (𝟙 (geometricFiber (H n) s)) = ⊥) :
    {m : ℕ // HasVectorBundleSeries m (H 0)} :=
  ⟨n, hasVectorBundleSeries_of_segment H j hstep n 0 (by
    rw [Nat.zero_add]
    exact range_id_eq_bot_of_geometricFibres (H n) hterminal)⟩

end Langlands.GroupScheme.RelativeUnipotent
