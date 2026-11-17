import Langlands.GroupScheme.IsomorphismSheaf
import Langlands.GroupScheme.RelativeInnerForm
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-! # Isomorphisms on the coproduct of an étale cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.LocalGroupIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Full natural families agree on a test with initial underlying scheme. -/
theorem eq_of_isInitial {T : Over S} (hT : IsInitial T.left)
    (e f : LocalGroupIso G H T) : e = f := by
  apply ext_toFun
  intro W t g
  apply Over.OverMorphism.ext
  exact (IsInitial.ofStrict t.left hT).hom_ext _ _

/-- Arbitrary full natural families on disjoint scheme components glue. -/
theorem exists_sigmaFamily {ι : Type u} (V : ι → Over S)
    (e : ∀ i, LocalGroupIso G H (V i)) :
    ∃ f : LocalGroupIso G H (CoproductChart.sigmaOver V),
      ∀ i, f.refine (CoproductChart.sigmaOverι V i) = e i := by
  let F := presheaf G H
  let π := CoproductChart.sigmaOverι V
  have (i : ι) : Mono (π i) := by
    dsimp only [π, CoproductChart.sigmaOverι]
    infer_instance
  have hcov : Sieve.ofArrows V π ∈ fppfTopology S (CoproductChart.sigmaOver V) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      _ (sigmaOpenCover (fun i => (V i).left)).mem_grothendieckTopology
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp
    (isSheaf (G := G) (H := H) (fppfTopology S))
  have hcompat : Presieve.Arrows.Compatible F π e := by
    intro i j T r s hrs
    by_cases hij : i = j
    · subst j
      have h : r = s := (cancel_mono (π i)).mp hrs
      rw [h]
    · have hT : IsInitial T.left :=
        IsInitial.ofCoproductDisjointOfCommSq hij
          (coproductIsCoproduct (fun i => (V i).left)) r.left s.left
            (congrArg (fun r => r.left) hrs)
      exact eq_of_isInitial hT _ _
  obtain ⟨f, hf, -⟩ :=
    (Presieve.isSheafFor_arrows_iff F π).mp (hF.isSheafFor _ hcov) e hcompat
  exact ⟨f, hf⟩

/-- A full natural Isom family on the scheme coproduct of relative tests. -/
def sigmaFamily {ι : Type u} (V : ι → Over S)
    (e : ∀ i, LocalGroupIso G H (V i)) :
    LocalGroupIso G H (CoproductChart.sigmaOver V) :=
  Classical.choose (exists_sigmaFamily V e)

@[simp] theorem sigmaFamily_refine {ι : Type u} (V : ι → Over S)
    (e : ∀ i, LocalGroupIso G H (V i)) (i : ι) :
    (sigmaFamily V e).refine (CoproductChart.sigmaOverι V i) = e i :=
  Classical.choose_spec (exists_sigmaFamily V e) i

/-- Isomorphisms over each member of a cover give an actual isomorphism over its coproduct. -/
def isoOnSigma
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (e : ∀ i, (baseChange (𝒰.f i)).obj G ≅ (baseChange (𝒰.f i)).obj H) :
    (baseChange (Sigma.desc 𝒰.f)).obj G ≅ (baseChange (Sigma.desc 𝒰.f)).obj H :=
  (sigmaFamily (fun i => Over.mk (𝒰.f i))
    (fun i => LocalGroupIso.ofBaseChangeIso (e i))).toBaseChangeIso

end Langlands.GroupScheme.LocalGroupIso
