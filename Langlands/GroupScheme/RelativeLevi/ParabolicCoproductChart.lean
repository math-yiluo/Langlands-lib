import Langlands.GroupScheme.RelativeLevi.ParabolicSheaf
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

/-! # Actual parabolic families on scheme coproducts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.AlgebraicSpace
open CoproductChart

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)

include hG in
/-- There is at most one actual parabolic family over an empty parameter scheme. -/
theorem parabolicSubsingleton_of_isEmpty (T : Over S) [IsEmpty T.left] :
    Subsingleton (ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) := by
  let 𝒰 : Scheme.OpenCover.{u} T.left :=
    Scheme.Cover.mkOfCovers PEmpty.{u + 1} (fun _ => T.left)
      (fun _ => 𝟙 T.left) (fun x => isEmptyElim x)
  refine ⟨fun F H => eq_of_restrict_cover 𝒰 hG F H ?_⟩
  intro i
  change PEmpty.{u + 1} at i
  exact isEmptyElim i

variable {I : Type u} (V : I → Over S)
    (F : ∀ i, ParabolicSubgroup ((GroupScheme.baseChange (V i).hom).obj G))

/-- Arbitrary actual parabolic families match on the disjoint scheme components. -/
theorem coproductParabolic_compatible :
    Presieve.Arrows.Compatible (parabolicPresheaf G hG) (sigmaOverι V) F := by
  intro a b T f g hfg
  by_cases hab : a = b
  · subst b
    let : Mono (sigmaOverι V a) := Over.mono_of_mono_left _
    have h : f = g := by
      apply (cancel_mono (sigmaOverι V a)).mp
      exact hfg
    subst g
    rfl
  · let : IsEmpty T.left := _root_.AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
      (g := fun i => (V i).left)
      (show CommSq f.left g.left
        (Sigma.ι (fun i => (V i).left) a) (Sigma.ι (fun i => (V i).left) b) from
          ⟨congrArg (fun k => k.left) hfg⟩) hab
    let : Subsingleton (ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) :=
      parabolicSubsingleton_of_isEmpty hG T
    change restrict hG f (F a) = restrict hG g (F b)
    exact Subsingleton.elim _ _

/-- The component inclusions form a covering sieve on the big Zariski slice. -/
theorem sigmaOver_covering :
    Sieve.ofArrows V (sigmaOverι V) ∈ Scheme.zariskiTopology.over S (sigmaOver V) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (sigmaOpenCover (fun i => (V i).left)).mem_grothendieckTopology

/-- Actual parabolic families on the components glue uniquely to their scheme coproduct. -/
theorem existsUnique_coproductParabolic :
    ∃! H : ParabolicSubgroup ((GroupScheme.baseChange (sigmaOver V).hom).obj G),
      ∀ i, restrict hG (sigmaOverι V i) H = F i := by
  have hs : Presieve.IsSheafFor (parabolicPresheaf G hG)
      (Presieve.ofArrows V (sigmaOverι V)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact parabolic_isSheaf G hG _ (sigmaOver_covering V)
  exact (Presieve.isSheafFor_arrows_iff _ _).mp hs F (coproductParabolic_compatible hG V F)

/-- The actual parabolic on a scheme coproduct with the prescribed component families. -/
def coproductParabolic :
    ParabolicSubgroup ((GroupScheme.baseChange (sigmaOver V).hom).obj G) :=
  (existsUnique_coproductParabolic hG V F).choose

@[simp]
theorem restrict_coproductParabolic (i : I) :
    restrict hG (sigmaOverι V i) (coproductParabolic hG V F) = F i :=
  (existsUnique_coproductParabolic hG V F).choose_spec.1 i

/-- The actual natural chart induced by component parabolic families. -/
def coproductParabolicChart :
    (schemeYoneda S).obj (sigmaOver V) ⟶ parabolicPresheaf G hG :=
  uliftYonedaEquiv.symm (coproductParabolic hG V F)

/-- Evaluation after a component inclusion is restriction of its prescribed family. -/
theorem coproductParabolicChart_app_comp {T : Over S} (i : I) (a : T ⟶ V i) :
    (coproductParabolicChart hG V F).app (op T) ⟨a ≫ sigmaOverι V i⟩ =
      restrict hG a (F i) := by
  change restrict hG (a ≫ sigmaOverι V i) (coproductParabolic hG V F) = _
  rw [← restrict_comp, restrict_coproductParabolic]

end Langlands.GroupScheme.ParabolicSubgroupModuli
