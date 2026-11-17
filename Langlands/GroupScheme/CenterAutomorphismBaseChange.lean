import Langlands.GroupScheme.CenterAutomorphisms
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Full-centre fixation and faithfully flat base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphismFixesCenter

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- Fixation of the full centre is preserved by arbitrary base change. -/
theorem baseChange {f : G ≅ G} (hf : AutomorphismFixesCenter f) (b : S' ⟶ S) :
    AutomorphismFixesCenter ((GroupScheme.baseChange b).mapIso f) := by
  intro T z hz
  apply (baseChangePointsEquiv b G T).injective
  change baseChangePointsEquiv b G T (z ≫ ((GroupScheme.baseChange b).map f.hom).hom.hom) = _
  rw [baseChangePointsEquiv_comp]
  apply hf
  rwa [center_baseChange, SubgroupFunctor.mem_baseChange] at hz

/-- Fixation of the full centre descends through a faithfully flat quasi-compact
base change. -/
theorem of_baseChange (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    {f : G ≅ G} (hf : AutomorphismFixesCenter ((GroupScheme.baseChange b).mapIso f)) :
    AutomorphismFixesCenter f := by
  intro T z hz
  let T' := (Over.pullback b).obj T
  let a : (Over.map b).obj T' ⟶ T :=
    Over.homMk (pullback.fst T.hom b) (by
      change pullback.fst T.hom b ≫ T.hom = pullback.snd T.hom b ≫ b
      exact pullback.condition)
  have hpe : baseChangePointsEquiv b G T' ((Over.pullback b).map z) = a ≫ z := by
    apply Over.OverMorphism.ext
    dsimp only [T']
    simp only [baseChangePointsEquiv_left, Over.pullback_map_left, pullback.lift_fst,
      Over.comp_left, a, Over.homMk_left]
  have hz' : (Over.pullback b).map z ∈
      (center ((GroupScheme.baseChange b).obj G)).carrier T' := by
    rw [center_baseChange, SubgroupFunctor.mem_baseChange, hpe]
    exact (center G).comp_mem a hz
  apply (Over.pullback b).map_injective
  have he := hf T' ((Over.pullback b).map z) hz'
  change (Over.pullback b).map z ≫ (Over.pullback b).map f.hom.hom.hom =
    (Over.pullback b).map z at he
  simpa only [Functor.map_comp] using he

/-- Full-centre fixation is equivalent before and after fpqc base change. -/
theorem baseChange_iff (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (f : G ≅ G) :
    AutomorphismFixesCenter ((GroupScheme.baseChange b).mapIso f) ↔
      AutomorphismFixesCenter f :=
  ⟨of_baseChange b, fun h => h.baseChange b⟩

end Langlands.GroupScheme.AutomorphismFixesCenter

namespace Langlands.GroupScheme

/-- Full scheme-theoretic centre fixation is detected by fpqc change of base. -/
def FullCenterFixationBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (G : GroupScheme S) (f : G ≅ G),
    AutomorphismFixesCenter ((GroupScheme.baseChange b).mapIso f) ↔
      AutomorphismFixesCenter f

/-- Full-centre fixation descends and ascends through fpqc base change. -/
theorem fullCenterFixationBaseChange : FullCenterFixationBaseChangeStatement.{u} := by
  intro S S' b _ _ _ G f
  exact AutomorphismFixesCenter.baseChange_iff b f

end Langlands.GroupScheme
