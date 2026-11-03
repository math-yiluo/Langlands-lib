import Langlands.GroupScheme.UnitSubgroup
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # A canonical representative of a trivial unipotent radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

variable {k : Type u} [Field k]

/-- Every representation of the trivial group scheme fixes every vector. -/
theorem isUnipotent_trivial :
    IsUnipotent (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  intro n _ _ _ ρ
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro he
    have := congrFun he (Classical.choice (inferInstance : Nonempty n))
    exact one_ne_zero this
  · intro T g
    rw [toUnit_unique g (1 : T ⟶ (Grp.trivial _).X), map_one]
    exact Matrix.one_mulVec _

/-- The identity section represents the radical whenever the ground-field
unipotent radical is trivial. -/
theorem isUnipotentRadical_kernelUnit
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsSeparated G.X.hom]
    (hG : HasTrivialUnipotentRadical G) : IsUnipotentRadical (kernelUnit G) where
  isClosedSubgroup := kernelUnit_isClosedSubgroup G
  smooth := by
    change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  connectedSpace := by
    change ConnectedSpace (Spec (CommRingCat.of k))
    infer_instance
  isUnipotent := isUnipotent_trivial
  isNormal := by
    rw [range_kernelUnit]
    intro T g x _ hx
    have hx' : x = 1 := by
      simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hx
    simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot, hx', mul_one,
      mul_inv_cancel]
  greatest H j hj hs hc hu hn := by
    rw [hG H j hj hs hc hu hn, range_kernelUnit]

/-- A chosen actual representative of the trivial ground-field radical. -/
def trivialUnipotentRadical
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsSeparated G.X.hom]
    (hG : HasTrivialUnipotentRadical G) :
    Σ U : GroupScheme (Spec (CommRingCat.of k)), {j : U ⟶ G // IsUnipotentRadical j} :=
  ⟨Grp.trivial _, kernelUnit G, isUnipotentRadical_kernelUnit G hG⟩

end Langlands.GroupScheme
