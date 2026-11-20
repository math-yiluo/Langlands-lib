import Langlands.GroupScheme.HomScheme.AffineFiberTorusAdicHom
import Langlands.GroupScheme.HomScheme.AffineFiberTorusAdicLimits

/-! # Adic effectivity of closed tori with affine ambient fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- The presheaf of actual closed tori in a smooth separated quasi-compact group
with affine residue fibres satisfies the adic limit condition. -/
def AffineFiberClosedToriAdicEffectivityStatement : Prop :=
  ∀ {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    HasAffineResidueFibers G → AdicLimits (smallAdmissiblePresheaf G)

/-- Algebraize the compatible torus homomorphisms on each complete local test
and apply the adic comparison for closed subgroups. -/
theorem affineFiberTorusAdicLimits : AffineFiberClosedToriAdicEffectivityStatement.{u} := by
  intro S G _ _ _ hG
  apply affineFiberTorusAdicLimits_of_homEffectivity G hG
  intro A _ _ _ _ f H hH s _
  let K := (baseChange f).obj G
  have : Smooth K.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom f))
  have : IsSeparated K.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom f))
  have : QuasiCompact K.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom f))
  exact (HomScheme.Adic.affineFiberTorusAdicHom A H K hH (hG.baseChange f)).surjective s

end Langlands.GroupScheme.TorusSubgroupModuli
