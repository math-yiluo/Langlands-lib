import Langlands.GroupScheme.Rational.FiniteSeparableQuotientLifts
import Langlands.GroupScheme.Rational.QuotientPointCocycle
import Mathlib.AlgebraicGeometry.EffectiveEpi

/-! # Finite separable cocycle vanishing and rational quotient lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.QuotientPointCocycle

variable {F : Type u} [Field F]
    {N G Q : GroupScheme (Spec (CommRingCat.of F))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hker : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    (hvanish : ∀ (L : Type u) [Field L] [Algebra F L]
      [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ : Cocycle N (specOver F L)), ξ.IsTrivial)

include hker hvanish in
/-- Smooth surjectivity and vanishing on every finite separable cover
give surjectivity on rational points of an actual represented-kernel quotient. -/
theorem surjective_of_finiteSeparable_vanishing :
    Function.Surjective
      (fun x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X =>
        x ≫ q.hom.hom) := by
  intro y
  obtain ⟨L, _, _, hfinite, hseparable, g, hg⟩ :=
    exists_finiteSeparable_quotient_lift G q.hom.hom y
  let : FiniteDimensional F L := hfinite
  let : Algebra.IsSeparable F L := hseparable
  let : IsRegularEpi (specOver F L).hom :=
    isRegularEpi_of_flat_of_surjective_of_isAffine _
  exact exists_lift_of_isTrivial n q hker y g hg
    (hvanish L (obstruction n q hker y g hg))

/-- Choose a rational lift, with its proved image equation, from the
finite-separable kernel-cocycle vanishing hypothesis. -/
def quotientPointLiftOfFiniteSeparableVanishing
    (y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Q.X) :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X //
      x ≫ q.hom.hom = y} :=
  Classical.choice (by
    obtain ⟨x, hx⟩ := surjective_of_finiteSeparable_vanishing n q hker hvanish y
    exact ⟨⟨x, hx⟩⟩)

end Langlands.GroupScheme.QuotientPointCocycle
