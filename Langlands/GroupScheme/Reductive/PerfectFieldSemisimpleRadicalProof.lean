import Langlands.GroupScheme.Reductive.PerfectFieldSemisimpleRadicalStatement
import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction
import Langlands.GroupScheme.Rational.SeparableSolvableRadicalProof
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Trivial radical and quotient by the radical over a perfect field: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PerfectFieldSemisimpleRadical

section Identity

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The kernel of the identity homomorphism is trivial on every test scheme. -/
theorem range_kernelι_id : SubgroupFunctor.range (kernelι (𝟙 G)) = ⊥ := by
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  simp

/-- The identity homomorphism is an fppf quotient by the trivial subgroup functor. -/
theorem isFppfQuotient_id : RelativeRoot.IsFppfQuotient ⊥ (𝟙 G) := by
  exact ⟨(inferInstance : Flat (𝟙 G.X.left)), (inferInstance : Surjective (𝟙 G.X.left)),
    (inferInstance : LocallyOfFinitePresentation (𝟙 G.X.left)), range_kernelι_id G⟩

end Identity

/-- Over a perfect field, Milne's Proposition 19.1 for the separable algebraic extension
`AlgebraicClosure k / k` makes every solvable radical geometric. -/
theorem isGeometricSolvableRadical_of_perfectField
    (h19 : SeparableAlgebraicSolvableRadicalStatement.{u})
    {k : Type u} [Field k] [PerfectField k]
    {R G : GroupScheme (Spec (CommRingCat.of k))}
    (hs : Smooth G.X.hom) (ha : IsAffineHom G.X.hom) (hc : ConnectedSpace G.X.left)
    {r : R ⟶ G} (hr : IsSolvableRadical r) : IsGeometricSolvableRadical r :=
  ⟨hr, h19 k (AlgebraicClosure k) G hs ha hc R r hr⟩

/-- Milne's Proposition 19.2 follows from Proposition 19.1. -/
theorem perfectFieldSemisimpleRadical_of_separableAlgebraic
    (h19 : SeparableAlgebraicSolvableRadicalStatement.{u}) :
    PerfectFieldSemisimpleRadicalStatement.{u} := by
  intro k _ _ G hs ha hc
  have := hs
  have := ha
  have := hc
  refine ⟨fun hG => ?_, fun R r hr Q q hQ hq => ?_⟩
  · obtain ⟨R, r, hr⟩ := solvableRadicalExistence k G
    have hbot : SubgroupFunctor.range r = ⊥ :=
      hG R r hr.isClosedSubgroup hr.smooth hr.connectedSpace hr.isSolvableGroupScheme
        hr.isNormal
    have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) (𝟙 G) := by
      rw [hbot]
      exact isFppfQuotient_id G
    exact (isGeometricSolvableRadical_of_perfectField h19 hs ha hc hr).isSemisimple_quotient
      (𝟙 G) hq
  · have := hQ
    exact (isGeometricSolvableRadical_of_perfectField h19 hs ha hc hr).isSemisimple_quotient
      q hq

end PerfectFieldSemisimpleRadical

open PerfectFieldSemisimpleRadical in
/-- **Milne, *Algebraic Groups* (2017), Proposition 19.2**: over a perfect field, a smooth
connected affine group with trivial solvable radical is semisimple, and every affine fppf
quotient by the solvable radical is semisimple. -/
theorem perfectFieldSemisimpleRadical : PerfectFieldSemisimpleRadicalStatement.{u} :=
  perfectFieldSemisimpleRadical_of_separableAlgebraic separableAlgebraicSolvableRadical

end Langlands.GroupScheme
