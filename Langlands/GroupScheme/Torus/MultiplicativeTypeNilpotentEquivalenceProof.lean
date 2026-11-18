import Langlands.GroupScheme.Torus.MultiplicativeTypeNilpotentEquivalenceStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleChartAssembly
import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleCoverLift
import Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence

/-! # Multiplicative-type groups over nilpotent thickenings -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- Base change to a nilpotent quotient is essentially surjective and fully
faithful on finite-type groups of multiplicative type. -/
theorem multiplicativeTypeNilpotentEquivalence :
    MultiplicativeTypeNilpotentEquivalenceStatement.{u} := by
  intro A _ J hJ
  dsimp only
  let r := Spec.algebraMap A (A ⧸ J)
  have : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk J))
      Ideal.Quotient.mk_surjective
  have : Surjective r :=
    Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence.spec_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (by simpa using hJ)
  constructor
  · intro H₀ hH₀
    classical
    have charts (x : Spec (CommRingCat.of (A ⧸ J))) := exists_splitChartLift J hH₀ x
    choose U V p t q hp hx hsq hs using charts
    apply exists_lift_of_etale_splitting_charts r p t q hsq hp _ H₀ hs
    intro x
    obtain ⟨v, hv⟩ := hx x
    exact ⟨x, v, hv⟩
  · intro H K hH hK
    exact hH.baseChange_hom_bijective_of_surjective_closedImmersion hK r

end Langlands.GroupScheme
