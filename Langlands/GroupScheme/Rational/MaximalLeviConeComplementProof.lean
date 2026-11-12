import Langlands.GroupScheme.Rational.MaximalLeviConeComplementReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Parabolics with a maximal Levi are determined by a missed direction: proof -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- **Parabolics with a maximal Levi are determined by a missed direction.** Let `P` be an
actual maximal proper rational parabolic of a connected reductive group `G` over a field,
with rational Levi `M` and split component `A`. A nonzero real character of `A` vanishing on
the central cocharacters that misses the positive cones of two compatible root presentations
of parabolics with Levi `M` forces the two parabolics, and their geometric unipotent radicals,
to have the same images in `G`. -/
theorem maximalLeviConeComplement : MaximalLeviConeComplementStatement.{u} :=
  maximalLeviConeComplementFromParabolicDynamic parabolicDynamic

end Langlands.GroupScheme
