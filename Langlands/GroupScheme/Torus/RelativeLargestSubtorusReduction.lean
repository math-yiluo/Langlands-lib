import Langlands.GroupScheme.Torus.RelativeLargestSubtorusStatement
import Langlands.GroupScheme.Torus.UniversalSubtorusTransport

/-! # Reduction of the largest-subtorus statement to universal existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Universal-subtorus existence implies existence and stability for every largest
closed relative subtorus, exactly as in the published statement. -/
theorem relativeMultiplicativeTypeLargestSubtorus_of_exists_universal
    (hex : ∀ (S : Scheme.{u}) (H : GroupScheme S),
      RelativeMultiplicativeType.IsMultiplicativeType H →
        ∃ (T : GroupScheme S) (j : T ⟶ H), IsUniversalSubtorus j) :
    RelativeMultiplicativeTypeLargestSubtorusStatement.{u} := by
  intro S H hH
  obtain ⟨T, j, hj⟩ := hex S H hH
  refine ⟨⟨T, j, hj.isLargest⟩, ?_⟩
  intro T' k hk S' b
  obtain ⟨a, ha⟩ := hk.2.2 T j hj.1 hj.2.1
  exact ((hj.of_factor hk.1 hk.2.1 a ha).baseChange b).isLargest

end Langlands.GroupScheme
