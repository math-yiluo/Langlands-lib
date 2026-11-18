import Langlands.GroupScheme.Reductive.WeilAbelianImageTriviality
import Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityStatement

/-! # Proof: homomorphisms with commutative image from a semisimple Weil restriction -/

universe u

namespace Langlands.GroupScheme

/-- **Homomorphisms with commutative image from a semisimple Weil restriction are trivial.** -/
theorem weilAbelianImageTriviality : WeilAbelianImageTrivialityStatement.{u} := by
  intro A B _ _ _ _ _ _ G' _ _ hred hss M T c hc X x
  exact WeilAbelianImage.app_eq_one G' c hc hred hss X x

end Langlands.GroupScheme
