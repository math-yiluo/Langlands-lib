import Langlands.GroupScheme.Reductive.IsogenyRootDatumStatement
import Langlands.GroupScheme.Reductive.SplitIsogenyStatement
import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # A conditional reduction of the fixed-torus extension criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The induced-map assertion and realization assertion imply the criterion for
a fixed torus isogeny. This reduction does not supply either geometric input. -/
theorem splitIsogenyExtension_of_rootDatum_and_existence
    (hmap : IsogenyRootDatumStatement.{u}) (hex : SplitIsogenyExistenceStatement.{u}) :
    SplitIsogenyExtensionStatement.{u} := by
  intro k _ G G' hG hG' T T' hT hT' i i' hi hi' J J' _ _ P P' _ _ hP hP' t _ht
  constructor
  · rintro ⟨φ, hφ, hsq⟩
    obtain ⟨_, f, hw, hc, _, _⟩ :=
      hmap k G G' hG hG' T T' hT hT' i i' hi hi' φ t hφ hsq J J' P P' hP hP'
    exact ⟨f, hw, hc⟩
  · rintro ⟨f, hw, _hc⟩
    obtain ⟨φ, t', hφ, _, hsq, hw', _hc'⟩ :=
      hex k G G' hG hG' T T' hT hT' i i' hi hi' J J' P P' hP hP' f
    have heq : t' = t :=
      hT'.hom_ext_of_characters fun χ => (hw' χ).symm.trans (hw χ)
    exact ⟨φ, hφ, by simpa only [heq] using hsq⟩

/-- Bundle realization with the extension criterion derived from the induced-map
assertion. Both geometric statements remain explicit inputs. -/
theorem splitIsogenyTheorem_of_rootDatum_and_existence
    (hmap : IsogenyRootDatumStatement.{u}) (hex : SplitIsogenyExistenceStatement.{u}) :
    SplitIsogenyTheoremStatement.{u} :=
  ⟨hex, splitIsogenyExtension_of_rootDatum_and_existence hmap hex⟩

end Langlands.GroupScheme
