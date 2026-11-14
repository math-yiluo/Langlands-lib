import Langlands.GroupScheme.Reductive.LocalSplitRootWeightFreeness
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement

/-! # The local isomorphism target from the affine isomorphism theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Local root-space trivializations supply the hypotheses of the affine
isomorphism theorem over every commutative local ring. -/
theorem localSplitIsomorphismTheorem_of_affine
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u}) :
    LocalSplitIsomorphismTheoremStatement.{u} := by
  intro R _ _ G H _ _ hG hH I I' _ _ i i' hi hi' hmax hmax' J J' P Q hP hQ hPQ
  obtain ⟨f⟩ := hPQ
  obtain ⟨φ, _, _, _⟩ := hAffine R G H hG hH I I' i i' J J' P Q
    hi hmax hP
    (fun α => ⟨localRootWeightSpaceEquiv G hG I i hmax P hP α⟩)
    hi' hmax' hQ
    (fun α => ⟨localRootWeightSpaceEquiv H hH I' i' hmax' Q hQ α⟩)
    f.symm
  exact ⟨φ⟩

end Langlands.GroupScheme
