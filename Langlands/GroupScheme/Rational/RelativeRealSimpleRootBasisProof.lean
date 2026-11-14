import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.LanglandsSimpleRootBasis
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Proof of the real simple relative-root basis -/

universe u

namespace Langlands.GroupScheme

/-- For a maximal split torus of a connected reductive group over any field, the
simple roots for a generic cocharacter form a real basis of the actual root span. -/
theorem relativeRealSimpleRootBasis : RelativeRealSimpleRootBasisStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  intro ν hν
  obtain ⟨D, _⟩ := relativeRootReflectionExistence k G hG T i hi
  have hT := hi.isSplitSubtorus.1
  refine ⟨realSimpleRootBasis i ν D hT (hT.finite_relativeRoots i) hν, ?_⟩
  intro α
  rw [realSimpleRootBasis_apply]
  rfl

end Langlands.GroupScheme
