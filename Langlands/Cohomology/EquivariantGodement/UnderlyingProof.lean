import Langlands.Cohomology.EquivariantGodement.Statement
import Langlands.Sheaf.Equivariant.Godement.Underlying

/-!
# The underlying-complex comparison for the equivariant Godement complex

The published comparison isomorphism and its augmentation compatibility prove
the corresponding published proposition.
-/

namespace Langlands.Cohomology

universe u

/-- Forgetting equivariance identifies the equivariant Godement complex with
the ordinary Godement complex, compatibly with the augmentations. -/
theorem equivariantGodementUnderlying :
    EquivariantGodementUnderlyingStatement.{u} := by
  intro R G X _ _ _ _ _
  exact ⟨Sheaf.Equivariant.Godement.underlyingComplexIso R G X,
    fun F => Sheaf.Equivariant.Godement.underlyingComplexIso_augmentation F⟩

end Langlands.Cohomology
