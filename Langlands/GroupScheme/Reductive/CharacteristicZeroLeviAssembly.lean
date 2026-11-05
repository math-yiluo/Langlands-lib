import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviReduction
import Langlands.GroupScheme.Reductive.CharacteristicZeroUnipotentExtension
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof

/-! # Levi assembly conditional on reductive vector-kernel splitting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace ReductiveUnipotentQuotient

variable {k : Type u} [Field k] [CharZero k]
    (hvector : CharacteristicZeroReductiveVectorExtensionStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : ReductiveUnipotentQuotient G)

include hvector in
/-- The published stable-vector proof and unipotent-kernel induction construct
a Levi section, conditional on the displayed vector-extension input. -/
theorem exists_leviSection : ∃ j : D.quotient ⟶ G, j ≫ D.projection = 𝟙 D.quotient := by
  let : Smooth D.projection.hom.hom.left := D.smooth_projection
  let : Surjective D.projection.hom.hom.left := D.isFppfQuotient.2.1
  let : ConnectedSpace (kernel D.projection).X.left := D.connectedSpace_kernel
  exact CharacteristicZeroUnipotentExtension.exists_section
    RelativeRoot.splitUnipotentStableVectorSubgroup hvector
    D.quotient D.isConnectedReductive G D.projection D.isUnipotent_kernel

/-- A chosen original-field homomorphic section of the reductive quotient.
The vector-extension theorem remains an explicit premise. -/
def leviSection : D.quotient ⟶ G :=
  Classical.choose (exists_leviSection hvector D)

/-- The chosen Levi section splits the actual quotient projection. -/
theorem leviSection_comp : leviSection hvector D ≫ D.projection = 𝟙 D.quotient :=
  Classical.choose_spec (exists_leviSection hvector D)

end ReductiveUnipotentQuotient

/-- The exact Levi target, conditional only on the reductive vector-extension
statement. Stable-vector existence is supplied by its published proof. -/
theorem characteristicZeroLeviDecomposition_of_reductiveVectorExtensions
    (hvector : CharacteristicZeroReductiveVectorExtensionStatement.{u}) :
    CharacteristicZeroLeviDecompositionStatement.{u} := by
  apply characteristicZeroLeviDecomposition_of_reductiveExtensionSections
  intro k _ _ E H _ _ _ q _ _ _ hH hU
  exact CharacteristicZeroUnipotentExtension.exists_section
    RelativeRoot.splitUnipotentStableVectorSubgroup hvector H hH E q hU

end Langlands.GroupScheme
