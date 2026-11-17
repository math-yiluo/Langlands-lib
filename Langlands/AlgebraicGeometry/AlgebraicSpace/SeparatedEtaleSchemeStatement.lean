import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-! # Schemehood of separated algebraic spaces with an etale structural atlas -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A separated algebraic space over a scheme is a scheme if it admits an
etale surjective scheme atlas whose structure map is etale. -/
def SeparatedEtaleSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (X : AlgebraicSpace S),
    IsSeparated X →
    HasAtlasProperty (@_root_.AlgebraicGeometry.Etale.{u}) X →
    IsRepresentedByScheme X

end Langlands.AlgebraicGeometry.AlgebraicSpace
