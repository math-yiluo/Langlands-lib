import Langlands.GroupScheme.Torus.Lattice
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Compactness of the rational norm kernel of a torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-- For every torus over a nonarchimedean local field, the common kernel of the normalized
absolute values of its rational characters is compact in the canonical point topology. -/
def TorusNormKernelCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom T.X.hom] [LocallyOfFiniteType T.X.hom],
    GroupScheme.IsTorus T →
      letI : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
      letI : TopologicalSpace (GroupScheme.rationalPoints T) := rationalPointTopology F T.X
      IsCompact (rationalCommonNormKernel T : Set (GroupScheme.rationalPoints T))

end Langlands.Plancherel
