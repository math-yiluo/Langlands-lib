import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Statement: the trivial locus of a homomorphism into a separated group is closed -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Closedness of the trivial locus** (SGA 3, IX, Corollaire 5.3, closedness part of its
proof). Let `S` be a scheme, `H` an `S`-group of multiplicative type, `G` a separated
`S`-group and `u : H ⟶ G` a homomorphism. The set of points `s ∈ S` at which the fibre `u_s`
over the residue field `κ(s)` is the trivial homomorphism is closed in `S`. -/
def MultiplicativeTypeTrivialLocusClosedStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S), IsMultiplicativeType H → IsSeparated G.X.hom →
    ∀ u : H ⟶ G,
      IsClosed {s : S | ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u).hom.hom = 1}

end Langlands.GroupScheme
