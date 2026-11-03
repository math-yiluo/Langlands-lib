import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Statement: fpqc reflection of central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An fpqc change of base reflects the full central-isogeny predicate, including
local finite presentation and centrality of the scheme-theoretic kernel on all tests. -/
def CentralIsogenyFpqcReflectionStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) [Surjective b] [Flat b] [QuasiCompact b]
    (G H : GroupScheme S) (f : G ⟶ H),
    IsCentralIsogeny ((GroupScheme.baseChange b).map f) → IsCentralIsogeny f

end Langlands.GroupScheme
