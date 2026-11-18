import Langlands.AlgebraicGeometry.StrictLocalEtaleLimit

/-! # Statement: strictly local limits of affine etale neighbourhoods exist -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every point of an affine scheme admits a strictly Henselian local affine
limit of a small cofiltered diagram of affine etale neighbourhoods. This is
an existential consequence of strict henselization and its etale-algebra
presentation, retaining only the data in `StrictLocalEtaleLimit`. -/
def StrictLocalEtaleLimitExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (s : S), Nonempty (StrictLocalEtaleLimit S s)

end Langlands.AlgebraicGeometry
