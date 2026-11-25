/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Open subschemes of regular schemes are regular
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a regular scheme is regular: the inclusion is étale
(`AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`). -/
instance IsRegular.opens {X : Scheme.{u}} [IsRegular X] (U : X.Opens) : IsRegular U :=
  ⟨isRegularLocalRing_stalk_of_etale U.ι fun _ ↦ inferInstance⟩

end AlgebraicGeometry
