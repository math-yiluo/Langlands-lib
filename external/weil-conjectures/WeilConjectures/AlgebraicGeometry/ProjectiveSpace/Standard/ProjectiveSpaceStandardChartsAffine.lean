/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-!
# Standard charts and coordinate sections of projective space

## References

* Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end
end AlgebraicGeometry.ProjectiveSpace
