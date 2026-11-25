/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.AlgebraicGeometry.NormalEtale

/-!
# Locally constant sheaves on a normal scheme extend uniquely over a dense open

Let `X` be a locally noetherian scheme whose local rings are integrally closed domains. The
local rings of étale `X`-schemes are then integrally closed domains as well
(`AlgebraicGeometry.Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain`), so for
an open immersion `j : U ⟶ X` with dense image and a locally constant sheaf `G` on `X`, the unit
`G ⟶ j_* j^* G` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction_of_isDomain_stalk`).
This is part (3) of the blueprint lemma `theorem-purity-real-sheaves-curves`, at a finite
coefficient level.

## Main statements

- `AlgebraicGeometry.Etale.isDomain_stalk_left_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed_stalk`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X U : Scheme.{u}}

/-- The local rings of an étale scheme over a scheme whose local rings are integrally closed
domains are integral domains
(`AlgebraicGeometry.Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain`).
-/
lemma isDomain_stalk_left_of_isIntegrallyClosed_stalk
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (W : X.Etale) (w : W.left) : IsDomain (W.left.presheaf.stalk w) :=
  (Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain W.hom hX w).1

/-- Blueprint `theorem-purity-real-sheaves-curves`, part (3), at a finite coefficient level:
**locally constant sheaves on a normal scheme extend uniquely over a dense open.** For a locally
noetherian scheme `X` whose local rings are integrally closed domains, an open immersion
`j : U ⟶ X` with dense image and a locally constant sheaf `G` of modules on the small étale site
of `X`, the unit `G ⟶ j_* j^* G` is an isomorphism: the local rings of étale `X`-schemes are
again integrally closed domains. -/
theorem isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (j : U ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j.base))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf G] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app G) :=
  isIso_unit_upperStarLowerStarAdjunction_of_isDomain_stalk j
    (isDomain_stalk_left_of_isIntegrallyClosed_stalk hX) hj G

end Etale

end AlgebraicGeometry
