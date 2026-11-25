/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveExtension
import WeilConjectures.AlgebraicGeometry.EtaleSmallInjectiveCriterion

/-! Coefficient universe lift on the small étale site. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coefficient lift preserves injective abelian sheaves on the small étale site.
Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO.
(blueprint: lem-sc-etale-ulift-injective)

Proof: Replace the small étale site by its essentially u-small affine model using
`AffineEtale.sheafEquiv`, and then by a u-small skeleton with transported topology.
Restriction commutes with coefficient lift. The free abelian sheaf on a representable
has u-small values: the representable and free presheaf are u-small, and sheafification
on this u-small site uses u-small limits and colimits. These constructions commute
with ULift. A subsheaf of the lifted free representable is u-small objectwise.
Shrink its values and transport the restrictions, group operations, and sheaf condition
to obtain a small-coefficient sheaf. Full faithfulness of ULift descends its inclusion
and any map to the lift of I. Injectivity of I extends that map over the small free
representable; lifting gives an extension over the large one. Tag 01DO gives injectivity
of the lifted sheaf. Transport back through the site equivalences. The argument also
applies to the empty scheme and the zero injective sheaf. -/
theorem etale_ulift_injective (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I] :
    Injective
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj I) := by
  apply etale_injective_of_small_extensions X
  intro A B hB f hf g
  exact etale_ulift_injective_extension X I hB f g

end AlgebraicGeometry.Scheme
