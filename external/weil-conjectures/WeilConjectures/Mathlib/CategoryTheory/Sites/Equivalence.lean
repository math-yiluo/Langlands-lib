/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence

/-!

# Transporting sheafification to the small model of a site

Mathlib's `CategoryTheory.hasSheafifyEssentiallySmallSite` deduces sheafification on an
essentially `w`-small site `(C, J)` from sheafification on its small model. This file
proves the converse transport, which is the direction one usually has at hand:

```
                (equivSmallModel C).inverse
  (C, J)  ←──────────────────────────────────  (SmallModel C, K)
                (equivSmallModel C).functor
     with  K = (equivSmallModel C).inverse.inducedTopology J
```

`(equivSmallModel C).functor` is a dense subsite for these two topologies, so
`CategoryTheory.Equivalence.hasSheafify` carries `HasSheafify J A` over to
`HasSheafify K A`.

## Main results

- `CategoryTheory.hasSheafify_inducedTopology_equivSmallModel`: sheafification on a site
  transports to the induced topology on its small model.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
  (A : Type u₁) [Category.{v₁} A]

/-- Sheafification on a site transports to the induced topology on its small model. -/
lemma hasSheafify_inducedTopology_equivSmallModel [HasSheafify J A] :
    HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J) A :=
  have : (equivSmallModel.{w} C).symm.inverse.IsDenseSubsite J
      ((equivSmallModel.{w} C).inverse.inducedTopology J) :=
    inferInstanceAs ((equivSmallModel.{w} C).functor.IsDenseSubsite _ _)
  (equivSmallModel.{w} C).symm.hasSheafify _ J A

end CategoryTheory
