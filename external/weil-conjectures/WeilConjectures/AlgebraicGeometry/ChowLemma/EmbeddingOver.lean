/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# The Chow embedding over the source

For a separated morphism `f : X ⟶ S` of finite type over a Noetherian base, Chow's lemma
provides the Chow modification `π : X' ⟶ X` together with an immersion
`ι : X' ⟶ ℙ(index f; S)` over `S`. Since `ℙ(index f; X)` is the base change of
`ℙ(index f; S)` along `f`, the pair `(π, ι)` is a morphism `X' ⟶ ℙ(index f; X)` over `X`
(`AlgebraicGeometry.ChowModification.toProjectiveSpaceSource`), and it is an immersion. If `f`
is moreover proper, `ι` is a closed immersion and hence so is `(π, ι)`. This is the form of
Chow's lemma used in the reduction of proper base change to the projective line.

## Main definitions

- `AlgebraicGeometry.ChowModification.toProjectiveSpaceSource` — the morphism
  `(π, ι) : X' ⟶ ℙ(index f; X)` into the projective space over the *source* of `f`.

## Main results

- `AlgebraicGeometry.ChowModification.toProjectiveSpaceSource_over` and
  `AlgebraicGeometry.ChowModification.toProjectiveSpaceSource_map` — it is a morphism over `X`,
  and composing it with the base change `ℙ(index f; X) ⟶ ℙ(index f; S)` of `f` gives `ι`.
- `AlgebraicGeometry.ChowModification.isImmersion_toProjectiveSpaceSource` — it is an
  immersion.
- `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpaceSource` — if `f` is
  proper, it is a closed immersion.

## Blueprint

The declarations of this file implement `lemma:weil-pbc-chow-embedding-over-x` of the
proper-base-change blueprint for the Chow modification of a morphism to a Noetherian base;
the general form of that lemma, for an arbitrary lift into `ℙ(n; X) = X ×_S ℙ(n; S)`, is
`AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_lift`.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ChowModification

section

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

/-- The Chow modification `X'` of `f : X ⟶ S`, mapped into the projective space over the
source `X`: the morphism `(π, ι) : X' ⟶ X ×_S ℙ(index f; S) = ℙ(index f; X)` induced by the
modification `π` and the immersion `ι` into the projective space over `S`, i.e. the lift of

```
  ChowModification f
       │       ╲ toProjectiveSpace
       │        ╲
       │         ↘   map (index f) f
       │   ℙ(index f; X) -----------> ℙ(index f; S)
       │         │                          │
  modificationMap│ ↘                        │ ↘
       │         ↓                          ↓
       └──────>  X ----------- f ---------> S
```

into the cartesian square on the right. -/
def toProjectiveSpaceSource : ChowModification f ⟶ ℙ(index f; X) :=
  ProjectiveSpace.liftBaseChange (modificationMap f) (toProjectiveSpace f)
    (toProjectiveSpace_over f).symm

/-- `toProjectiveSpaceSource f` is a morphism over `X`:

```
                     toProjectiveSpaceSource
  ChowModification f ------------------------> ℙ(index f; X)
                    ╲                        ╱
     modificationMap ╲                      ╱ ↘
                      ↘         X        ↙
```

commutes. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceSource_over :
    toProjectiveSpaceSource f ≫ ℙ(index f; X) ↘ X = modificationMap f :=
  ProjectiveSpace.liftBaseChange_over _ _ _

/-- `toProjectiveSpaceSource f` composed with the base change
`ℙ(index f; X) ⟶ ℙ(index f; S)` of `f` is the immersion
`toProjectiveSpace f : X' ⟶ ℙ(index f; S)`:

```
                     toProjectiveSpaceSource
  ChowModification f ------------------------> ℙ(index f; X)
                    ╲                        ╱
   toProjectiveSpace ╲                      ╱ map (index f) f
                      ↘ ℙ(index f; S)    ↙
```

commutes. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceSource_map :
    toProjectiveSpaceSource f ≫ ProjectiveSpace.map (index f) f = toProjectiveSpace f :=
  ProjectiveSpace.liftBaseChange_map _ _ _

/-- The morphism `(π, ι) : X' ⟶ ℙ(index f; X)` is an immersion, since `ι` is one. -/
instance isImmersion_toProjectiveSpaceSource : IsImmersion (toProjectiveSpaceSource f) :=
  inferInstanceAs (IsImmersion (ProjectiveSpace.liftBaseChange _ _ _))

end

/-- **The Chow embedding over `X`**: for `f : X ⟶ S` proper, the morphism
`(π, ι) : X' ⟶ ℙ(index f; X)` of `toProjectiveSpaceSource` is a closed immersion, the diagram
being the one of `AlgebraicGeometry.ChowModification.toProjectiveSpaceSource_map`.
(blueprint: `theorem-chow-s-lemma-projective-form--2`) -/
instance isClosedImmersion_toProjectiveSpaceSource {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [IsProper f] :
    IsClosedImmersion (toProjectiveSpaceSource f) :=
  -- composed with the base change `ℙ(index f; X) ⟶ ℙ(index f; S)` of `f`, which is separated
  -- since `f` is, it is the closed immersion `ι`
  inferInstanceAs (IsClosedImmersion (ProjectiveSpace.liftBaseChange _ _ _))

end AlgebraicGeometry.ChowModification

end
