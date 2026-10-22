# Restriction along an étale morphism

This module constructs restriction of sheaves along an étale scheme morphism
and its map on global sections. It is internal infrastructure for the
geometric cohomology framework, built from Mathlib's actual small étale sites
and the published `EtaleAutomorphism` and `EtaleDerivedSections` modules.
It is not a transcription of a named result of Harris.

## Sites and restriction

Let `X` and `Y` be schemes in universe `u`, and let `f : Y ⟶ X` be étale.
`siteMap f : Y.Etale ⥤ X.Etale` sends an étale structure map `U ⟶ Y`
to its composite `U ⟶ Y ⟶ X`, leaving the underlying scheme and arrows
unchanged. It is Mathlib's `MorphismProperty.Over.map`.

Three instances establish the properties needed for sheaf restriction.

- `siteMap_preservesPullbacks` proves preservation of pullbacks by comparison
  with the functor forgetting to schemes. That forgetful functor preserves
  pullbacks and reflects isomorphisms, and hence reflects the relevant limits.
- `siteMap_isContinuous` uses pullback preservation and preservation of
  covering families. The small étale precoverage is pulled back from the
  scheme precoverage along the forgetful functor. The two composites to
  schemes are equal by functor extensionality, so covering families are
  preserved.
- `siteMap_isCocontinuous` uses the pointwise characterization of covering
  sieves from `EtaleAutomorphism.mem_smallEtaleTopology_iff`. A covering arrow
  into `siteMap f U` has an étale source over `Y` by composing its arrow to
  `U` with `U`'s structure morphism. This supplies a lift of each covered
  point. Downward closure of the original sieve verifies membership.

For any category `A`, `restriction f A` is the continuous precomposition
functor from sheaves on `X` to sheaves on `Y`. Its value at a sheaf `F` has
sections

```text
(restriction f A).obj F (U → Y) = F (U → Y → X).
```

No sheaf condition or map on sheaves is assumed as an additional input.
Continuity proves that precomposition preserves the sheaf condition.

`restrictionComp f A g`, for étale `g : Z ⟶ Y`, is the natural isomorphism
from restriction along `f` followed by restriction along `g` to restriction
along `g ≫ f`. `restrictionId A` identifies restriction along the identity
of `X` with the identity functor. Both are induced by Mathlib's
`MorphismProperty.Over.mapComp` and `mapId` isomorphisms.

## Sections

`terminalSectionsMap f A` is a natural transformation

```text
F ↦ F(terminal X.Etale)
    ⟶ F ↦ ((restriction f A).obj F)(terminal Y.Etale).
```

For each sheaf its component is the contravariant restriction map along
the unique arrow from `siteMap f (terminal Y.Etale)` to the terminal object
of `X.Etale`. Naturality is the naturality of a sheaf morphism.
`terminalSectionsMap_comp` proves compatibility with successive restrictions,
using `restrictionComp` to identify the targets.
`terminalSectionsMap_id` proves that identity restriction gives the identity
on sections after applying `restrictionId`.
The proofs combine presheaf maps and use uniqueness of arrows into a terminal
object.

For a commutative ring `R : Type u`, the module proves that
`restriction f (ModuleCat.{u} R)` is additive and `R`-linear: both properties
hold componentwise. `sectionsMap f R` transports `terminalSectionsMap`
through `EtaleDerivedSections.sectionsIso`, giving the natural transformation

```text
EtaleDerivedSections.sections X R
  ⟶ restriction f (ModuleCat R) ⋙ EtaleDerivedSections.sections Y R.
```

Thus the target uses the published global-section functor defined by the
constant-sheaf adjunction.

## Scope and provenance

This construction generalizes the already published automorphism restriction
to all étale morphisms and reuses the same small étale topology. Its intrinsic
obligations are proved in the accompanying Lean file; no new axioms or assumed
comparison maps are introduced. The site and sheaf constructions come from
the pinned Mathlib modules `AlgebraicGeometry.Sites.Etale`,
`CategoryTheory.MorphismProperty.OverAdjunction`,
`CategoryTheory.Sites.Continuous`, and the precoverage framework.

Only the schemes and, in the module-coefficient part, the ring and coefficient
modules share universe `u`; the general coefficient category `A` has
independent object and morphism universes. The hypothesis that `f` is étale is
essential to this particular site functor. General scheme morphisms, including
arbitrary infinite algebraic base extensions, are outside this module.

The file does not construct adjoints of restriction, prove its exactness or
preservation of injectives, or construct derived cohomology pullbacks.
It supplies no compact-support map, Hecke operator, Shimura specialization,
or comparison with the automorphism action on cohomology. Those remain
subsequent construction or comparison obligations in the broader framework.
