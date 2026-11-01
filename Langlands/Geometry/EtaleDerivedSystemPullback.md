# Geometric pullback of whole derived coefficient systems

Author: Worker 13.

This internal construction applies the published
[actual derived etale pullback](EtaleDerivedPlusPullback.md) and its
[identity and composition laws](EtaleDerivedPlusPullbackFunctoriality.md)
to an arbitrary diagram of actual coefficient sheaves. The construction
uses categorical whiskering; it asserts no new original-literature theorem.

## Inputs and systems

Let `X`, `Y` be schemes in universe `u`, let `R : Type u` be a fixed
commutative ring, and let `f : Y ⟶ X` be etale. For an arbitrary category
`J`, with independent object and morphism universes `v`, `w`, take
`D : J ⥤ EtaleDerivedSections.ModuleSheaf X R`. These are actual small-etale
sheaves of `ModuleCat R`; every transition of `D` is an actual sheaf map.
No invertibility of those maps is required.

The sheaf derived categories on `X`, `Y` (and `Z` for composition) and
the module derived category have independent localization universes
`wX`, `wY`, `wZ`, `wT`. The imported derived-section functor inserts a
sheaf in degree zero and applies actual bounded-below right-derived
ordinary global sections.

The target coefficient system is exactly
`D ⋙ EtalePullback.restriction f (ModuleCat R)`, including every restricted
transition. No identification with a separately constructed associated
sheaf or base-changed torsor system is assumed.

## The actual maps and naturality

`systemDerivedSectionsMap f R D` is the natural transformation

```text
D ⋙ derivedSections X R
  ⟶ (D ⋙ restriction f (ModuleCat R)) ⋙ derivedSections Y R.
```

It is `Functor.whiskerLeft D (derivedSectionsMap f R)`; its component
at `j` is the actual derived geometric map of `D.obj j`.
`systemDerivedSectionsMap_naturality` records its commuting square
for each original coefficient transition, using the same transition
restricted to `Y` on the target.

`systemDerivedSectionsMapFunctor` constructs this transformation
naturally on the whole category of `J`-indexed sheaf diagrams by applying
`Functor.whiskeringRight` to `derivedSectionsMap f R`.
Its component is the preceding map, as proved by reflexivity.
Its naturality field proves the commuting square for an arbitrary
natural transformation `D ⟶ E` of coefficient systems.

`systemCohomologyMap f R D q` and `systemSectionsMap f R D` whisker the
published ordinary cohomology and ordinary section maps by `D`.
Consequently they too retain every coefficient transition.

## Canonical recovery and geometric laws

`systemDerivedSectionsHomologyIso X R D q` identifies degree-`q`
cohomology of the entire derived system with `D ⋙ cohomology X R q`.
`systemDerivedSectionsZeroIso X R D` similarly identifies degree zero
with `D ⋙ sections X R`. Each uses the functor associator and the
whiskered canonical recovery isomorphism for actual derived sections.
Here `q : ℕ` indexes cohomology, independently of the objects of `J`.

`systemDerivedSectionsMap_homology` proves equality of the two natural
transformation paths obtained by applying homology to the actual derived
pullback and then recovering ordinary cohomology, or first recovering
and then applying `systemCohomologyMap`. The degree-zero counterpart
`systemDerivedSectionsMap_zero` uses `systemSectionsMap`.
Both proofs apply the published single-sheaf recovery equation at every
vertex. They preserve the specified canonical comparisons.

`systemDerivedSectionsMap_id` proves that pullback along the identity,
followed by the derived image of the actual identity-restriction comparison,
is the identity natural transformation of the whole derived system.
For etale `g : Z ⟶ Y`, `systemDerivedSectionsMap_comp` proves that the
two successive maps followed by the derived image of `restrictionComp`
equal pullback along `g ≫ f`. Both proofs use natural-transformation
extensionality and the actual single-sheaf derived identity/composition
laws. Equality of derived maps is never inferred from homology equality.

## Scope

This construction concerns ordinary derived global sections of degree-zero
sheaves over a fixed scalar ring, along etale scheme maps. It supplies
no compact supports, traces, scalar extension, inverse limits or claims
about commuting with limits. It does not identify a target associated
sheaf system from independently base-changed torsors, construct an actual
Harris Shimura scheme, or assert analytic uniformization or arithmetic
Galois comparison.
