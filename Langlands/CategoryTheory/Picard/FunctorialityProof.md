# Functoriality of the categorical Picard group: proofs

This module proves the three proposition definitions of
[FunctorialityStatements.md](FunctorialityStatements.md) in the namespace
`Langlands.CategoryTheory.PicardGroup`. Worker 270 wrote the Lean proofs and
this explanation. The statement module and the definitions it imports from
`Langlands.CategoryTheory.Picard.Basic` are imported unchanged.

| Published statement | Closing theorem |
| --- | --- |
| `MapIdentityStatement C` | `mapIdentity` |
| `MapCompositionStatement F G` | `mapComposition` |
| `MapIsoStatement F G` | `mapIso` |

## Signatures

Each closing theorem repeats the complete outer parameter list of its
statement, in the same order. Every category `C`, `D`, `E` has its own object
universe and its own morphism universe, six independent universe levels in
all. Each category carries explicit `Category`, `MonoidalCategory` and
`BraidedCategory` instances, and each functor carries a `Functor.Monoidal`
instance, exactly as in the statements. `mapIdentity` takes `C` explicitly;
`mapComposition` and `mapIso` take the categories implicitly and the functors
explicitly. `mapIso` adds no hypothesis: the natural isomorphism `F ≅ G` is
the bound variable of `MapIsoStatement` and is introduced inside the proof.
No hypothesis asks that a functor preserve the braidings or that the natural
isomorphism respect the monoidal structures.

## Common reduction

All three conclusions are equalities of additive homomorphisms. Each proof
first applies `AddMonoidHom.ext`, which reduces the equality to agreement at
every class `x : PicardGroup C`. Then it applies the published `PicardGroup.ext`.
This lemma says that two Picard classes are equal when their underlying
skeleton classes `toSkeletonClass` are equal. The published simp lemma
`toSkeletonClass_map` rewrites the class of `map F x` as
`F.mapSkeleton.obj (toSkeletonClass x)`; this holds by definition, since
`map F` is `Units.map (Skeleton.monoidHom F)` followed by the additive type
tag. Next, `toSkeleton_representative` rewrites `toSkeletonClass x` as
`toSkeleton (representative x)`, the class of the chosen representative
object. Mathlib's `Functor.mapSkeleton_obj_toSkeleton` then evaluates the
induced skeleton functor on that class:
`F.mapSkeleton.obj (toSkeleton X) = toSkeleton (F.obj X)`.
After these rewrites each goal compares the classes of explicit objects.

## Identity

In `mapIdentity`, `AddMonoidHom.id_apply` simplifies the right-hand side to
`toSkeletonClass x`. The reduction turns the left-hand side into
`toSkeleton ((𝟭 C).obj (representative x))`. `Functor.id_obj` rewrites this
as `toSkeleton (representative x)`, and the two sides agree.

## Composition

In `mapComposition`, `AddMonoidHom.comp_apply` rewrites the right-hand side
as `map G (map F x)`, so `map F` is applied first and then `map G`, the order
of the statement. Three uses of `toSkeletonClass_map` and three uses of
`Functor.mapSkeleton_obj_toSkeleton` reduce the two sides to
`toSkeleton ((F ⋙ G).obj (representative x))` and
`toSkeleton (G.obj (F.obj (representative x)))`. `Functor.comp_obj` rewrites
the first as the second. The composite's `Functor.Monoidal` instance is the
one Mathlib provides and that the statement already uses. The proof never
inspects its tensor or unit comparisons, since the class of an object does
not depend on them.

## Natural isomorphism

In `mapIso`, introduce the natural isomorphism `e : F ≅ G`. The reduction
leaves `toSkeleton (F.obj (representative x)) = toSkeleton (G.obj
(representative x))`. The component `e.app (representative x)` is an
isomorphism `F.obj (representative x) ≅ G.obj (representative x)`. Mathlib's
`congr_toSkeleton_of_iso` turns an isomorphism into equality of skeleton
classes. Only this single component is used. Neither naturality of `e` nor
any compatibility with the monoidal structures of `F` and `G` is needed.

## Scope

Only these three laws are proved. The module adds no definitions, no helper
lemmas and no axioms. `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for each closing theorem. It proves no
statement about Picard groups of schemes or other specific categories.
