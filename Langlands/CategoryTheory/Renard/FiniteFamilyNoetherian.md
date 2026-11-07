# Noetherianity detected by a finite family of functors

Worker 1582. Internal derived infrastructure for the proofs of Renard VI.7.5,
Proposition and Theorem, printed pages 186–187 / PDF pages 192–193, in David
Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes
reductifs p-adiques (2026 version)--2026.pdf`.

In VI.7.5 Renard views the functor `R` of VI.7.2 as a functor into a product
of categories `M(M)_D`. He then argues that if a chain of subrepresentations
does not stabilize, neither does its image under the faithful exact `R`. The
Theorem's proof repeats this argument. This module replaces the product
category by a finite family of functors `F i : C ⥤ D i`, indexed by a type
`ι` with `[Finite ι]`, and proves the chain argument for such a family. All
target categories share one object universe and one morphism universe, and
these are independent of the source universes and of the index universe.
The finite-family formulation is derived here; Renard does not state it
separately. The Noetherian and finite-type predicates are exactly the
published `IsNoetherianObject`, `IsFiniteTypeObject` and
`IsNoetherianCategory` of Appendix A.I.2–A.I.3, printed pages 248–249 / PDF
pages 254–255.

## Definitions

- `JointlyReflectsMonoIsos F`: every monomorphism `f` with `(F i).map f` an
  isomorphism for every `i` is itself an isomorphism.
- `JointlyDetectsZero F`: every object `X` with `(F i).obj X` a zero object for
  every `i` is a zero object.

## Implemented proofs

`exists_functorSubobjectMap_lt` assumes that every `F i` preserves
monomorphisms and that the family jointly reflects isomorphisms between
monomorphisms. Under these assumptions, a strict inclusion `P < Q` of actual
subobjects stays strict under the published `functorSubobjectMap (F i) X` for
at least one `i`. The proof is by contradiction. Suppose no image is strict.
Mathlib's strict-subobject criterion then makes every `(F i).map` of the
inclusion `Subobject.ofLE P Q` an isomorphism. The joint reflection
hypothesis makes the inclusion itself an isomorphism. Its commuting
factorization then gives `P = Q`.

`noetherianObject_of_finite_family` takes, in addition, that `ι` is finite
and that every image `(F i).obj X` is Noetherian in Renard's sense. Its
conclusion is that `X` is Noetherian. Take a strictly increasing sequence
`f : ℕ → Subobject X`. For each `i`, the image sequence under
`functorSubobjectMap (F i) X` is monotone. It is therefore eventually
constant from some index `n i`, by Mathlib's chain condition and the
published `noetherianMathlibComparison`. Since `ι` is finite, the range of
`n` is bounded above by some `N`. Applying the previous lemma to
`f N < f (N + 1)` yields some `i` whose images are strictly increasing at
`N`. This contradicts the stabilization from `n i ≤ N`. Finiteness of the
family is used exactly in this pigeonhole step.

`noetherianCategory_of_finite_family` additionally assumes all source
subobject unions, and that the images of every finite-type source object
under all `F i` are Noetherian. Its conclusion is the source
`IsNoetherianCategory`.

In the abelian section all categories are abelian and every `F i` is
additive. `jointlyReflectsMonoIsos_of_jointlyDetectsZero` assumes, in
addition, that every `F i` preserves epimorphisms and that the family
jointly detects zero objects. It proves joint reflection of isomorphisms
between monomorphisms. Suppose a monomorphism `f` is sent to an isomorphism
by every `F i`. Each `(F i).map (cokernel.π f)` is then zero after
cancelling the epimorphism `(F i).map f`. It is also an epimorphism, so
`(F i).obj (cokernel f)` is zero. Joint detection makes `cokernel f` zero,
so `f` is an epimorphism and therefore an isomorphism.

`noetherianObject_of_finite_exact_family` and
`noetherianCategory_of_finite_exact_family` assume Renard's two-sided
`SequenceExact` for every `F i`. Its left part gives preservation of
monomorphisms, and its right part gives preservation of epimorphisms,
through Mathlib's short-exact criteria. These results combine the previous
theorems. They are the form in which a finite family of cuspidal Jacquet
functors, exact and jointly detecting zero objects, is to be used in VI.7.5.

## Scope

Only the generic categorical transfer is proved. This module does not
construct the cuspidal Jacquet functors and does not prove their
exactness, their joint detection of zero objects, or Noetherianity of their
images. It discharges neither exact represented-group VI.7.5 target.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
