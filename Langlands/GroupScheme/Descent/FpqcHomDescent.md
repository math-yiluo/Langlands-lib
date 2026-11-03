# Fpqc descent of compatible group-scheme homomorphisms

This module constructs and proves uniqueness of descent for actual
group-scheme homomorphisms compatible with Čech data whose solutions are supplied.
It is an internal categorical consequence of the actual pullback definitions,
Mathlib's fpqc effective epimorphism theorem, and faithful monoidal pullback.
The proof is by Worker 1347 for cover-existence task
`a41119fb-a633-4b81-a979-4b08e9ddbb15`.

## Scope and interface

Let `p : S ⟶ B` be a morphism of schemes in arbitrary universe `u`, let
`C D : GroupScheme B`, and let
`f : (baseChange p).obj C ⟶ (baseChange p).obj D`.
Assume `hf : Compatible (canonicalDatum p C) (canonicalDatum p D) f`.
There is no commutativity, finite-type, affineness, smoothness, field,
or characteristic hypothesis.

`comp_eq_of_projection_eq` needs no geometric hypothesis on `p`. For
every scheme `Z` and maps `a b : Z ⟶ C_S`, equality of their projections
to `C` implies equality of the projections of `a ≫ f` and `b ≫ f` to `D`.

For `Flat p`, `Surjective p`, and `QuasiCompact p`:

- `underlying` constructs the morphism of underlying schemes `C ⟶ D`;
  `underlying_fac` is its factorization after the pullback projection.
- `underlying_over` proves that this map respects the structure morphisms
  to `B`, giving `overHom : C.X ⟶ D.X`.
- `pullback_overHom` recovers `f.hom.hom`, and `overHom_isMonHom`
  proves that the descended morphism preserves unit and multiplication.
- `hom : C ⟶ D` is the resulting actual group-scheme homomorphism.
  `baseChange_hom` states `(baseChange p).map (hom p f hf) = f`.
- `unique` identifies any other homomorphism with that same base change,
  and `existsUnique_hom` bundles existence and uniqueness.

## Implemented proof

Given `a` and `b` with equal original projection, take the pair of their
base coordinates as a map `r : Z ⟶ S ×_B S`. The first point and `r`
define a map to the first iterated pullback of `C_S`. The canonical
overlap isomorphism sends this map to `b` after projection to `C_S`.
To prove this equality, compare the original projection to `C` using
`canonicalOverlap_fst`, and compare the projection to `S` using the
structure-map equation of the overlap isomorphism and the pullback
condition. Applying the compatibility square to this map gives
`comp_eq_of_projection_eq`.

The projection `C_S ⟶ C` is itself fpqc, hence an effective epimorphism.
`EffectiveEpi.desc` applies to the composite `C_S ⟶ D_S ⟶ D`, using
the preceding all-scheme equality as its relation condition. Its
factorization equation proves `underlying_fac`. Epimorphism cancellation,
the pullback condition, and the structure-map equation for `f` show that
the descended morphism is over `B`.

The two pullback projections prove `pullback_overHom`. Pullback along `p`
is a faithful monoidal functor. The published generic lemma
`GaloisCocharacterDescent.isMonHom_of_faithfulMap` reflects the unit and
multiplication equations from those of `f`. `Grp.homMk` then constructs
`hom`; homomorphisms of group objects need no additional inverse equation.
Finally, faithfulness of the same pullback gives `unique`.

## Descent through supplied solutions

The namespace `Descent.Solution` extends the canonical construction.
Let `D : Datum p G`, `E : Datum p H`, `s : Solution D`, `t : Solution E`,
and `f : G ⟶ H` with `hf : Compatible D E f`. Under the same fpqc hypotheses,
`descendHom s t f hf : s.obj ⟶ t.obj` descends the compatible conjugate
`s.iso.hom ≫ f ≫ t.iso.inv` between the two canonical data.
Compatibility follows by composition and the inverse-compatibility lemma
from the published `Descent.Data` module.

`baseChange_descendHom` proves the square

```text
(baseChange p).map (descendHom s t f hf) ≫ t.iso.hom = s.iso.hom ≫ f.
```

It follows from `baseChange_hom` and cancellation of `t.iso.inv` with
`t.iso.hom`. `descendHom_unique` rewrites any other such square into equality
with the same conjugate and applies canonical uniqueness.
`existsUnique_descendHom` bundles these results.

## Remaining obligations

This construction requires the two objects over `B`, or solutions supplying
them, as inputs. It does not construct a descended object for an arbitrary
affine datum, assert affine object effectivity, or construct the datum of a cover.
Its internal provenance is the categorical argument described above; no
unproved effectivity or cover-existence statement is used as a premise.
