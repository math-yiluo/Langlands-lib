# The Picard group of a regular local ring with one element inverted is trivial

`Langlands.CommutativeAlgebra.RegularLocalAwayPicardStatement.{u}` defines exactly
the proposition

```lean
∀ (R : Type u) [CommRing R], IsRegularLocalRing R →
  ∀ f : R, Subsingleton (CommRing.Pic (Localization.Away f))
```

It states that for every regular local commutative ring `R` and every element
`f` of `R`, the Picard group of the localization `R_f` has at most one element.
The universe `u` is arbitrary. The Lean file defines this proposition and
supplies no proof or new axiom.

## Conventions

The imports are `Mathlib.RingTheory.Localization.Away.Basic`,
`Mathlib.RingTheory.PicardGroup` and `Mathlib.RingTheory.RegularLocalRing.Defs`.
Every notion in the proposition is an existing Mathlib notion.

`IsRegularLocalRing R` extends `IsLocalRing R` and `IsNoetherianRing R`. Its
additional field is
`(IsLocalRing.maximalIdeal R).spanFinrank = ringKrullDim R`: the minimal number
of generators of the maximal ideal equals the Krull dimension. This is the usual
Noetherian regular-local convention, with finite dimension, and Mathlib tags it
with Stacks Definition 00KU. Regularity is an explicit implication premise
rather than an instance binder.

`Localization.Away f` is Mathlib's `Localization (Submonoid.powers f)`, the
localization `R_f = R[1/f]` of `R` at the multiplicative set of powers of `f`.
It is a commutative ring in the same universe `u`.

`CommRing.Pic A` is Mathlib's Picard group of a commutative ring `A`: the
isomorphism classes of invertible `A`-modules, with multiplication induced by
the tensor product over `A`; the identity element is the class of `A`, and the
inverse of a class is the class of the dual module. Here an `A`-module `M` is
invertible (`Module.Invertible A M`) when the canonical map
`Module.Dual A M ⊗[A] M → A` is bijective; by `Module.Invertible.right` it
suffices that `N ⊗[A] M ≃ₗ[A] A` for some `A`-module `N`. The classes are those
of modules whose carrier lies in the universe of `A`, here `u`.

### Meaning of `Subsingleton`

A group is a subsingleton exactly when its only element is the identity. Thus
`Subsingleton (CommRing.Pic (Localization.Away f))` says that the class of every
invertible `R_f`-module (with carrier in universe `u`) equals the identity class
`[R_f]`, i.e. every such invertible `R_f`-module is trivial. Mathlib's `CommRing.Pic.subsingleton_iff` states that
`Subsingleton (CommRing.Pic A)` holds if and only if every invertible `A`-module
`M` with carrier in the universe of `A` is free, and
`CommRing.Pic.mk_eq_one_iff_free` and `CommRing.Pic.mk_eq_one_iff` identify the
identity class with the free invertible modules and with the modules isomorphic
to `A`. Hence the proposition is equivalent to: for every regular local `R` in
universe `u`, every `f : R`, and every invertible `R_f`-module `M : Type u`, the
module `M` is free, equivalently isomorphic to `R_f`
(`Module.Invertible.free_iff_linearEquiv`). A private
development check confirmed this unfolding with `CommRing.Pic.subsingleton_iff`;
it is not part of this module.

### Scope

The proposition covers every regular local commutative ring and every element
`f`:

- `f = 0`: then `0` lies in the powers of `f`, so `R_0` is the zero ring and its
  Picard group is trivial; this case is included rather than excluded.
- `f` a unit: then `R_f` is isomorphic to `R` itself.
- `f` a nonzero element of the maximal ideal: this is the substantive case used
  in the factoriality argument below.

No domain, dimension, characteristic, residue-field, completeness, henselianity
or excellence premise is added.

## Original source

This is a direct formalization of the Stacks Project, More on Algebra,
Lemma 15.123.1, [Tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ):
“Let R be a regular local ring. Let f ∈ R. Then Pic(R_f) = 0.” The Stacks
statement writes the trivial Picard group additively as `0`; the Lean statement
says that the multiplicative group `CommRing.Pic (Localization.Away f)` is a
subsingleton. The Stacks lemma also places no restriction on `f`.

The original is retained as `0AFZ.html` in the registered source
`stacks-regular-local-ufd-2026-10-29`, entitled
*Stacks Project - Regular local rings are UFDs and factorization definitions
(HTML snapshot 2026-10-29)*, with directory SHA256
`49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`. The full
lemma, its proof and its three comments were read, together with the section
page `0FJH.html` and its two comments.

The Picard-group conventions are those of Stacks, More on Algebra,
Section 15.119, [Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW):
Definition 15.119.1 calls an invertible module trivial if it is isomorphic to
the ring; Lemma 15.119.2 shows that a module `M` is invertible if and only if
`M ⊗_R N ≅ R` for some module `N`, and that then `N ≅ Hom_R(M, R)`; and the text
after it defines `Pic(R)` as the group of isomorphism classes of invertible
modules under the tensor product. Mathlib's notion agrees: a module invertible
in Mathlib's sense satisfies this condition with `N` its dual, and conversely
`Module.Invertible.right` derives Mathlib invertibility from any such
isomorphism (with the tensor factors in either order, by commutativity of the
tensor product). This page is retained as
`0AFW.html` in the registered source `stacks-picard-groups-rings-0AFW-2026-11-01`
(directory SHA256
`08e0c00b7e7107f06fa769fd1d3253b4c3feff83d54dd85afc39c46ff259b02a`), with the
cited Lemmas 15.120.7 (`0AFX.html`) and 15.121.1 (`0AFY.html`); none of these
three pages has comments.

### Source proof and its retained correction

The Stacks proof takes an invertible `R_f`-module `L`, which is finite, and
chooses a finite `R`-module `M` with `M_f ≅ L` (Algebra, Lemma 10.126.3,
Tag 05N5). Since `R` is regular local, `M` has a finite free resolution over `R`
(Algebra, Proposition 10.110.1, Tag 00O7), so `L` is quasi-isomorphic to a
finite complex of free `R_f`-modules. Lemma 15.121.1 (Tag 0AFY) then gives
`[L] = n[R_f]` in `K_0(R_f)` for some integer `n`, and applying the determinant
map `K_0(R_f) → Pic(R_f)` of Lemma 15.120.7 (Tag 0AFX) shows that `L` is
trivial.

The retained page records a correction of this argument. Comment #8716
(Kentaro Inoue, 2 November 2023) suspected that the argument in the last two
sentences of the earlier proof was not correct because `R_f` does not
necessarily belong to `K_0(R)`, and suggested using surjectivity of
`Pic(R) → Pic(R_f)` instead.
Comment #8717 (Laurent Moret-Bailly, 3 November 2023) proposed substituting
“`[L_f] = n[R_f]` in `K_0(R_f)`” in the penultimate sentence. Comment #9358
(Stacks project, 4 June 2024) reports the fix in Stacks commit `814287db`. The
retained proof text uses this correction: the class computation takes place in
`K_0(R_f)`, not in `K_0(R)`, and the determinant map applied is the one for the
ring `R_f`. Its remaining subscript in `[L_f]` is harmless, since `L` is already an
`R_f`-module and `L_f = L`. The correction concerns only the proof; the lemma
statement, and hence this formalization, is unchanged by it. The section
comments #6705 and #6908 on `0FJH.html` concern suggested power-series additions
and do not affect this lemma.

This describes the source argument; no part of it is implemented in this
statement module, and the proposition itself does not mention `K_0` or
determinants. A proof may follow any valid route. One possible route replaces
the `K_0` argument by showing that the invertible module, being the localization
of a finite `R`-module with a finite free resolution, is stably free over `R_f`,
and then applying Mathlib's `Module.free_of_isStablyFree_of_invertible`.

## Role in the project

The assertion is the Picard-group input of the Stacks proof that regular local
rings are unique factorization domains (Lemma 15.123.2, Tag 0AG0; Library
statement `Langlands.CommutativeAlgebra.RegularLocalFactorialStatement`), which
applies it to `R_x` for a regular parameter `x`. This module imports only
Mathlib: it does not import or depend on `RegularLocalFactorialStatement` or on
any geometric extension statement, and it is intended to be proved independently
of them.
