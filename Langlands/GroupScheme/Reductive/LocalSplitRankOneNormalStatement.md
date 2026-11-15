# Statement: rank-one normalization of Weyl-normalized simple root data

This module defines the predicate `LocalSplitCell.RankOneNormal` and states, without proof,
that Weyl-normalized simple-root data over a local ring satisfy it. It contains one
definition and one `Prop`-valued statement, and no theorems.

## The predicate

Notation, from the imported modules:

- `rootPoint v Z x` is the point of `G` over `Z` given by `v : 𝔾ₐ ⟶ G` at the global
  function `x` (module `LocalSplitCell`);
- `weylPoint u u' = u'(-1) · u(1) · u'(-1)` is the corresponding global point;
- `G.constantPoint g Z` pulls a global point `g` back to `Z`;
- `cocharPoint ν Z t` is the point of the coordinate split torus `T_I` over `Z` with
  coordinates `t ^ ν j` (module `LocalSplitPositiveCell`);
- `i.hom.hom` is the underlying morphism of the torus `i : T_I → G`.

Let `R` be a commutative ring and `G` a group scheme over `Spec R`. Let
`i : T_I → G` be a coordinate split torus, `P : RootDatum J (I → ℤ) (I → ℤ)`, and
`v : J → (𝔾ₐ ⟶ G)`. For an index `a`, write `-a` for `P.reflectionPerm a a` (the index of
`-P.root a`) and `N = weylPoint (v a) (v (-a)) = v_{-a}(-1) v_a(1) v_{-a}(-1)`.
`RankOneNormal i P v a` is the conjunction of three conditions:

1. for every commutative ring `B` in universe `u`, every `s : Spec B → Spec R`, and every
   global function `x` on `Spec B`, `N v_a(x) N⁻¹ = v_{-a}(-x)` over `s`;
2. in the same generality, `N v_{-a}(x) N⁻¹ = v_a(-x)`;
3. `N · N = a^∨(-1)` as global points of `G`. Here `a^∨(-1)` is
   `cocharPoint (P.coroot a) (𝟙_) (-1) ≫ i.hom.hom`, the image under `i` of the torus
   point of the coroot of `a` at `-1`.

## Statement

`LocalSplitRankOneNormalStatement.{u}` says the following. Let `R` be a commutative local
ring and `G` a reductive group scheme over `Spec R` with affine structure morphism, all
in universe `u`. Let `I` be a finite type with decidable equality and
`i : T_I → G` a closed (`IsClosedSubgroup`) coordinate split torus, maximal on every
residue-field fibre (`IsFibrewiseMaximalTorus`). Let `P : RootDatum J (I → ℤ) (I → ℤ)`
be a fibrewise root datum of `(G, i)` (`IsFibrewiseRootDatumOf`), `b` a base of `P`, and
`u : J → (𝔾ₐ ⟶ G)`. Assume that for every simple root `a` of `b`:

- `u a` is a root parametrization of `i` for `P.root a`, and `u (-a)` is one for
  `P.root (-a)` (`IsRootParametrization`);
- `weylPoint (u a) (u (-a))` is a Weyl point of `i` acting by `P.reflection a`
  (`IsWeylPoint`).

Then `RankOneNormal i P u a` holds for every simple root `a`.

These hypotheses are exactly the conclusion of the published
`LocalSplitSimpleRootGroupStatement` (module
`Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction`) for one base,
without the reducedness of `R`.

## Provenance and scope

This is an internal statement, written for this project. It is the rank-one input of the
proof of the Isomorphism Theorem over an arbitrary local ring. Conrad, *Reductive group
schemes* (2014), Corollary 5.1.9 (printed pp. 140–141), treats the Weyl element
`w_a(X) = exp_a(X) exp_{-a}(-X⁻¹) exp_a(X)` built from a trivialization `X` of the root
space and its dual section `X⁻¹`. Its part 3 gives the conjugation of `U_a` by `w_a(X)`
into `U_{-a}`, and its part 4 gives `w_a(X)² = a^∨(-1)`. SGA 3, Exp. XXIII, 3.1.1 uses the
same identities. Conrad proves them from the classification of split groups of
semisimple rank one (Theorem 5.1.8), by explicit computation in `SL₂` and `PGL₂`.

The statement here starts instead from the condition that
`u_{-a}(-1) u_a(1) u_{-a}(-1)` is a Weyl point. In `SL₂`, with `u_a(x)` upper unitriangular
and `u_{-a}(y)` lower unitriangular with entry `c y`, this condition forces `c = 1`. Then
`N = [[0, 1], [-1, 0]]`, which gives the three identities. The statement asserts that the
same holds for every reductive group over a local ring, including rings with nilpotents.
It is not proved here; its proof over a general local ring is open in the Library.
