# Functoriality and full-group equivariance of coefficient cochains

This module constructs functorial maps between the actual alternating cochain
spaces in `Langlands.Cohomology.Lie.CoefficientCochains`. It proves their
compatibility with that module's differential, and restricts the differential
to the actual submodule of cochains equivariant under every element of a group.
All new declarations are in `Langlands.Cohomology.Lie`.

## Parameters and scope

The scalar field `K`, the Lie algebras `L`, `L'`, `L''`, the coefficient spaces
`M`, `N`, `P`, and the group `G` have independent universes. Each Lie algebra
has its given `LieRing` and `LieAlgebra K` structures. Each coefficient space
has an additive commutative group and a `K`-module structure. No dimension,
finiteness, topology, connectedness or continuity hypothesis is imposed.

The construction and functor laws for `pullMap` need no Lie action on the
coefficient spaces and no characteristic-zero assumption. Differential
naturality additionally uses `CharZero K`, actual Lie-module structures on
`M` over `L` and `N` over `L'`, and the action compatibility specified below.
The full-group restriction similarly uses `CharZero K` and an actual Lie
module `M` over `L`. These characteristic-zero hypotheses allow use of the
published all-degree evaluation formulas for the differential.

## Pullback and coefficient postcomposition

For a Lie-algebra map `φ : L' →ₗ⁅K⁆ L` and a linear coefficient map
`ψ : M →ₗ[K] N`, the constructed linear map is

```
pullMap φ ψ q : Cochains K L M q →ₗ[K] Cochains K L' N q
```

Its value on a cochain is
`ψ.compAlternatingMap (f.compLinearMap φ.toLinearMap)`. Thus it uses
Mathlib's actual alternating-map precomposition and linear postcomposition;
linearity in `f` is proved by evaluation. `pullMap_apply` gives the exact
formula

```
pullMap φ ψ q f x = ψ (f (fun i => φ (x i))).
```

`pullMap_id` identifies simultaneous identity maps with the identity linear
map on cochains. `pullMap_comp` proves

```
pullMap (φ.comp φ') (ψ'.comp ψ) q =
  (pullMap φ' ψ' q).comp (pullMap φ ψ q).
```

In particular the Lie-algebra arguments vary contravariantly and coefficient
values covariantly. Both laws follow by linear-map extensionality,
alternating-map extensionality and definitional evaluation; they are proved
for every natural degree, including degree zero.

`pullMap_id_eq_map` identifies `pullMap` at the identity Lie-algebra map with
the existing coefficient operation `map ψ q`, when `ψ` is a Lie-module map
for the same Lie algebra. This theorem only needs the Lie-ring-module
structures needed to state that coefficient map.

## Compatibility with the actual differential

`omitNth_lieHom` states that the published increasing tuple deletion commutes
with applying `φ`. This is definitional. `bracketFirst_lieHom` similarly
states that bracket-first insertion commutes with applying `φ`. Its proof
separates the first tuple entry, where it uses `φ.map_lie`, from every
successor entry, where it is definitional. These tuple identities hold at all
their typed indices; the latter does not require an ordering hypothesis on
its two indices.

Suppose the genuine coefficient actions satisfy

```
hψ : ∀ x m, ψ ⁅φ x, m⁆ = ⁅x, ψ m⁆.
```

This is the compatibility of a linear map with the given Lie actions along
`φ`; it is not an assumed compatibility with a cochain differential.
`pullMap_differential` proves, for every `q` and every cochain `f`,

```
pullMap φ ψ (q+1) (differential q f) =
  differential q (pullMap φ ψ q f).
```

The proof evaluates alternating maps. In degree zero it uses
`differential_apply_zero`, `hψ` and uniqueness of the empty tuple. In positive
degree it uses `differential_apply_succ`, moves `ψ` through finite sums and
integer scalar multiples, and applies the two tuple identities and `hψ`.
Every occurrence of `differential` is the published action-plus-bracket
operator; no alternate or supplied differential is introduced.

## Full-group-equivariant differential

Let `σ : Representation K G L` and `ρ : Representation K G M` be actual
representations of a group `G`. The required compatibilities are

```
hσ : ∀ g x y, σ g ⁅x,y⁆ = ⁅σ g x, σ g y⁆
hρ : ∀ g x m, ρ g ⁅x,m⁆ = ⁅σ g x, ρ g m⁆.
```

Thus `σ` preserves the bracket, and the coefficient representation is
covariant with the Lie action. The imported submodule
`Langlands.HorizontalAlternating.equivariant σ ρ q` consists exactly of
alternating cochains satisfying

```
f (fun i => σ g (x i)) = ρ g (f x)
```

for **every** `g : G` and tuple `x`. `differential_mem_equivariant` proves
that the actual degree-`q` differential carries this submodule into its
degree-`q+1` counterpart. The proof fixes an arbitrary group element. In
degree zero it uses the equivariance of the empty tuple and `hρ`. In
positive degree it expands the two differential sums. The action terms
follow from equivariance on deleted tuples and `hρ`. For the bracket terms,
`hσ` bundles `σ g` as a Lie-algebra map; `bracketFirst_lieHom` and cochain
equivariance identify every summand.

`equivariantDifferential σ ρ hσ hρ q` is the actual `K`-linear map between
these two submodule types. Its underlying value is `differential q f.val`;
its membership proof is the preceding theorem, and its linearity follows
from the linearity of the existing differential. The theorems
`equivariantDifferential_val` and `equivariantDifferential_apply` record the
underlying alternating-map equality and its evaluation at every tuple.
No restriction to an identity component or to infinitesimal invariance is
made.

## Internal provenance and remaining work

This is an internal construction from the published `CoefficientCochains`
and `HorizontalAlternating` modules. The alternating-map compositions come
from `Mathlib.LinearAlgebra.Alternating.Basic`; the imported coefficient
module supplies the actual differential and its zero- and positive-degree
formulas. Mathlib is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`. The functor laws and full-group
stability are derived directly in Lean from these constructions. No new
external-source identification is asserted.

This module does not prove square-zero, define cycles, boundaries or
cohomology, or restrict the differential to horizontal cochains or the
horizontal-equivariant intersection. Preservation of that intersection
requires the additional relation between the group action and its compact
Lie action; covariance alone is not asserted to supply it. Analytic
compact differentiation and actual automorphic coefficient attachment also
remain separate construction obligations.

Authorship: Worker 2.
