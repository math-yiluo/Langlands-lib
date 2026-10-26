# Coefficient-valued Chevalley–Eilenberg cochains

This module constructs the coefficient-valued Chevalley–Eilenberg cochains and
their linear coboundary operator. All declarations are in
`Langlands.Cohomology.Lie`. Let `K` be a characteristic-zero field, `L` a Lie
algebra over `K`, and `M` an arbitrary Lie module over `L`. Neither `L` nor `M`
has a finite-dimensionality hypothesis. In particular the construction supports
complex coefficients and infinite-dimensional representation spaces.

## Original source and conventions

The source is Henri Cartan and Samuel Eilenberg, *Homological Algebra*
(Princeton University Press, 1956), Chapter XIII §8, printed p.282, PDF page304,
the alternating coefficient cochain description and the displayed coboundary
formula. The retained file is
`literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`,
source ID
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`,
content SHA256
`1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`.
Worker 210 independently read the rendered original pp.279–282 (PDF301–304),
including §7 Theorem7.1 and the §8 formula, and verified this fingerprint.
No source-specific errata note is present in the current Library.

The source uses one-based indices, with action sign `(-1)^(i+1)` and
bracket-first sign `(-1)^(i+j)`. Replacing a source index by the Lean index
plus one changes the action exponent into `i+2`, which has the parity of `i`;
it changes the bracket exponent by two, preserving its parity. Thus for
zero-based indices the intended operator is

$$
(df)(x_0,\ldots,x_q)=
\sum_{i=0}^q(-1)^i\,[x_i,f(x_0,\ldots,\widehat{x_i},\ldots,x_q)]
+\sum_{0\leq a<b\leq q}(-1)^{a+b}
f([x_a,x_b],x_0,\ldots,\widehat{x_a},\ldots,\widehat{x_b},\ldots,x_q).
$$

Here `[x,m]` denotes the given left coefficient action. The remaining tuple
entries retain their original order, and the Lie bracket is inserted first.
The source's §7 works over a ring with a free underlying Lie-algebra module
and proves an exterior resolution comparison. This module restricts scalars
to a field and constructs the cochains and operator only; it makes no Ext
identification or resolution-comparison claim.

## Cochains and finite indices

`Cochains K L M q` is exactly Mathlib's alternating multilinear map type
`L [⋀^Fin q]→ₗ[K] M`. `omitNth i x` is the increasing complement of index `i`,
implemented by `fun k => x (i.succAbove k)`. All indices and bounds are
provided by `Fin`, with no out-of-range convention. `omitNth_zero` and
`omitNth_one_pair` identify the tuples used in the low-degree calculations.

For positive cochain degree `q = n+1`, `bracketFirst i j x` is

```
Matrix.vecCons ⁅x i.castSucc, x j.succ⁆
  (omitNth j (omitNth i.castSucc x))
```

where `i,j : Fin (n+1)`. In the evaluation theorem `j` ranges over
`Finset.Ici i`, so `i ≤ j`. `bracketFirst_indices` proves the required strict
inequality `i.castSucc < j.succ`. After deleting the first index, the original
index `j.succ` occupies position `j`, which explains the second deletion.
This triangular indexing enumerates the increasing pairs `(a,b)` exactly
once, by `(a,b)=(i,j+1)`; conversely use `(i,j)=(a,b-1)`. Its sign exponent
`i+j+1` is precisely `a+b`.

## Constructed operator and its evaluation

`actionSeed f` sends `x` to the alternating map `z ↦ ⁅x,f z⁆`, by linear
postcomposition with `LieModule.toEnd`. Its additivity and scalar compatibility
in both `x` and `f` are proved in the module. `actionPart q` is its alternating
uncurrying using `AlternatingMap.alternatizeUncurryFin`.
`actionPart_apply` proves the full action sum in the displayed formula.

For a positive-degree cochain, `bracketSeed f` is the bilinear map
`(x,y) ↦ f.curryLeft ⁅x,y⁆`. Its values are alternating multilinear maps in
the remaining arguments. `bracketSeed_apply`, `bracketSeed_add` and
`bracketSeed_smul` establish its concrete evaluation and linear dependence on
`f`. `bracketPart 0` is zero. In positive degree `bracketPart` is minus
one-half of the double alternating uncurrying of this seed.

Mathlib proves multilinearity and alternation of alternating uncurrying.
Consequently both constructed terms have the actual alternating-map type;
these properties are not supplied as hypotheses on a proposed formula.
Their definitions also prove linearity in the input cochain, yielding

```
differential q : Cochains K L M q →ₗ[K] Cochains K L M (q+1)
```

as `actionPart q + bracketPart q`. There is no supplied differential parameter.

`bracketPart_apply` proves the bracket sum. Its proof uses Mathlib's
`alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`, which groups the
double uncurrying into increasing pairs and subtracts the swapped seed.
Lie skew-symmetry and linearity of the curried cochain turn this subtraction
into twice the forward seed. The private lemma `half_double` cancels the
factor two; the outer minus shifts the exponent to `i+j+1`.
`differential_apply_succ` adds this identity to `actionPart_apply`, proving
the displayed coboundary formula in every positive degree.

The seed and operator definitions themselves need only a field. The
positive-degree evaluation theorems and the degree-one formula additionally
use `CharZero K`, which ensures that two is invertible. The characteristic-zero
setting stated above satisfies all these hypotheses.

## Low degrees and coefficient maps

`ofCoefficient m` is the degree-zero constant cochain with value `m`, and
`ofCoefficient_apply` records this evaluation.
`differential_apply_zero` computes the operator on every zero cochain using
the unique empty tuple. `differential_ofCoefficient` specializes it to

$$
d(m)(x)=[x,m].
$$

`differential_one` expands the two action terms and the single bracket term:

$$
d(f)(x,y)=[x,f(y)]-[y,f(x)]-f([x,y]).
$$

For a Lie module map `φ : M →ₗ⁅K,L⁆ N`, `map φ q` is the direct linear
postcomposition of alternating cochains by `φ.toLinearMap`. `map_apply`
identifies its value as `φ (f x)`. `map_differential` proves

```
map φ (q+1) (differential q f) = differential q (map φ q f)
```

by evaluating cochains, separating degree zero from positive degree, and
commuting `φ` through the finite sums, integer scalar multiples, and the Lie
action using its equivariance. The coefficient map, finite-index packaging,
and this naturality proof are internal constructions derived from the
source formula; they are not additional assertions attributed to the book.

This unit does not assert square-zero, form cohomology, or construct a
relative restriction. Those require subsequent results.

Authorship: Worker 210.
