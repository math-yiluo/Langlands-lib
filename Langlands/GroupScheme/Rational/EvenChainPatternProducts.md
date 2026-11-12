# Pattern products for even path components

Provenance: derived. This module translates Steinberg's modified products
`N''` and `N'''` to rational points with several components handled together.
The Lean interface is from Worker 175's shared draft for Task 5324
(`dae9b3ff-3319-4226-a421-ef1462af985a`); Worker 162 checked the originals
and completed this documentation. It asserts no existence or product property.

## Setting and supplied data

There is one arbitrary universe `u`. The field `k : Type u` may be finite
or imperfect and have any characteristic. The actual group scheme `G`
over `Spec k` has affine structure morphism, and `p : SplitPinning G` is
supplied. That published structure includes connected reductivity, an actual
split maximal torus, a finite reduced root datum and a pinning. No simple
connectedness is assumed. Rational
points are `rationalPoints G = (Over.mk (𝟙 (Spec k)) ⟶ G.X)` with their
actual group law.

`SplitPinning.middleDistance m i` is `m - 1 - i` if `i + 1 < m`, and `i - m`
otherwise, with natural subtraction. For `m > 0` and `i < 2*m` it gives
distance from the middle pair `{m-1,m}`; both middle positions have distance
zero. It is also defined outside these bounds.

`SplitPinning.corootRationalPoint p α t` evaluates the actual coroot
cocharacter `p.corootHom α` at `t : kˣ`, using the inverse of
`Gm.affinePointsEquiv` at the identity base map and then the coroot morphism.

`SplitPinning.EvenChainData p J`, for `J : Type u`, supplies:

- `half c : ℕ` and `path c : Fin (2 * half c) → p.base.support`;
- `isPathComponent c : RootDatumPathWeights.IsPathComponent (path c)`,
  imposing positive length, the type `A` Cartan pairing matrix, and
  orthogonality to every simple root off the path. Thus `half c > 0`
  and the path is an injective listing of a whole type `A_(2 * half c)`
  component;
- `disjoint`: equality of vertices on paths `c` and `c'` implies `c=c'`;
- `modified c : p.SteinbergModifiedData`, from the published
  `Rational/SteinbergModifiedRootProduct`. Its distinct simple roots `a,b`
  are fixed by `modified_a`, `modified_b` to zero-based positions
  `half c - 1`, `half c`. It supplies the root `α=a+b`, a whole-root
  parametrization `xAlpha`, an actual reflection representative `nAlpha`,
  and nonzero scalars `ca,cb : k`;
- `nAlpha_mem`: `nAlpha.point` lies in the supremum of the two subgroups of
  rational points of the actual root subgroups of `α` and `-α`. This is
  generation in the rational-point group, not only after field extension.

The structure takes no `Fintype J` instance. Finite products use explicit
`Fin` equivalences; the statements also quantify over `Fintype J`.
Empty `J` is permitted, and not every even component need be selected.

## Ordering and products

The following names are in `SplitPinning.EvenChainData`.
`Rest C` is the subtype of simple roots different from both middle vertices
of every selected path, including all other vertices and all simple roots
on unselected components.

For `e : Fin q ≃ C.Rest`, `IsMiddleOut C e` requires vertices of strictly
smaller `middleDistance` on each selected path to occur earlier. Vertices
at equal distance may occur in either order. No ordering between components
or condition on unselected components is imposed.

For `x : p.NormalizedSimpleRootParametrizations`, path `c`, Boolean `b`,
`s : k` and `t : kˣ`, `block C x c b s t` is:

| Pattern | Block in `rationalPoints G` |
| --- | --- |
| `false` | `x_α(s) n_α` |
| `true` | `u_b u_a x_α(s) n_α α^∨(t)` |

Here `u_a=x_a(ca)` and `u_b=x_b(cb)` are the published
`SteinbergModifiedData.ua`, `.ub`. The coroot factor is
`corootRationalPoint p α t`. The unit is unused for `false`.
No simple-reflection family is an argument of `block`.

For `n : p.SimpleReflectionRepresentatives`, `o : Fin r ≃ J`,
`e : Fin q ≃ C.Rest`, `ε : J → Bool`, `s : J → k`, `t : J → kˣ` and
`d : Fin q → k`, `patternProduct C x n o e ε s t d` takes all blocks along
`o`, then the factors `x_(e j)(d_j) n_(e j)` along `e`. It uses `List.ofFn`
and `List.prod` in increasing `Fin` order. Empty products are identities;
no commutation or middle-out assumption is imposed by the definition.
`patternSet C x n o e` existentially quantifies all four coordinate
families and takes the resulting image set. It asserts no unique coordinates.

## Sources and derived provenance

Robert Steinberg, *Regular elements of semi-simple algebraic groups*,
Publ. Math. IHÉS 25 (1965), 49–80, source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
PDF page numbers are printed page numbers minus 47.

The notation before 9.11 and Theorem 9.11, printed p.74 (PDF p.27), give
`N'' = X_α σ_α ∏_(j ≠ m,m+1) X_j σ_j` and
`N''' = u_(m+1) u_m X_α σ_α T_α ∏_(j ≠ m,m+1) X_j σ_j`.
The source's middle positions `m,m+1` are zero-based `m-1,m` here.
The order `u_b u_a` and torus placement after `n_α` agree with the source.
Theorem 9.11 permits arbitrary nonidentity root points and takes products
over several components. Lemmas 9.12–9.14, p.75 (PDF p.28), give the
smaller type `A` comparison, product coordinates and conjugacy when those
points change. The normalization in 9.16, p.76 (PDF p.29), serves later
character calculations and is not imposed here. The formulas and strata
in 9.15–9.19, pp.75–77 (PDF pp.28–30), motivate the two patterns;
7.9, p.68 (PDF p.21), is the ordinary cross-section comparison.
The unmodified factors `X_j σ_j` also occur in 1.4, p.50 (PDF p.3).
In 9.2–9.3, p.72 (PDF p.25), the split-case representatives are made
rational by Hilbert's Theorem 90 applied to the cocycle
`γ ↦ σ_i⁻¹ γ(σ_i)` in `G_i ∩ T`; the proof of 9.7(e) on p.77
constructs `σ_α` over `k` in the same way.

This is a derived translation to rational points over arbitrary fields
with supplied split data. These are coordinate image sets of rational points,
not subvarieties over an algebraic closure. The Boolean pattern independently
selects a modified block for each listed component. The coroot image replaces a separately supplied
rank-one torus; comparison with the source's `T_α` remains an obligation
for a cross-section theorem. The several-component product puts all blocks
first and all remaining factors afterwards. `IsMiddleOut` is a derived
interface for Galois orbits ordered by distance from the middle, motivated
by 9.4, pp.72–73 (PDF pp.25–26), and the final paragraph proving 9.7(e)
after 9.19, p.77 (PDF p.30). A path reversal exchanges the two vertices
at the same middle distance. The predicate alone asserts no Galois compatibility.

## Scope

No existence of data or orderings, root-group comparison, immersion,
coordinate uniqueness, regularity, character formula, quotient property,
Galois stability or rational section over a non-split field is asserted.
The associated `EvenChainCrossSectionStatement` and
`EvenChainGaloisDataStatement` modules isolate the pointwise cross-section and
Galois-stability obligations.
