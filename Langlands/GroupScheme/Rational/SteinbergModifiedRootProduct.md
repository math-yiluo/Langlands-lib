# Supplied merged-root data and Steinberg's modified ordered morphisms

This internal construction works over an arbitrary field `k : Type u`, in any characteristic and including finite and imperfect fields. It uses an actual affine group scheme `G` over `Spec k` and a supplied `p : SplitPinning G`. It defines data types and actual morphisms in `Over (Spec k)` for the two ordered products underlying Steinberg's modified sets `N''` and `N'''`, relative to explicitly supplied data. No existence of these data is asserted. The published module `Langlands.GroupScheme.Rational.SteinbergRootProduct` is imported unchanged, and its simple-root data and scalar-coordinate machinery are reused.

## Data for an arbitrary root

`SplitPinning.RootParametrization p α` is indexed by an arbitrary root index `α : p.rootIndex`, not only a simple root. It supplies an actual group-scheme homomorphism `hom` from the standard additive group `VectorGroup.groupScheme (CommRingCat.of k) 1` to `G`, with three fields. These are the same as in the published `NormalizedRootParametrization`:

- `represents`: `hom` represents the whole intrinsic functor `RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)`, meaning equality of subgroup functors on every scheme test.
- `isClosedSubgroup`: `IsClosedSubgroup hom`.
- `torus_equivariant`: the all-test law `t x_α(c) t⁻¹ = x_α(α(t) c)`, using `VectorGroup.charValue` and standard global-function coordinates.

There is no derivative (pinning vector) field, because a pinning only chooses root vectors for simple roots.

`SplitPinning.ReflectionRepresentative p α` supplies a rational point `point`, an actual torus automorphism `torusAut`, the equation `IsNormalizingPoint p.inclusion point torusAut`, and `characterAut torusAut = p.rootDatum.reflection α`. This follows the Library's convention, in which the character action is induced by the inverse torus automorphism. These are the fields of the published `SimpleReflectionRepresentative`, indexed by an arbitrary root.

The adapters `NormalizedRootParametrization.toRootParametrization` and `SimpleReflectionRepresentative.toReflectionRepresentative` forget the derivative normalization or reindex by the root of a simple root. They keep every other field. The published types are not changed.

`RootParametrization.point x T c` evaluates the root map at a global function `c` on a test `T`, as `VectorGroup.scalarPoint` followed by the root map. The module proves the following about it:

- `point_comp`: its precomposition law.
- `mem_rootSubgroup_iff`: a point of the intrinsic root subgroup is exactly a value `x.point T c`.
- `point_zero`: the zero coordinate gives the identity.
- `point_injective`: the map `c ↦ x.point T c` is injective, because `represents` includes that the root map is a monomorphism and additive points are determined by their coordinates.
- `point_eq_one_iff`: `x.point T c = 1 ↔ c = 0`.

`RootParametrization.rationalPoint x c` is the rational point with standard additive coordinate `c ∈ k`, transported to global functions of `Spec k` by `(Scheme.ΓSpecIso _).inv`. `toUnit_comp_rationalPoint` computes its restriction to any test along the structure map. `rationalPoint_ne_one` proves that a nonzero scalar gives a nonidentity point.

## The coroot factor

`SplitPinning.corootHom p α` is `CommGroupScheme.groupHom (p.rootDatum.coroot α) ≫ p.inclusion`. This is the actual cocharacter `p.rootDatum.coroot α : Gm (Spec k) ⟶ p.torus` of the supplied root datum, a morphism of commutative group schemes in `cocharacterLattice`, followed by the torus inclusion. The construction does not use an abstract one-dimensional torus. It does not identify this image with Steinberg's rank-one torus `T_α`.

## Ordered products of simple-root factors

For an arbitrary finite list `f : Fin r → p.base.support` and supplied families `x : p.NormalizedSimpleRootParametrizations` and `n : p.SimpleReflectionRepresentatives`, `simpleRootProductPoint f x n T c` is the product of `x_(f j)(c_j) n_(f j)`. The factors are taken in increasing `Fin r` order, with each rational representative restricted along `toUnit T`. The definition uses `List.ofFn` and the actual point group, so factors need not commute. `steinbergProductPoint_eq` shows that the published `steinbergProductPoint e x n` is this product along the ordering `e`, by definition. `simpleRootProductPoint_comp` gives compatibility with arbitrary precomposition. `simpleRootProductPoint_zero` shows that the empty product is the identity point.

## Supplied modified data

`SplitPinning.SteinbergModifiedData p` bundles:

- distinct simple roots `a b : p.base.support`, with `a_ne_b`;
- a root index `alpha : p.rootIndex` with `root_eq : p.rootDatum.root alpha = p.rootDatum.root a + p.rootDatum.root b`;
- `xAlpha : p.RootParametrization alpha` and `nAlpha : p.ReflectionRepresentative alpha`;
- scalars `ca cb : k`, with `ca_ne_zero` and `cb_ne_zero`.

`D.Complement` is the subtype `{j : p.base.support // j ≠ D.a ∧ j ≠ D.b}`. For a simple-root family `x`, `D.ua x = x_a(c_a)` and `D.ub x = x_b(c_b)` are rational points with standard additive coordinates. `ua_ne_one` and `ub_ne_one` prove that they are not the identity, using the whole-root representation and the nonzero scalars. `toUnit_comp_ua` and `toUnit_comp_ub` compute their restrictions to any test.

## The two morphisms

Fix `D`, an ordering `e : Fin q ≃ D.Complement`, and families `x` and `n`. On a test `T`, with global functions `s` and `d : Fin q → Γ(T.left, ⊤)` and a `Gm` point `t : T ⟶ Gm`:

- `steinbergModifiedProductPoint D e x n T s d` is `x_α(s) n_α * ∏_j (x_(e j)(d_j) n_(e j))`.
- `steinbergModifiedTorusProductPoint D e x n T t s d` is `u_b u_a x_α(s) n_α α^∨(t) * ∏_j (x_(e j)(d_j) n_(e j))`.

Here `α^∨(t)` is `t ≫ (p.corootHom D.alpha).hom.hom`. Every rational point is restricted along `toUnit T`. The products are taken left to right in the displayed order in the actual point group. `steinbergModifiedProductPoint_comp` and `steinbergModifiedTorusProductPoint_comp` prove compatibility with arbitrary precomposition `f : W ⟶ T`. They pull back the global functions by `f.left.appTop`, and the second also pulls back the `Gm` point to `f ≫ t`.

`steinbergModifiedProduct D e x n` is an actual morphism over `Spec k` from standard affine `(q+1)`-space `(VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X` to `G.X`. It evaluates the first formula on that domain, with `s` the coordinate section `0` and `d_j` the coordinate section `j.succ`. `steinbergModifiedTorusProduct D e x n` is an actual morphism over `Spec k` from `(Gm (Spec k)).X ⊗ (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X`, the fiber product over `Spec k`, to `G.X`. It evaluates the second formula at the first projection and at the coordinates of the second projection, in the same way.

The all-test formulas are the following:

- `comp_steinbergModifiedProduct`: for every point `c` of affine `(q+1)`-space, `c ≫ steinbergModifiedProduct` is the first formula, with `s` and `d_j` the standard coordinates `0` and `j.succ` of `c`.
- `lift_comp_steinbergModifiedTorusProduct`: for a `Gm` point `t` and an affine point `c`, `lift t c ≫ steinbergModifiedTorusProduct` is the second formula, with the coroot factor written as `t ≫ groupHom (coroot α) ≫ p.inclusion`.
- `comp_steinbergModifiedTorusProduct`: the second formula at an arbitrary point `g` of the product domain, through its two projections.
- `coordinatesPoint_comp_steinbergModifiedProduct` and `coordinatesPoint_comp_steinbergModifiedTorusProduct`: evaluation at specified global functions `s` and `d`, through the inverse standard coordinate equivalence applied to `Fin.cons s d`.

The proofs push precomposition through each factor and through the ordered list product. They use naturality of the root-map values and `toUnit_unique` for the test structure maps, and identify pulled-back coordinate sections by `VectorGroup.coordinates_apply` and `VectorGroup.coordinates_comp`.

For the empty complement, `q = 0` with `e₀ : Fin 0 ≃ D.Complement`, the complementary product is the identity. `steinbergModifiedProductPoint_zero` and `steinbergModifiedTorusProductPoint_zero` reduce the formulas to `x_α(s) n_α` and `u_b u_a x_α(s) n_α α^∨(t)`. `comp_steinbergModifiedProduct_zero` and `lift_comp_steinbergModifiedTorusProduct_zero` state the same on every test for the scheme morphisms. The products are used only as scheme morphisms, with no group-homomorphism structure.

## Provenance and scope

The source is Robert Steinberg, *Regular elements of semi-simple algebraic groups* (1965), registered as `steinberg-1965-regular-elements-semisimple-groups`. The relevant passages are the type `A_n` (`n = 2m` even) notation before Theorem 9.11, and Theorem 9.11 itself, both on printed p.74 (PDF p.27). Lemmas 9.12–9.14 are on printed p.75 (PDF p.28). There, `N''` is the product `X_α σ_α ∏_(j ≠ m, m+1) (X_j σ_j)` and `N'''` is `u_(m+1) u_m X_α σ_α T_α ∏_(j ≠ m, m+1) (X_j σ_j)`, with `α = α_m + α_(m+1)`. The Lean construction is a derived all-test translation of these ordered expressions over any field and for arbitrary supplied data. It keeps the order of the fixed factors `u_b u_a` and the placement of the torus factor after `n_α`. In the intended type `A_(2m)` application, `a` and `b` are the two middle simple roots, `u_b` plays the role of `u_(m+1)`, and `alpha = a + b`. This module does not impose that application.

Steinberg's `T_α` is the rank-one torus, and his `σ_α` normalizes it in the rank-one group `G_α`. Here the torus factor is the image of the supplied coroot cocharacter, and `nAlpha` is an arbitrary supplied reflection representative. The construction does not include his later normalizations, such as the commutator normalization used in 9.16. The following remain separate obligations:

- comparison of these data with the rank-one subgroup, torus and normalizer choices;
- existence and normalization of compatible data, including root parametrizations for nonsimple roots;
- type-A classification;
- closedness, irreducibility, or the isomorphism-of-varieties statement of Lemma 9.13;
- the conjugacy of Lemma 9.14;
- regularity and the character formulas of 9.15–9.18;
- the stratum isomorphisms of 9.19;
- any invariant-quotient comparison, Galois descent, or rational section.

In particular, no global rational section is claimed for arbitrary quasi-split even-type-A forms. The parent `QuasiSplitSteinbergQuotientStatement` pair, `SteinbergRootProduct`, and every pair they import are unchanged.
