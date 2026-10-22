# Integral Tate groups from actual torsion fibres

This module constructs the full and prime-to-`p` integral Tate groups of an actual commutative group scheme `G : Grp (Over S)`, evaluated on a test scheme `T : Over S`. It assumes only `IsCommMonObj G.X`. Its levels come from the actual multiplication morphism and the published scheme kernel. No family of abstract groups or transition maps is supplied as input.

All declarations are in `Langlands.GroupScheme.Tate`. This is the reusable group-scheme construction. The [bundled abelian-scheme interface](AbelianScheme.md) specializes it to the project's abelian schemes.

## Original sources and provenance

The sources were read directly at these locations:

- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), Chapter I, printed p.18, PDF p.26. Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. This page defines the full Tate module as the inverse limit of `A[N](kᵃᶜ)` over positive integers, and the away-from-a-finite-set version by restricting the integers to those coprime to that set. `Away` implements the singleton-prime case when `p` is prime; its formula is meaningful for any natural `p`.
- B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built 2012-02-08, Chapter X (10.1)–(10.5), printed pp.141–143, PDF pp.145–147. Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The end of (10.1) gives multiplication-by-ℓ transitions on ℓ-power torsion, (10.2) describes compatible sequences with coordinatewise addition, and (10.5) gives the induced coordinatewise map for a homomorphism.

No source-specific errata file was present in the available Library. The general transition `[M/N]` for `N ∣ M`, its laws, the universal lifts, the topology, and extension to arbitrary commutative group schemes and test schemes are internal constructions. They are not attributed to a displayed general-divisibility formula in either source. The sources' statements on ranks, finite étaleness, scalar actions, Galois actions, isogenies, rationalization, and exact sequences are not formalized by this module.

## Actual torsion levels

`levelGroup G T n` is the kernel subgroup of the homomorphism on `T`-points induced by the already published `multiplication G (n : ℤ)`. `mem_levelGroup` rewrites its membership condition as `x ^ n = 1`. This follows from `points_multiplication` and the equality between natural and integer powers at a nonnegative exponent.

`Level G T n` uses additive notation for this subgroup; it has an abelian-group structure. `toSection` is its injective additive homomorphism to `Additive (T ⟶ G.X)`. The ambient Mathlib group-object notation is multiplicative, so powers in the implementation are multiplication by natural numbers in the usual additive notation for group schemes.

`kernelLevelEquiv` is the additive equivalence from

```text
Additive (T ⟶ (kernel (multiplication G n)).X)
```

to `Level G T n`. It is precisely the additive conversion of the imported `kernelPointsEquiv`; no scheme kernel is reconstructed. Its forward map composes with the actual kernel inclusion. Its inverse uses the published kernel pullback's universal lift.

`fibreLevelEquiv G s n` additionally identifies the points of the actual scheme fibre with `Level G (Over.mk s) n`. For any `s : U ⟶ S`, its source is

```text
Over.mk (𝟙 U) ⟶ (Over.pullback s).obj (kernel (multiplication G n)).X.
```

Thus its source consists of sections over `U` of the fibre product of the torsion scheme with `U`. The construction uses the map/pullback adjunction on over categories, identifies the composite of the identity with `s` with `s`, and then applies `kernelLevelEquiv`. When `U = Spec Ω`, these are the Ω-valued points of the actual torsion fibre.

`FullAt G s` and `AwayAt G s p` specialize the limits below to a field-valued point `s : Spec Ω ⟶ S`. The implementation works for every field Ω. Taking Ω algebraically closed gives the geometric-point convention of the full Tate module in Harris–Taylor; algebraic closedness is not needed to construct the groups themselves.

## Divisibility transitions and inverse limits

For `h : n ∣ m`, `transition G T h` sends the underlying section `x` to `x ^ (m / n)`. It lands in the `n`-torsion subgroup because `(x ^ (m/n)) ^ n = x ^ m = 1`; the divisibility hypothesis gives `(m/n) * n = m`. Commutativity makes this a homomorphism. By `points_multiplication`, this is the map induced on the underlying sections by `[m/n]`.

`transition_self` proves the identity law at a positive level. `transition_comp` proves that transitions for `n ∣ m ∣ k` compose to the transition for `n ∣ k`, using the natural-number identity `(k/m) * (m/n) = k/n`. The latter law actually holds without positivity; positivity is imposed on every index of the inverse limit.

For a predicate `P : ℕ → Prop`, `Index P` consists of positive integers satisfying `P`. `coherent G T P` is the additive subgroup of the product of the levels consisting of families `x` with

```text
transition G T h (x m) = x n
```

for every pair of indices and every divisibility witness `h : n.val ∣ m.val`. `Integral G T P` is this subgroup as a type. Addition and negation are coordinatewise; closure follows from the transition homomorphisms. `Full` takes `P n = True`, while `Away p` takes `P n = Nat.Coprime n p`.

`evaluation` gives the coordinate homomorphisms and `evaluation_transition` their compatibility. `lift` constructs a homomorphism into the limit from any compatible family of homomorphisms from an additive group. `evaluation_lift` and `lift_unique` establish its projection and uniqueness laws. These exhibit the inverse-limit universal property directly through coherent families, without requiring a chosen categorical limit object. `restrictAway` restricts the full family to the coprime indices.

## Topology and functoriality

Each `Level` is given the discrete topology. `Integral` has the subtype topology inherited from the product of those discrete levels, and an `IsTopologicalAddGroup` instance. `continuous_evaluation` follows from continuity of a product projection and the subtype inclusion. `continuous_lift` states that the universal lift is continuous when every coordinate map is continuous. In particular, `continuous_restrictAway` proves continuity of restriction.

No level is asserted to be finite. No compactness or profiniteness conclusion is made: such a result requires a separate finiteness hypothesis or a geometric theorem establishing finiteness of the relevant points. This matters for the general commutative group schemes and test schemes allowed here.

For an actual group-scheme homomorphism `f : G ⟶ H`, `levelMap T f n` composes the underlying section with `f`. Preservation of powers proves torsion membership; preservation of multiplication proves additivity. `levelMap_transition` proves compatibility with transitions. `map T P f` is the resulting homomorphism of integral Tate groups. `evaluation_map` records its coordinate formula.

`map_id` and `map_comp` prove identity and composition by extensionality and categorical composition of sections. `map_mul` proves additivity in the group-scheme homomorphism: the pointwise multiplication `f * g` in Mathlib's group-object notation induces the sum of Tate homomorphisms. Its proof is the compatibility of precomposition with pointwise multiplication. `continuous_map` follows coordinatewise from discreteness of the source level and continuity of evaluation. These laws apply simultaneously to the full and prime-to-`p` groups by their predicate specializations.
