# Prescribed character values along a simple relative root

`Langlands.GroupScheme.exists_simpleRootValueCharacter` constructs an additive
homomorphism from the character lattice of a split base-changed torus to
`Additive Kˣ`, with prescribed value on one simple relative-root fiber and zero
values on the other simple relative-root and double-root fibers.

## Setting and conclusion

Let `K/k` be a finite Galois extension, `f : S → T` a map of commutative group
schemes, and `j : T → G` a maximal torus that represents the centralizer of the
maximal split torus `f ≫ j`. The theorem assumes the indicated affineness and
local finite type instances for `G` and `T`, that `j` is a closed subgroup,
and that `T_K` is split. Let `P` be a finite reduced root datum of `j_K` on the
actual character and cocharacter lattices of `T_K`, with root lattice equal to
the whole character lattice. Let `ν` be generic for `f ≫ j`, let `a` be simple
relative to `ν`, and choose an actual root `β` restricting to `a`.

For any unit `c : Kˣ` whose underlying element belongs to the stabilizer field
`rootOrbitField k K j β`, the theorem supplies
`φ : characterLattice T_K →+ Additive Kˣ`. Its values are Galois-equivariant
after coercion to `K`, and `φ β.val = Additive.ofMul c`. For every other simple
relative root `d ≠ a` and every actual root `γ` restricting either to `d` or to
`2 • d`, it satisfies `φ γ.val = 0`. In multiplicative notation this last
condition is character value `1`. The theorem constructs character values;
descent to an actual rational torus point is a separate step.

## Implemented proof

1. Restriction is transported from `X*(T_K)` to `X*(S)` using the inverse of
   split-torus character base change. The private `restrictCharacter` lemmas
   identify its base change, its pairing with cocharacters, and its invariance
   under Galois action. The torus centralizer hypothesis makes the restriction
   of each absolute root nonzero; the splitting-field restriction criterion
   then makes it a relative root.
2. Genericity of `ν` makes the base change of `ν ≫ f` regular for `P`.
   The associated absolute base `B` consists of the positive indecomposable
   roots. Any absolute root restricting to a simple relative root lies in
   `B`: a positive decomposition would restrict to a decomposition of that
   relative root into positive relative roots. Linear independence of `B`
   and the full-root-lattice assumption give an integral basis `e` of
   `X*(T_K)`. The public lemma
   `RootPairing.Base.simpleRootValue_repr_nonneg` proves that a positive
   root has nonnegative coordinates in any integral basis identified with
   `B`, by induction on positive-root addition.
3. The private `multipleSimpleRootFiber_coordinate_zero` proves a stronger
   coordinate vanishing fact used for both `d` and `2 • d`. If `t` restricts
   to `m • d` with `m > 0` and simple `d ≠ a`, its coordinate at every
   `s ∈ B` restricting to `a` is zero. Choose an absolute root above `d`.
   Its Galois conjugates are basis roots with zero `s`-coordinate.
   The maximal split subtorus orbit-sum theorem identifies the orbit sum of
   `t` with `m` times that chosen root's orbit sum. On taking the
   `s`-coordinate, the left side is a sum of nonnegative integers and
   the right side is zero. The identity conjugate's coordinate must vanish.
4. `exists_rootOrbitValue` supplies a Galois-equivariant function `ψ` on the
   actual roots with value `c` at `β` and value `1` off its orbit.
   Extend `s ↦ Additive.ofMul (ψ s)` linearly along `e` to obtain `φ`.
   The descended regular-cocharacter simple-root action permutes `B`, so
   equivariance on the basis proves equivariance on the whole lattice.
   The root `β` is in `B`, hence its prescribed value is preserved.
5. Expand another root `γ` above `d` or `2 • d` in `e`. For a basis root
   above `a`, its coefficient vanishes by step 3. For any other basis root,
   its value under `ψ` is `1`, since the Galois orbit of `β` stays in
   the fiber of `a`. Each summand of the additive extension is therefore
   zero, proving the required value at `γ`.

## Provenance

This module is a derived helper for
`QuasiSplitAdjointSimpleRootTransitivityStatement`. Its direct inputs are the
Library's root-fiber restriction and Galois-orbit results, character orbit-sum
comparison for maximal split subtori, and the regular-cocharacter base and
Galois-action constructions. The unit-valued orbit function is proved in the
companion module `RootOrbitUnitValue`. The coordinate argument here uses
integral absolute simple-root coordinates and Galois orbit sums; it requires
no relative simple-root basis or unproved relative-root-system statement.
