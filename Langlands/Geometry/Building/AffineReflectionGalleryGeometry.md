# Wall-reflection generation and galleries for locally finite arrangements

This module proves the published
`Langlands.Geometry.Building.AffineReflectionGalleryGeometryStatement` as the
theorem `Langlands.Geometry.Building.affineReflectionGalleryGeometry`, at the
statement's universe levels `uV, uA`. The module imports the unchanged
statement module, `AffineChamberAction` and `Mathlib.Topology.Instances.Real.Lemmas`. It uses the five
premises of `IsLocallyFiniteReflectionArrangement` as stated and adds no other
hypotheses. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

The module reuses `IsCoroot.map` and `conjugate_affineReflection` from
`AffineChamberAction` for transport of coroots and reflections. Its remaining
helpers live in `Langlands.Geometry.Building.AffineRootSystem.GalleryGeometry`.
The module defines two auxiliary notions:

- `IsRegular Ψ x` means `∀ ψ ∈ Ψ, ψ x ≠ 0`. This is exactly the regularity
  hypothesis in the target statement.
- `separatingRoots Ψ x y` is the set of `η ∈ Ψ` with `η x * η y < 0`.

## Implemented route

### Real arithmetic

The lemmas `sign_add_eq_of_abs_lt`, `mul_neg_of_sign_eq`, `mul_pos_of_sign_eq`
and `sign_eq_of_not_mul_neg` relate `SignType.sign` to the sign of products of
reals. The function `t ↦ a + t (b - a)` describes a root restricted to a
segment. For it, `crossTime_mem` shows that its zero `a / (a - b)` lies in
`(0, 1)` when `a * b < 0`. Next, `crossing_lt` and `crossing_eq` show that a
sign change at or before a time `T ∈ (0, 1)` forces `a * b < 0` and puts the
crossing time at or before `T`. Finally, `cross_mul_eq` turns equal crossing
times into the vanishing of the cross term `p * b - a * q`.

### Affine functionals, coroots and reflections

`apply_smul_vadd` evaluates an affine functional on `c • u +ᵥ p`. If the
linear part vanishes, the functional is constant
(`apply_eq_of_linear_eq_zero`, `eq_zero_of_linear_eq_zero`). If it does not
vanish, the functional is nonzero somewhere (`exists_apply_ne_zero`).

`isCoroot_unique` shows that coroots are unique. The proof applies Mathlib's
`Module.Dual.eq_of_preReflection_mapsTo` to the finite spanning set
`derivativeRoots Ψ`, using the two arrangement fields for finiteness and
spanning. Then `affineReflection_eq_of_eq_smul` follows: proportional roots
define the same `affineReflection`, because `c⁻¹ • v` is a coroot of `c • ψ`
and coroots are unique. Conversely, `exists_eq_smul_of_affineReflection_eq`
evaluates `e p -ᵥ p` and shows that equal reflections come from proportional
roots. `IsCoroot.map` and `conjugate_affineReflection` move a root, its
coroot and its reflection along a root-preserving affine automorphism.

### Separation and walls

`reflectionSeparates` is invariant in two ways. It depends only on the facets
of its two points (`reflectionSeparates_of_facetRel`). It is also carried
along by conjugation with an element of `rootStabilizer Ψ`
(`reflectionSeparates_conj`). The same two invariances therefore hold for
`wallReflections`: see `mem_wallReflections_of_facetRel` and
`conj_mem_wallReflections`. Wall reflections are coroot reflections, so the
subgroup they generate lies inside `affineWeylGroup Ψ`
(`closure_wallReflections_le`), and hence inside the root stabilizer.

The core criterion is `mem_wallReflections_of_sign_eq`. Its hypotheses are:

- `x` is regular,
- `ψ ∈ Ψ` has coroot `v`,
- `ψ z = 0`,
- every root not proportional to `ψ` has the same sign at `x` and at `z`.

Under these hypotheses `affineReflection ψ hv.1 ∈ wallReflections Ψ x`.
Separation of `x` from its image holds because `ψ (s x) = -ψ x`. For
uniqueness, take any reflection `t = s_η` that separates `x` from `s x`.
Suppose `η` is not proportional to `ψ`. The root `η - η.linear v • ψ` is again
in `Ψ`, it is not proportional to `ψ`, its value at `x` is `η (s x)`, and its
value at `z` is `η z`. The sign hypothesis then forces `η x` and `η (s x)` to
have the same sign, which contradicts separation. So `η` is proportional to
`ψ`, and `affineReflection_eq_of_eq_smul` gives `t = s`.

### Finiteness and generic perturbation

`finite_separatingRoots` shows that `separatingRoots Ψ x y` is finite. It
applies `finite_bounded_at` at `x` with the bound
`a ↦ |a (y -ᵥ x)|`: a separating root satisfies `|η x| ≤ |η y - η x|`.

`eventually_sign_smul_vadd` fixes a point `p` and a direction `u`. It shows
that for every small enough `ε`, every root nonzero at `p` keeps its sign at
`ε • u +ᵥ p`. Roots with `|η p| ≤ |η.linear u|` form a finite set by
`finite_bounded_at`, and the claim holds for each of them eventually. For the
other roots it holds whenever `|ε| < 1`.

`exists_facetRel_forall_ne_zero` moves a regular point `y` inside its facet
(`facetRel`) off the zero sets of a finite family of affine functionals, each
with nonzero linear part. The proof is induction on a `Finset`. At each step,
if the new functional vanishes, the point is pushed a small positive amount
along a direction on which that functional's linear part is nonzero. The
eventual sign statements keep both the facet and the functionals already
handled.

### A separating wall exists (`exists_wall`)

Let `x` and `y` be regular with a nonempty finite set `R` of separating roots.
First move `y` within its facet to a point `y'`. The point `y'` avoids every
functional `ψ x • η - η x • ψ` with `ψ, η ∈ R` not proportional. Each of these
has nonzero linear part. Otherwise it would be constant, and since it vanishes
at `x` it would be zero, which would make `η` a multiple of `ψ`. Take a root
`ψ ∈ R` with the smallest crossing time `t = ψ x / (ψ x - ψ y')` on the
segment `s ↦ s • (y' -ᵥ x) +ᵥ x`. Let `z` be the point at time `t`, so
`ψ z = 0`. Now take a root `η` not proportional to `ψ`:

- `η z = 0` is impossible. It would make `η` separating with the same crossing
  time as `ψ`, so `y'` would lie on one of the avoided cross functionals.
- A sign change of `η` before time `t` is impossible, by minimality of `t`.

So `η` has the same sign at `x` and `z`, and the core criterion makes the
reflection of `ψ` a wall reflection at `x`.

### Galleries (`separatingRoots_ssubset`, `exists_facetRel`)

Let `s` be a wall reflection at `x` coming from a root `ψ` that separates `x`
from `y`. `separatingRoots_ssubset` shows that `separatingRoots Ψ (s x) y` is
a proper subset of `separatingRoots Ψ x y`. Suppose a root `η` separates `s x`
from `y` but not `x` from `y`. Then `η` separates `x` from `s x`, so wall
uniqueness gives `s_η = s`. Then `η = c • ψ`, which contradicts the sign
pattern. Moreover, `ψ` itself no longer separates `s x` from `y`.

`exists_facetRel` takes regular `x` and `y`. It finds
`w ∈ Subgroup.closure (wallReflections Ψ x)` with `facetRel Ψ (w x) y`, by
strong induction on `(separatingRoots Ψ (w x) y).ncard`. If the set is
nonempty, `exists_wall` gives a wall reflection `s` at `w x`. Its conjugate
`w⁻¹ s w` is a wall reflection at `x`, so `s * w` stays in the generated
subgroup and the count drops. If the set is empty, `w x` and `y` have the
same signs on every root.

### Generation (`affineReflection_mem_closure`)

Fix `ψ ∈ Ψ` with coroot `v`, and write `s` for its reflection. Write
`g η = η - (η.linear v / 2) • ψ`. Move `x` within its facet to a point `x'`.
The point `x'` avoids `g η` for every `η` separating `x` from `s x` whose
`g η` has nonzero linear part. Let `m = (-(ψ x') / 2) • v +ᵥ x'`. Then
`η m = g η x'` for every `η`, and `ψ m = 0`.

Every root not proportional to `ψ` is nonzero at `m`. If `g η` has zero linear
part, then `η m = 0` would give `η = (η.linear v / 2) • ψ`. Otherwise
`η m = 0` would make `η` separate `x'` from `s x'`. Hence `η` separates `x`
from `s x`, and `x'` would lie on the zero set of `g η`, which it avoids.

Next choose `δ > 0` from `eventually_sign_smul_vadd` at `m` in direction `v`.
The point `δ • v +ᵥ m` is regular:

- multiples of `ψ` take the value `c * (2 δ)` there, which is nonzero;
- every other root keeps its nonzero sign from `m`.

The core criterion, applied with `z = m`, makes `s` a wall reflection at
`δ • v +ᵥ m`. By `exists_facetRel`, some `w` in the subgroup generated by the
walls of `x` has `w x` in the same facet as `δ • v +ᵥ m`. So `s` is a wall
reflection at `w x`, its conjugate `w⁻¹ s w` is a wall reflection at `x`, and
`s = w (w⁻¹ s w) w⁻¹` lies in the generated subgroup.

### Final theorem

`affineReflectionGalleryGeometry` introduces the statement's data. It proves
the subgroup equality by `le_antisymm`, using `closure_wallReflections_le` in
one direction and `affineReflection_mem_closure` on the generators of
`affineWeylGroup Ψ` in the other. The chamber-transport conjunct is
`exists_facetRel`, packaged as an element of the subtype
`Subgroup.closure (wallReflections Ψ x)`.

## Provenance

The proof is internal. Its strategy is the classical chamber and gallery
argument for real reflection arrangements: a first wall met on a segment,
induction on the number of separating hyperplanes, and conjugation of
reflections along galleries. This is the geometry behind Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Remark 1.3.16 and Lemma 1.3.17.
The exact source identifier and hash are recorded in the unchanged
statement's Markdown. The Lean proof does not follow that source line by line,
and it adopts no external Lean implementation. Coroot uniqueness uses
Mathlib's `Module.Dual.eq_of_preReflection_mapsTo`.
