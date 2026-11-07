# Cyclic norm-one elements and division-algebra commutators

The namespace `Langlands.CyclicNorm` gives an explicit weighted-sum
construction for cyclic Hilbert 90 and a precise commutator consequence.
The fields `K : Type uK` and `L : Type uL` have independent arbitrary
universes. The results impose no characteristic restriction.

For an actual automorphism `σ : L ≃ₐ[K] L` and `x : L`, define

`coefficient σ x i = ∏ j < i, σʲ(x)`,

and, writing `n = orderOf σ`,

`weightedTrace σ x z = ∑ i < n, coefficient σ x i * σⁱ(z)`.

These are the actual finite products and finite sum in `L`, rather than
supplied coefficient or solution functions.
The theorem `coefficient_shift` gives
`x * σ(coefficient σ x i) = coefficient σ x (i+1)`.
If `coefficient σ x n = 1`, shifting the finite sum proves

`x * σ(weightedTrace σ x z) = weightedTrace σ x z`.

This is `weightedTrace_relation`. Its proof uses the two expansions of
the sum through index `n`. The term at `n` equals the term at zero,
because `σⁿ = 1` and the full coefficient product is one.

The theorem `exists_weightedTrace_ne_zero` assumes only that `σ` has
finite order, in addition to the field and algebra structures. The
powers of `σ` indexed by `Fin n` are distinct: equality of two such
powers and the bounds below `orderOf σ` force equality of the indices.
Mathlib's linear independence of distinct multiplicative characters,
applied to these automorphisms as functions `L → L`, therefore makes
their weighted sum a nonzero function. Otherwise all its coefficients
would vanish, whereas the coefficient at zero is one. Thus some
`z : L` has `weightedTrace σ x z ≠ 0`.

Now let `L/K` be finite Galois and require explicitly that `σ` generates
the whole automorphism group:

`∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ`.

The theorem `coefficient_order_eq_norm` identifies the full coefficient
product with `algebraMap K L (Algebra.norm K x)`. The proof enumerates all
automorphisms by the distinct powers below `orderOf σ` and applies
Mathlib's product formula for the actual field norm.

If `Algebra.norm K x = 1`, this product is one. Choose an input with
nonzero weighted trace and make that value a unit `y : Lˣ`.
The shifted-sum identity says `x * σ(y) = y`, so

`exists_div_of_norm_eq_one` proves `∃ y : Lˣ, (y : L) / σ(y : L) = x`.

This is cyclic Hilbert 90 for arbitrary independent field universes. The
implemented proof uses the finite weighted sum and character independence
directly, without a group-cohomology computation or a reduction to small
fields. In particular the module does not import or invoke Mathlib's
small-field cyclic Hilbert 90 theorem.

For the commutator consequence, let `D : Type uD` be any ring with a
`K`-algebra structure, `ι : L →ₐ[K] D` an actual algebra map, and
`u : Dˣ` an actual unit satisfying

`(u : D) * ι(a) * (u⁻¹ : D) = ι(σ(a))` for every `a : L`.

Only `Ring D` is needed; division algebras are a particular case. For
`x : Lˣ` with `Algebra.norm K (x : L) = 1`, Hilbert 90 supplies `y`.
Set `v = Units.map ι.toMonoidHom y`. The conjugation identity on unit
values gives the same identity in `Dˣ`, and transporting
`x = y / σ(y)` through the unit map gives

`Units.map ι.toMonoidHom x = v * u * v⁻¹ * u⁻¹`.

This is the single group commutator `⁅v,u⁆`.
The theorem `exists_commutator_of_norm_eq_one` supplies `v` with precisely
this equality, and `map_mem_commutator_of_norm_eq_one` places the image
in the actual commutator subgroup of `Dˣ`.

The construction is an internal algebraic deduction from finite
product/sum identities, Mathlib's character independence and its actual
finite-Galois norm formula. The commutator assertion follows directly
from that construction and the stated conjugation identity; no new
interpretation of an original source is claimed.

The finite cyclic extension, its specified generator and, in the
commutator consequence, the specified algebra map and conjugating unit
remain explicit hypotheses. This unit does not construct local
unramified maximal subfields, prove existence of the conjugating unit,
compare the subfield norm with reduced norm, or move arbitrary
division-algebra norm-one elements into such a subfield. It therefore
does not prove local SK₁ vanishing or `LocalKneserTitsStatement`.
