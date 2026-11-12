# Closed subgroups with connected fibres containing all jets

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer` proves
the density step of the normalizer argument, in coordinates.

## Setting

`A` is a commutative ring and `F` is a functor from commutative `A`-algebras to
groups, corepresented through `e` by an `A`-algebra `C`. For a point `x` of
`F` over `B`, `cls e x : C →ₐ[A] B` is its classifying map. `counit e` is the
classifying map of the identity point over `A`, and `antipode e` and `comul e`
classify the inverse of the universal point and the product of the two
universal points over `C ⊗[A] C`. `Z` is a family of subgroups `Z B ≤ F.obj B`,
and `IsCutOutBy e Z K` (Library) says that `x ∈ Z B` exactly when `cls e x`
kills the ideal `K` of `C`.

## Main result

`eq_bot_of_forall_le_pow`: assume `C` is smooth over `A`, and every fibre
`Spec (κ(p) ⊗[A] C)` over a point `p` of `Spec A` is connected. Let `Z` be
cut out by a finitely generated ideal `K` with `K ≤ (ker (counit e)) ^ n` for
every `n`. Then `K = ⊥`, so `Z` is all of `F`.

Geometrically: a finitely presented closed subgroup of a smooth group with
connected fibres which contains every infinitesimal neighbourhood of the
identity section is the whole group.

## Proof

*Good locus.* For a point `x` over `B` and an ideal `Q` of `B`, `Good e K x Q`
means that some `t ∈ C` with `t * K = 0` satisfies `cls e x t ∉ Q`. For prime
`Q` this says that the image of `Q` under `x` lies in the open complement of
`V(Ann K)`, the open subscheme on which `Z` agrees with `F`. Goodness is
compatible with algebra maps (`good_map_iff`) and defines an open subset of
`Spec B` (`isOpen_good`).

*Group properties.* `K` is stable under the antipode (`antipode_mem`),
because `Z` is closed under inverses; hence goodness is stable under inverses
(`good_inv`). The comultiplication is flat: it is the left inclusion
`C → C ⊗[A] C` followed by the shear automorphism `(x, z) ↦ (x z, z)`
(`comul_flat`). Since `Z` is closed under products, `comul e` maps `K` into
the ideal `K ⊗ C + C ⊗ K`. That ideal is killed by `t₁ ⊗ t₂` whenever
`t₁` and `t₂` kill `K`. The equational criterion of flatness
(`exists_mul_eq_zero_of_flat`), applied along `comul e`, then gives an
annihilator of each element of `K` whose image avoids `Q`. Finite generation of
`K` combines these into one annihilator (`exists_forall_mul_eq_zero_of_fg`).
So goodness is stable under products at prime ideals (`good_mul`).

*An annihilator at the identity.* Every element of `K` lies in every power of
`ker (counit e)`. The Krull-intersection result
`exists_mul_eq_zero_of_forall_mem_pow` of `KrullSection` gives an
annihilator with counit `1`. Finite generation gives a single `s` with
`s * K = 0` and `counit e s = 1`. Hence the identity point is good at every
proper ideal (`good_one`).

*The fibre argument.* Fix an `A`-field `k` with `Spec (k ⊗[A] C)` connected,
and let `V` be the good locus of the universal fibre point. `V` is open and
contains the prime of the identity point, so it is nonempty. It is also closed
(`exists_isOpen_not_good`): let `y ∉ V` have residue field `κ`. Over
`E = (k ⊗[A] C) ⊗[k] κ`, let `u` be the fibre point and let `y'` be the point
`y`, defined over `κ`. The set `W` of primes of `E` at which `y'⁻¹ u` is good is
open. Its image under the projection `Spec E → Spec (k ⊗[A] C)` is open by
Mathlib's `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`.
The image contains `y`, because `y'⁻¹ u` is the identity at the diagonal
`κ`-point. It misses `V`, because goodness of both `u` and `y'⁻¹ u` would make
`y' = u (y'⁻¹ u)⁻¹` good at a prime of `E`, and hence `y` good. By
connectedness `V` is everything (`good_fibrePt`).

*Conclusion.* Every prime `P` of `C` lies in some fibre, so the universal point
is good at `P`. If `K ≠ ⊥`, then `Ann K` is proper and lies in a maximal ideal
`P`. Goodness at `P` gives `t ∈ Ann K` with `t ∉ P`, a contradiction.

## Provenance

This is the density step of Brian Conrad, *Reductive group schemes* (2014),
Proposition 2.1.6 (printed and one-based PDF pp.62–63, source
`conrad-2014-reductive-group-schemes`). There an open subgroup of a smooth
group with connected fibres is shown to be everything. The formal route is
derived for this proof. It works with the annihilator locus of `K` in
coordinates. It replaces Conrad's fibrewise open-subgroup argument by the
coset argument above over residue fields, and uses no Noetherian hypothesis or
closed-point argument.
