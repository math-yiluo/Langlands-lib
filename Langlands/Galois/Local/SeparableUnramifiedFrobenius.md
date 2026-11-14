# Frobenius on the actual inertia fixed field

Worker 220 derived this internal arithmetic adapter for the twisted chamber
quotient construction from the imported Library and Mathlib results. It is not
a separate assertion attributed to the Bruhat–Tits literature.

Let `F` be any nonarchimedean local field in universe `u`, with its specified
valuation and topology, and put `K = inertiaFixedField F`. There is no
characteristic assumption.

The definition `fixedFieldResidueGaloisEquiv F` is a topological group
isomorphism from `Gal(K/F)` to the Galois group of the spectral residue
extension

```
ResidueField (extensionIntegers F K) / ResidueField (baseIntegers F).
```

Its underlying homomorphism is the published `residueHom F K`. The new lemma
`fixedField_residueHom_injective F` establishes injectivity. Surjectivity and
continuity are the published `residueHom_surjective` and
`residueHom_continuous`. Compactness of the source and the Hausdorff property
of the target give continuity of the inverse.

The injectivity proof lifts an automorphism with trivial residue action to
the separable closure. Every Teichmüller root belongs to `K`, by
`mem_inertiaFixedField_of_pow_eq_one`. Compatibility of residue actions with
restriction (`residueHom_restrict`) shows that the lift preserves its
residue. The root-rigidity lemma `eq_of_pow_eq_one_of_sub_mem`, using
`teichOrder_isUnit`, shows that the lift fixes the root. The criterion
`mem_separableInertia_of_forall_teichSet` then puts the lift in inertia, so it
fixes all of `K`.

The helper `arithmeticFrobenius_denseRange k L` applies to an arbitrary
algebraic extension of a finite field, with independent universes for `k`
and `L`. It says that the integer powers of
`FiniteField.frobeniusAlgEquivOfAlgebraic k L` have dense range in `Gal(L/k)`.
The proof uses `isGalois_of_finite_base`, the Krull neighborhood basis of
finite Galois intermediate fields, and Mathlib's theorem that arithmetic
Frobenius generates the Galois group of a finite field extension. Restriction
commutes with the cardinality power map.

Finally, `exists_fixedField_arithmeticFrobenius F` supplies a single
`φ : Gal(K/F)` with both properties:

1. For every finite-dimensional intermediate field `E/F` in `K`, and every
   `σ : Gal(K/F)`, some `n : ℤ` satisfies
   `σ⁻¹ * φ ^ n ∈ E.fixingSubgroup`.
2. For every `x : fixedFieldIntegers F`,
   ```
   residue _ (fixedFieldIntegerAut F φ x)
     = residue _ x ^ Nat.card 𝓀[F].
   ```
   Here `fixedFieldIntegerAut` is the actual integer-ring automorphism from
   `Langlands.GroupScheme.Descent.FiniteUnramified`.

The proof transports arithmetic Frobenius through the inverse of the
topological comparison. Density transports along that homeomorphism. Each
fixing-subgroup coset in item 1 is open and nonempty, so it meets the powers.
For item 2, `fixedFieldIntegersEquiv` transports the spectral residue equality
to the actual fixed-field integer ring, and `localResidueEquiv` identifies
the two finite base residue cardinalities.

These declarations provide arithmetic input only. They do not construct a
finite-field reductive quotient or prove a chamber or cocycle-vanishing
statement.
