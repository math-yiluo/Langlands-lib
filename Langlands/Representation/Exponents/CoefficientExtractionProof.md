# Exact coefficient extraction by common stable Jacquet lifts

Author: Worker 1197.

The theorem `Langlands.glJacquetExponentCoefficientExtraction.{uF,uV}`
proves exactly the closed Library proposition
`Langlands.GLJacquetExponentCoefficientExtractionStatement.{uF,uV}`.
Its sole declaration has that unapplied type. The statement pair and all
existing imported pairs are unchanged.

The implemented proof derives the coefficient directly from a common stable
Jacquet lift and compact-open smooth duality. It does not take a canonical
pairing, an asymptotic formula, opposite Jacquet duality or an eigenvector as
an additional premise. This route also allows the threshold to be exactly
one.

## Published inputs

The module imports the target and these existing Library proofs:

- `Exponents.JacquetEigenvectorProof`:
  `glJacquetExponentEigenvector` extracts a nonzero ordinary eigenvector for
  the entire split centre with the original character. Its proof establishes
  normalized Jacquet admissibility and uses a finite-dimensional Levi-fixed
  space, rather than a finite-dimensional ambient representation.
- `Jacquet.CanonicalLiftBijectivityProof`:
  `stableImageJacquetMap_bijective_of_finiteDimensional` identifies the
  actual stable image of compact compression with the fixed vectors of the
  actual upper coinvariant quotient.
- `Jacquet.StableImageTupleIndependenceProof`:
  `stableImage_blockScalar_eq` identifies the stable-image submodules for
  any two strict block-scalar tuples. Its imported
  `Group.GL.BlockContractionProof` also supplies `deepChamberNonempty`.
- `Smooth.Contragredient.CompactDualityProof`:
  `smoothDualFixedRestriction_bijective` extends any linear functional on
  the compact-fixed subspace to an actual compact-fixed element of
  `SmoothDual ρ`.
- `Group.GL.BlockIwahoriBasis`:
  `exists_compactOpenSubgroup_hasBlockIwahoriFactorization` supplies the
  needed compact open subgroup inside any identity neighborhood, with its
  weak-chamber containments.

The canonical-lift imports provide `Jacquet.blockCompressedAction_mk`
and `Jacquet.map_averageMap_of_forall_eq`. The former intertwines
compression with the **unnormalized** quotient action and introduces no
scalar. The latter evaluates a linear map on the normalized compact average
when it is constant on the compact orbit.

## Implemented proof

Fix all parameters of the target, admissible `ρ`, block shape `B` and
generalized normalized upper exponent `χ`. Install `T.topology` and
`T.generalLinearTopologicalGroup n`. Write `q = Jacquet.mk ρ N`, where
`N = B.unipotentSubgroup F.Carrier`, and let `A` be the unnormalized action
of `M = B.leviSubgroup F.Carrier` on these coinvariants.

First apply `glJacquetExponentEigenvector` to obtain `w ≠ 0` with
`T.splitCentreJacquet B ρ a w = χ(a) • w` for every tuple `a`. Choose an
actual quotient representative `v₀` by `B.jacquetMk_surjective`.
Smoothness gives an open subgroup `U` fixing `v₀`. The cofinal Iwahori
basis gives compact open `K ⊆ U` with the published block factorization.
Thus `v₀` is `K`-fixed and

```
W = fixedJacquetMap ρ N M hMN K ⟨v₀, hvK⟩
```

lies in the `(M ∩ K)`-fixed part of the unnormalized quotient. Under
`B.jacquetModuleEquiv ρ`, its underlying quotient vector is exactly `w`.
Consequently `W ≠ 0`.

For every tuple `a`, put

```
μ(a) = (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ)
         * (χ a : ℂ).
```

The normalized eigenvector equation is rewritten on the representative
`v₀` by `normalizedJacquet_mk_eq_inv_halfModulus`. Apply
`B.jacquetModuleEquiv ρ` and multiply by the positive-half unit scalar.
The scalar and its inverse cancel, giving

```
A (B.blockScalarInLevi F.Carrier a) W = μ(a) • W.
```

This is the same upper character `χ`, with no inversion or conjugation.
It uses the explicit half modulus already in the target and does not
introduce a new Haar-modulus comparison.

Choose a reference strict tuple `c` using `B.deepChamberNonempty T 1`.
Admissibility gives finite-dimensional `K`-fixed vectors. Bijectivity of
`stableImageJacquetMap` for `c` gives a stable lift `x` with `q x = W`.
Since `W ≠ 0`, `x` is nonzero.

This one lift works simultaneously for every strict tuple. To see this,
fix any strict `a`. Tuple independence places the same `K`-fixed vector
`x` in the actual stable image for `a`. Both its compression `C(a)x` and
`μ(a) • x` belong to that stable image. The quotient law gives

```
q (C(a)x) = A(a)(q x) = μ(a) • W = q (μ(a) • x).
```

Injectivity of the stable-image Jacquet map for `a` therefore implies
`C(a)x = μ(a) • x`. The lift was chosen before `a`; this argument does
not choose a new lift for each tuple.

Choose a linear functional `φ₀` on the `K`-fixed space that detects `x`,
using algebraic-dual separation, and put `φ = φ₀(x)⁻¹ • φ₀`. Then
`φ(x) = 1`. Compact-open smooth duality supplies
`ℓ ∈ (SmoothDual ρ)^K` restricting to `φ`, so `ℓ(x) = 1`.
Evaluate the fixedness equation of `ℓ` at the inverse subgroup element to
obtain `ℓ(ρ(k)y) = ℓ(y)` for every `k ∈ K` and `y ∈ V`.
The published averaging lemma now gives `ℓ(e_K y) = ℓ(y)`.
Consequently, for every strict `a`,

```
ℓ(ρ(B.blockScalar F.Carrier a)x)
  = ℓ(e_K ρ(B.blockScalar F.Carrier a)x)
  = ℓ(C(a)x)
  = μ(a) ℓ(x)
  = μ(a).
```

Take the witnesses to be the underlying vector `x : V`, this actual smooth
functional, and `ε = 1`. The target's forward-ratio inequalities are
converted to `B.IsStrictlyContracting T a` using
`blockScalarRatio_apply`, `normalizedAbsUnits_coe`, the unit coercion laws
and `div_eq_mul_inv`. The group element `B.blockScalar F.Carrier a` is
the target's embedded block-scalar Levi element. This finishes the exact
coefficient equality.

## Scope and provenance

The field and carrier universes remain independent and in the target's
order `uF,uV`. The proof retains every prime, finite p-adic field, supplied
topological realization, positive rank, complex carrier, admissible
representation, block shape and generalized exponent. All witnesses
precede the universal quantifier over tuples. No bound is imposed on common
central scalars: only forward ratios occur in the chamber. For one block
those conditions are vacuous, and the same proof gives the equation for
every scalar tuple. Zero carriers need no extra hypothesis or exceptional
case, since a nonzero generalized exponent cannot occur in their Jacquet
module.

The implementation is an internal derivation from the published inputs
listed above. The statement's motivating original is J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), §I.2–I.3, pp.242–243, Theorem I.4.1 and Corollary
I.4.2, p.245, and the first paragraph of the proof of Proposition III.2.2,
pp.265–266. Registered source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
These pages were read from the retained original; the extraction formula
on p.266 was checked in its page image. No applicable project errata file
was found. The original obtains extraction through the canonical pairing;
this proof instead uses published compression and canonical-lift results
to establish the coefficient directly. It asserts no construction of the
pending actual canonical pairing or opposite-duality equivalence.

In terms of the five obligations discussed in the statement Markdown,
Jacquet fixed-space finiteness and generalized-to-ordinary extraction are
provided by the imported eigenvector theorem. Actual quotient
representatives and stable lifts are constructed in this proof.
Compact-open smooth duality, algebraic separation and rescaling provide
the detecting functional without needing opposite-pairing
nondegeneracy. Explicit inverse-half cancellation and tuple independence
provide the normalization and the whole strict chamber. No tempered
criterion, Langlands uniqueness or square-integrable classification is
used.

The Lean-service Lake build and complete declaration inspection succeed without
warnings. The inspected theorem retains universe parameters `uF,uV` and
uses only `propext`, `Classical.choice` and `Quot.sound`. These development
checks do not replace independent semantic review, exact-target validation
or Library publication.
