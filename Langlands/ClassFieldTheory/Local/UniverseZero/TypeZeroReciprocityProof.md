# Finite abelian local reciprocity at field universes zero: proof

The module `Langlands.ClassFieldTheory.Local.UniverseZero.TypeZeroReciprocityProof`
proves the published proposition
`Langlands.LocalClassField.UniverseZero.FiniteAbelianReciprocityTypeZeroStatement` with
the theorem

```lean
theorem Langlands.LocalClassField.UniverseZero.finiteAbelianReciprocityTypeZero :
    FiniteAbelianReciprocityTypeZeroStatement
```

Its type is exactly the target. The target is the transparent alias of the Library
proposition `Langlands.LocalClassField.FiniteAbelianReciprocity.{0, 0}` in
[`TypeZeroStatement`](TypeZeroStatement.lean). The module imports the target
module, the supporting module
[`FiniteGeometricQuotient`](../FiniteGeometricQuotient.lean) and the published
bridge module [`InertiaFromGeometricProof`](InertiaFromGeometricProof.lean). It
changes none of them and imports no module under `Langlands/NYLL/`.

## What is proved

Fix a prime `p`, fields `F E : PadicField.{0} p`, the algebra, scalar-tower,
finite-dimension and abelian-Galois instances of the Library proposition, and
arbitrary supplied `TF : F.TopologicalData` and `TE : E.TopologicalData`. Give
`F.Carrier` the topology `TF.topology`. Then there is a continuous multiplicative
equivalence `r` from the actual norm quotient
`F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range` to
`Gal(E.Carrier/F.Carrier)` such that:

- **geometric clause:** for every `a : F.Carrierˣ` with `TF.ord a = 1` and every
  `x : E.Carrier` with `TE.discreteValuation x ≤ 1`,
  `TE.discreteValuation ((r [a]).symm x - x ^ TF.residueCardinality) < 1`;
- **inertia clause:** for every `σ`, `σ = r [a]` for some unit `a` with
  `TF.ord a = 0` exactly when `TE.discreteValuation (σ x - x) < 1` for every
  `x` with `TE.discreteValuation x ≤ 1`.

Here `[a]` is `QuotientGroup.mk a`.

## Proof

1. **The witness.** The Library theorem `continuous_geometricArtin F TF E TE`
   says that `geometricArtin F E TE` is continuous for `TF.topology`. That map
   is by definition `geometricSymbol F E.Carrier`. The supporting theorem
   `exists_quotientEquiv_geometricSymbol F E.Carrier` then gives `r` with
   `r [a] = geometricSymbol F E.Carrier a` for every `a`.
2. **Geometric clause.** Let `TF.ord a = 1` and `TE.discreteValuation x ≤ 1`.
   Rewrite `r [a]` to the geometric symbol by step 1. The Library theorem
   `ramified_normalization F TF E TE a ha x hx` is the required congruence for
   `geometricArtin F E TE a`. It holds for every abelian extension, ramified or
   not, and for arbitrary supplied `TF` and `TE`.
3. **Inertia clause.** The published `inertiaFromGeometric p F E TF TE` applies
   to every multiplicative equivalence from the norm quotient to the Galois
   group that satisfies the geometric clause. Applied to the underlying
   equivalence `r.toMulEquiv` and step 2, it gives the inertia clause.

The theorem returns `⟨r, step 2, step 3⟩`.

## Scope and provenance

Every clause holds for the single map `r`, the quotient of the Library's
geometric finite Artin symbol. The proof adds no hypothesis to the target. The
mathematical source of the target is Serre, *Local Fields*, XIII.4,
Proposition 8 with its corollary, and Proposition 13 with its corollary
(source `serre-1979-local-fields`), in the geometric convention explained in
[`FiniteReciprocityStatement.md`](../FiniteReciprocityStatement.md). The proof
assembles published Library theorems, starting from the Library's own finite
Artin symbol.
It does not follow Serre's argument.

The module compiled without errors or warnings with Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
