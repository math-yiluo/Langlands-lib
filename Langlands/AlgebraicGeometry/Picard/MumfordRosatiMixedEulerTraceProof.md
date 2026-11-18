# Proof of the Mumford Rosati mixed Euler trace formula

Lean module: `Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceProof`. Authors:
Worker 5218 and Worker 195.

`Langlands.AbelianScheme.Rosati.mumfordMixedEulerTrace : MumfordMixedEulerTraceStatement.{u}`
proves the Library statement `Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`
in its universe `u`. The theorem's type is exactly the statement. No hypothesis is added.

## What the statement says

Let `k` be an algebraically closed field of characteristic zero. Take an abelian scheme `A`
over `Spec k` of positive relative dimension `g`, with the Rosati data `P`, `W`, `hadd` and
`lam` of the statement. Assume that the underlying map of `lam` is the Mumford map of an
actual ample line bundle `L`. Then for every actual endomorphism `f` of `A`,

`traceForm(lam, f, f) * pureTopCoefficient(L, g) = 2 * mixedCoefficient(L, f*L, g)`.

See the statement's Markdown for the exact objects. It relates this identity to Milne,
*Abelian Varieties*, author revision January 2, 2022, Theorem 17.3 and Theorem 13.3(b)
(registered source `milne-abelian-varieties-1986-author-2022`).

## Proof

The proof is a single term. It applies three published reductions to six published
theorems:

```
mumfordMixedEulerTraceCharZeroReduction
  (isogenyDegreeTateDeterminantCharZeroReduction endomorphismDegreeLinePolynomial
    (isogenyDegreeTateDeterminantNormReduction isogenyFinrankKernelCard
      isogenyKernelCardTateDeterminant tateDeterminantNonzeroSurjective
      fieldSurjectiveEndomorphismIsogeny))
  mumfordEulerDegree
```

All names are in the namespace `Langlands.AbelianScheme` or `Langlands.AbelianScheme.Rosati`.
All are used at the universe `u`.

### The reductions

- `isogenyDegreeTateDeterminantNormReduction` (module
  `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReduction`) proves
  `IsogenyFinrankKernelCardStatement → IsogenyKernelCardTateDeterminantStatement →
  TateDeterminantNonzeroSurjectiveStatement → FieldSurjectiveEndomorphismIsogenyStatement →
  IsogenyDegreeTateDeterminantNormStatement`.
  The last statement (G23) says that, in characteristic zero and for a prime `p`, the degree
  of an isogeny endomorphism has the same `p`-adic norm as the determinant of its rational
  `p`-adic Tate map, and that this determinant is `0` for an endomorphism that is not an
  isogeny.
- `isogenyDegreeTateDeterminantCharZeroReduction` (module
  `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroReduction`) proves
  `EndomorphismDegreeLinePolynomialStatement → IsogenyDegreeTateDeterminantNormStatement →
  IsogenyDegreeTateDeterminantCharZeroStatement`.
  The conclusion (S1₀) says that, in characteristic zero, the degree of an endomorphism equals
  the determinant of its rational `p`-adic Tate map, and that determinant is `0` for a
  non-isogeny. This is Milne's Proposition 12.9 (p. 23) in characteristic zero.
- `mumfordMixedEulerTraceCharZeroReduction` (module
  `Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceCharZeroReduction`) proves
  `IsogenyDegreeTateDeterminantCharZeroStatement → MumfordEulerDegreeStatement →
  MumfordMixedEulerTraceStatement`.

### The six input theorems

- `endomorphismDegreeLinePolynomial : EndomorphismDegreeLinePolynomialStatement` (G1),
  module `Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialProof`. The degree is
  polynomial of degree at most `2g` along lines `n • φ + ψ` (first step of the proof of
  Milne's Proposition 12.4, p. 21).
- `isogenyFinrankKernelCard : IsogenyFinrankKernelCardStatement` (G2a), module
  `Langlands.AbelianScheme.IsogenyFinrankKernelCardProof`. In characteristic zero the degree
  of an isogeny is the number of `k`-points of its kernel (Milne, Section 8, p. 12).
- `isogenyKernelCardTateDeterminant : IsogenyKernelCardTateDeterminantStatement` (G2b),
  module `Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantProof`. For `p` invertible
  in `k`, the number of kernel points of an isogeny endomorphism and the determinant of its
  rational `p`-adic Tate map have the same `p`-adic norm.
- `tateDeterminantNonzeroSurjective : TateDeterminantNonzeroSurjectiveStatement` (G3a),
  module `Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveProof`. In characteristic
  zero, an endomorphism whose rational `p`-adic Tate determinant is nonzero is surjective.
- `fieldSurjectiveEndomorphismIsogeny : FieldSurjectiveEndomorphismIsogenyStatement` (G3b),
  module `Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyProof`. A surjective
  endomorphism is an isogeny (Milne, Proposition 8.1, p. 12).
- `Rosati.mumfordEulerDegree : Rosati.MumfordEulerDegreeStatement` (S2), module
  `Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeProof`. For an ample Mumford
  presentation `lam` of `L`, the map `n • lam + f ≫ lam ≫ f^∨` is an isogeny of degree
  `χ(f^* L ⊗ L^n)^2` for all large `n`.

The proof routes of the reductions and of the inputs are described in their modules'
Markdown files. This module adds no other declarations.
