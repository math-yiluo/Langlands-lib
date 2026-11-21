# Relative parabolic discriminants at an exact cyclic norm

`RelativeParabolicDiscriminantNormStatement` and its proof
`twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm` give the relative
comparison used by Henniart–Lemaire, *Changement de base et induction
automorphe pour GL(n) en caractéristique non nulle* (2011), II.4.5, printed
p. 88 (PDF p. 96), just before formula (3). The source uses the ordinary and
twisted relative factors defined in (1), p. 86 (PDF p. 94). This is a
field-algebra derivation of that comparison at exact Levi norm representatives;
it does not formalize the source's orbital-integral argument.

Let `F` and `E` be fields with `Algebra F E` and `IsCyclicAlgebra σ l`.
For any standard block shape `B` of rank `n`, suppose `δ : B.Levi E` and
`γ : B.Levi F` satisfy the exact equality in `GL_n(E)`

```
cyclicNorm σ l (B.leviEmbedding E δ) = baseChange F E n (B.leviEmbedding F γ).
```

Then `twistedRelativeParabolicDiscriminant B σ δ` equals
`relativeParabolicDiscriminant B F γ` in `F`. These are the determinants of
`σ − Ad(δ)⁻¹` over `F` on `𝔤(E)/𝔪(E)` and `1 − Ad(γ)⁻¹` over `F` on
`𝔤(F)/𝔪(F)`, respectively. No regularity, topology, characteristic, or
ramification hypothesis is needed for the equality. The exact equality of
norms, rather than arbitrary conjugacy in the ambient group, is the hypothesis.
The field universes are independent.

## Proof implemented in Lean

1. The quotient is coordinated by off-block entries, reindexed by a finite
   ordinal. The adjoint action on the quotient is multiplicative by the
   conjugation law on full matrices. In these coordinates it defines a monoid
   homomorphism `M` from the actual Levi into `GL_d`, where `d` is the off-block
   count. Evaluating on a single matrix unit gives the `(p,q)` entry of `M(m)`
   as `m[p.row,q.row] * m⁻¹[q.col,p.col]`, with the elements embedded in the
   ambient group. This proves compatibility both with entrywise automorphisms
   and with field inclusion. It follows that the ordered cyclic norm of `M(δ)`
   equals `M(γ)` after extension. Transposing off-block positions exchanges
   the strict upper and lower halves, so `d` is even.
2. Conjugating the twisted quotient map into coordinates replaces `σ` by
   `coordinateFieldAut` and the adjoint action by the matrix column action.
   There the factorization is
   `σ − M(δ)⁻¹ = (−M(δ)⁻¹) (1 − M(δ) σ)`.
   Restricting scalars on the first factor takes the field norm of the
   extension-field determinant. Even dimension removes its minus sign, and
   `IsCyclicAlgebra.determinant_cyclicNorm` identifies the scalar norm of the
   determinant of `M(δ)` with the determinant of the matrix norm; inversion
   gives the corresponding result for the inverse determinant.
3. For the second factor, `IsCyclicAlgebra.det_cyclicSemilinearDefect` gives
   the determinant of one minus the ordered matrix norm after the scalar is
   embedded into `E`. Multiplying the two factors gives the determinant of
   `M(γ)⁻¹ − 1` after base change. Even dimension again removes the sign.
   The resulting determinant is the scalar extension of the ordinary
   discriminant, since determinants commute with the field map. Injectivity
   of the field map yields the equality in `F`.

This result compares only the relative factors for the standard block Levi.
It does not prove their nonvanishing, compare Haar measures, or prove the
orbital descent or induced character formulas.
