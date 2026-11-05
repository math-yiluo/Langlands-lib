# Frobenius kills finite-coordinate stability defects

Let `k` be a field in any universe, `G` an affine group scheme over `k`, and
`ρ` an actual matrix representation on a finite coordinate space indexed by
`n`. Let `B : Matrix n m k` and `C : Matrix m n k`, where `m` is also finite.
The construction does not require `C * B = 1`.

`affineMatrix_baseField` identifies the matrix at an affine test point with
coefficients in `k` with the rational matrix at a corresponding relative
`Spec k` point. Its proof uses the identity map of `Spec k`, naturality of the
matrix of global sections, and the inverse identities of `Γ(Spec k) ≅ k`.

`affineCoordinateStabilityDefect ρ B C` is the matrix

```
M * B_A - B_A * (C_A * M * B_A)
```

in the full coordinate algebra `A = O(G)`. Here `M` is the universal affine
matrix of `ρ`, and `B_A`, `C_A` are obtained by applying `algebraMap k A` to
all entries. In particular the definition retains nilpotent coefficients.

Suppose `k` is algebraically closed, `G` is locally of finite type over `k`,
and for every rational point `g` the matrix identity

```
ρ(g) * B = B * (C * ρ(g) * B)
```

holds. Then `isNilpotent_affineCoordinateStabilityDefect` proves that every
entry of the defect is nilpotent. Evaluating the universal matrix under any
`k`-algebra map `O(G) → k` gives an affine point over `k`; the first comparison
lemma and the assumed identity make the evaluated defect zero. The published
Nullstellensatz helper
`StabilizerImageDichotomy.isNilpotent_of_forall_algHom` then applies to the
finite-type coordinate algebra. No reducedness premise is used.

For prime exponential characteristic `p`,
`exists_frobeniusPower_isStableCoordinates` produces an exponent `e` such that
the actual representation `ρ.frobeniusPower p e` has stable coordinates
`B^(p^e)` and `C^(p^e)`, with powers taken entrywise. Stability here is the
published `IsStableCoordinates` identity on **every relative test scheme**.
The proof bounds the finitely many nilpotence exponents by one natural number
and uses `e < p^e` to kill every entry. The characteristic-power map is a ring
homomorphism and commutes with the scalar map, so the killed equation is the
universal stability equation of the powered matrices and representation. The
published affine-model stability criterion pulls it back to all tests.

This is an internal derivation from the actual matrix Frobenius and affine
coordinate interfaces and the published Nullstellensatz result. Its motivation
is the iterated Frobenius step in Milne, *Algebraic Groups* (2017), Lemma 5.16,
printed p. 102 (PDF p. 118). It replaces a smooth-image argument only for this
finite-coordinate stability conclusion. It constructs no smooth image, makes
no characteristic-zero claim, and does not assert inverse-character occurrence
or the normal-subgroup quotient existence theorem.
