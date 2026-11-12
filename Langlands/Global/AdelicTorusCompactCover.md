# Compact principal representatives for arbitrary actual number-field tori

Let `F` be a number field in arbitrary universe `u`, and let `T` be an actual
affine group scheme locally of finite type over `F`, with `IsTorus T`.
`AdelicGroupPoints.torusCompactSet F T hT` is a compact set in the original
`normOneSubgroup F T` such that every norm-one adelic point `g` has an actual
rational point `q` with

```text
rationalNormOne F T q * g ∈ torusCompactSet F T hT.
```

The norm-one subgroup is the existing intersection of the normalized
absolute-value kernels of all `F`-rational algebraic characters.
The topology and principal map are the original ones. The assertion retains
all such number fields and tori, including nonsplit tori, anisotropic tori,
positive-dimensional split centers and the trivial torus.

This is an internal derivation. The theorem
`hasCompactNormOneRationalCover_of_isTorus` first invokes the published
`torusFiniteGaloisSplitting` to obtain a finite Galois extension `L/F` in the
same universe over which the actual pullback base change of `T` is split.
The finite-extension number-field theorem equips `L` with its number-field
instance. The published
`hasCompactNormOneRationalCover_of_isSplitTorus` constructs compact principal
representatives for that actual upper-field group.

Apply
`AdelicGaloisUnit.hasCompactNormOneRationalCover_of_baseChange` to descend
these compact representatives. That theorem proves compactness using the
closed embedding of the exact scalar-extension map on norm-one rational
quotients and reconstructs compact representatives from local compactness.
Its proof uses actual Galois fixed-image descent, closed discrete principal
subgroups and the canonical adelic Weil comparison. It assumes neither the
general reductive compactness theorem nor full Weil-character classification.

Finally, `torusCompactSet` chooses a set from this proved existence theorem.
`isCompact_torusCompactSet` and
`exists_rational_mul_mem_torusCompactSet` are the two components of that
existence witness. No extra compactness hypothesis or supplied fundamental
set occurs in the construction.

The module establishes the torus case of the parent compactness program. It
does not prove compactness for reductive groups with nontrivial semisimple
part.
