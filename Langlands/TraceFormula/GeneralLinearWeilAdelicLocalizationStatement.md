# Localization of the adelic comparison for the Weil restriction of GLₙ

`Langlands.TraceFormula.GeneralLinearWeilAdelicLocalizationStatement.{u}`
quantifies over number fields `K` and `L` in `Type u` with `[Algebra K L]`
and `[FiniteDimensional K L]`, and over all natural numbers `n`.
Write `W` for the Weil restriction of the general linear group over `L` to
`K`, and `K_i` for the completion at a place `i` of `K`.

The map `Φ` from `W(𝔸_K)` to `GL_n(𝔸_L)` is the composite used in
`GeneralLinearWeilAdelicTwistStatement`. First `AdelicGaloisUnit.weilAdelicEquiv`
gives an adelic point of the base-changed group over `L`. Then
`AdelicGroupPoints.map` applies the group scheme isomorphism
`GroupScheme.GeneralLinear.baseChangeIso` on adelic points.
Finally `GeneralLinearGroupPoints.adelicHomeomorph L n` gives an invertible
matrix over `𝔸_L`.

For each finite or infinite place `i : Place K`, the coefficient ring map
`r : 𝔸_L → K_i ⊗_K L` is the composite

```text
𝔸_L ──→ L ⊗_K 𝔸_K ──→ L ⊗_K K_i ──→ K_i ⊗_K L.
```

The arrows are the inverse of `numberFieldAdeleTensorEquiv K L`, the tensor
map `1 ⊗ adeleProjection K i` where `1` is the identity on `L`, and the factor
exchange `localSwap K L i`. The last ring is `LocalBaseChangeAlgebra K L i`.
For every `g : AdelicGroupPoints K W` the proposition states the equality in
`GL_n(K_i ⊗_K L)`

```text
Matrix.GeneralLinearGroup.map r (Φ g) =
  localPointsEquiv K L n i (atPlace K W i g).
```

On the left, `Matrix.GeneralLinearGroup.map` applies `r` to the matrix entries.
On the right, `atPlace` projects the adelic point to `W(K_i)` and
`localPointsEquiv` gives its matrix in the local tensor algebra.

## Mathematical origin

For a `K`-algebra `A`, the Weil restriction comparison
`AffineWeil.unitGroundPointsEquiv` followed by
`GroupScheme.GeneralLinear.affinePointsEquiv` identifies `W(A)` with
`GL_n(L ⊗_K A)` naturally in `A`. At `A = 𝔸_K`,
`AdelicGaloisUnit.weilAdelicEquiv_eq` and
`AdelicGaloisUnit.tensorAdelicEquiv_apply` express the adelic comparison
in these tensor coordinates, using the canonical map to `𝔸_L`.
At `A = K_i`, `localPointsEquiv` uses the same identification followed by
`localSwap`. Naturality along `adeleProjection K i` gives the compatibility
in the proposition.

Getz and Hahn describe adelic points by their local points in
*An Introduction to Automorphic Representations* (2024), §2.3, Proposition 2.3.1,
printed p. 57 (PDF p. 74). The matrix equality here expresses the compatibility
of the Library's two comparisons with those local coordinates.
The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
