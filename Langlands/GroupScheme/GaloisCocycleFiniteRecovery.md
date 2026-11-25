# Finite recovery of coefficient Galois cocycles

This is an internal construction from the Library's affine Galois-point descent
and field-tower comparisons, together with Mathlib's normal closure. All fields
and schemes have arbitrary common universe `u`. The group scheme is affine; no
finite type, connectedness or reductivity hypothesis is needed.

Let `K/k` be a possibly infinite Galois extension, let `G` be an affine group
scheme over `k`, and let
`c : Aut(K/k) → rationalPoints (baseChanged k K G)` satisfy
`c(σ τ) = c(σ) · rationalConjugate σ (c(τ))`. Suppose that `c` is identically one
on the fixing subgroup of an intermediate field `E` normal over `k`.

The construction `GaloisCocycleFiniteRecovery.rationalValue` gives points of the
actual base change of `G` to `E`, indexed by `Aut(E/k)`.
`relativeRationalExtend_rationalValue` proves that extension to `K` of the value
at the restriction of **every** automorphism `σ` is exactly `c(σ)`.
`rationalValue_mul` proves the crossed-homomorphism identity for these recovered
points, with the Library's actual coefficient action on the actual base change.
These results do not require `E/k` to have finite degree.

The proof first works with coefficient points. If two automorphisms have equal
restriction to `E`, their quotient lies in the fixing subgroup, so the cocycle
identity gives equal values. If `τ` fixes `E`, normality implies that `τσ` and
`σ` have equal restriction. Comparing their cocycle values then shows that `τ`
fixes `c(σ)` coefficientwise. The relative group `Aut(K/E)` therefore fixes
each value. `GaloisPoint.relativeAlgebraicDescend` transports these fixed points
to the base-changed group over `E`, applies the existing arbitrary-Galois affine
point descent, and transports the result back to the original coefficient
convention. The theorem `relativeExtend_relativeAlgebraicDescend` proves exact
recovery. Choosing an automorphism lift defines `value`; the equal-restriction
lemma makes its extension independent of that choice. Injectivity of coefficient
extension and its compatibility with restricted automorphisms prove `value_mul`.

`GaloisPointComparison.relativeRationalExtend` transports relative coefficient
extension through the multiplicative equivalences between coefficient points
and rational points of the actual base changes. Its comparison, injectivity and
automorphism-compatibility theorems are proved explicitly.
`relativeRationalExtend_fst` also identifies its projection to `G` with
composition by the field-inclusion spectrum map. Applying these equivalences
to the coefficient construction gives `rationalValue` and the stated rational
recovery and cocycle laws.

Finally, `exists_finite_galois_trivial` starts from a finite intermediate field
`E₀` on whose fixing subgroup `c` is one. It takes the normal closure of `E₀`
inside `K`. Mathlib supplies its finite dimension and normality; separability is
inherited from `K/k`, giving a finite Galois extension. Its fixing subgroup is
contained in that of `E₀`, so triviality persists.
`exists_finite_rational_cocycle` combines this field with the constructed
`rationalValue`. Its conclusion includes finite dimension, the actual Galois
instance, the recovered cocycle identity and exact recovery of every original
value. It uses precisely the supplied finite-subextension triviality premise.

This module supplies a finite field and finite cocycle values for further
integral-model descent. It does not construct a smooth stabilizer model, descend
an integral semilinear family, construct a reductive residue quotient, or prove
the chamber-quotient statement `UnramifiedTwistedChamberQuotientStatement` that
it serves.
