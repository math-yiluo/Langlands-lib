# Integral realization of finite actual-character sign patterns

This internal helper applies the existing integral sign-realization theorem to
actual character and cocharacter lattices of a commutative group scheme over a
field. The field may have arbitrary universe `u`. No split-torus, finite-rank or
smoothness hypothesis is required.

For a finite indexed family of characters `α i` and a vector `v` in
`RealTorusSpace.V T = ℝ ⊗[ℤ] cocharacterLattice T`,
`exists_cocharacter_sign_eq` supplies a genuine integral cocharacter `μ` with

```text
sign (latticePairing T (α i) μ) = sign (eval T (α i) v)
```

for every index. Thus strictly positive, zero and strictly negative evaluations
are all retained. `exists_cocharacter_sign_eq_on_finite` gives the same statement
for an arbitrary finite set of characters, including the empty set.
`signRealizingCocharacter s hs v` chooses this genuine integral cocharacter;
`signRealizingCocharacter_spec` states its sign equality for each member of `s`.

The proof uses `RootFaceCone.exists_int_sign_realization` from
`Langlands.LinearAlgebra.RootFaceReflection`. It indexes by the original finite
index set times `Bool`, taking both the integral lattice-pairing functional and
its negative, with real scalar extensions `eval` and `-eval`. The pure-tensor
compatibility is exactly `eval_tmul`. Applying integral realization to both
signs gives equivalences for strict positivity and strict negativity, which
identify the three-valued signs. The finite-set version uses its subtype as the
finite index set. This is the same two-functional technique used inside
`FiniteCharacterBoundaryCocharacter.exists_boundaryCocharacter`, extracted here
as a reusable sign theorem; it needs neither a supporting cone nor duality.

This helper supplies integral sign realization only. It does not assert that a
cocharacter ray reaches a prescribed affine facet or that a special-fibre image
is a parabolic subgroup. Those comparisons remain separate obligations of the
facet-model application. Its provenance is internal derivation from the named
existing Lean lemmas, with no new source-dependent mathematical assertion.
