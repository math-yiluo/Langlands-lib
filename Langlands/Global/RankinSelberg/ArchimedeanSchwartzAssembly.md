# Assembly of archimedean and finite Schwartz factors

This internal construction supports the equal-rank archimedean factorization
problem. It combines arbitrary real and complex Schwartz functions with locally
constant compactly supported finite-place functions. It proves neither the
Whittaker-integral factorization nor the Fourier factorization.

Fix a number field `F`, a natural number `n`, and a finite set `S` of finite
places. For each real place choose a complex-valued Schwartz function `ΦR v` on
`Fin n → ℝ`; for each complex place choose a Schwartz function `ΦC w` on
`Fin n → ℂ`. For each finite place let `Φv v` be a complex-valued function on
`Fin n → FiniteCompletion F v`. The finite factors at places outside `S` are
unused.

`localRowDomain F n` indexes the local row spaces by the disjoint union of real
and complex places. The real continuous linear equivalence
`archimedeanRowEquiv F n` sends a mixed row `x` to its local rows
`j ↦ (x j).1 v` and `j ↦ (x j).2 w`. Its inverse reassembles the two coordinate
families for each row entry. The two-sided inverse and linearity laws are
coordinate identities; continuity follows from continuity of coordinate
projections and products. Pulling back `finiteTensor` along this equivalence
gives the Schwartz function `archimedeanTensor F n ΦR ΦC`. The lemma
`archimedeanTensor_apply` gives its value as the product of the real and complex
factors. All products include the possibility of an empty set of places.

The primary definition
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor.restrictedTensor`
has value

$$
\mathbf 1_{\mathrm{integralOutside}(S)}(x)
\left(\prod_{v\text{ real}}\Phi_{R,v}(x_v)\right)
\left(\prod_{w\text{ complex}}\Phi_{C,w}(x_w)\right)
\left(\prod_{v\in S}\Phi_v(x_v)\right).
$$

Here the indicator acts on the whole function, so the function is zero whenever
some finite coordinate outside `S` is nonintegral. The theorem
`restrictedTensor_eq` states this formula using the Library's
`realRowCoordinates`, `complexRowCoordinates` and `localCoordinates`, and the
subtype product over `S`. The scalar in the formula is exactly one.

If each `Φv v` for `v ∈ S` is locally constant and compactly supported,
`restrictedTensor_mem_schwartzBruhat` proves that this tensor belongs to
`schwartzBruhat F n`. Its proof first regards the function as a generator of
`restrictedSchwartzBruhat F n`, then applies the published theorem
`SchwartzBruhatProof.restricted_le_schwartzBruhat`.

Without any regularity assumption on the finite factors,
`restrictedTensor_isStandardOutside` proves `IsStandardOutside F n S`: the
indicator gives vanishing off the prescribed set, and on the set the formula
depends only on the archimedean coordinates and the local coordinates at `S`.
The proof uses equality of these coordinates and equality of finite products.

All constructions allow `n = 0` and impose no restriction on the signature of
`F`. In particular, their intended equal-rank application `n = r + 1` includes
`r = 0`.

This module is derived implementation infrastructure. It combines the generic
Schwartz tensor construction with the existing coordinate and Schwartz–Bruhat
definitions. It introduces no new literature assertion or analytic premise.
The exact product formula for the global Fourier transform, the representation
theory of Whittaker pure tensors, quotient-measure comparison and simultaneous
nonvanishing remain separate obligations of the factorization task.
