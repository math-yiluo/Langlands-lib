# Frobenius powers of finite regular coordinate subspaces

This derived construction relates powers of actual coordinate functions to the
Frobenius power of an actual matrix representation. It uses the existing
coalgebra basis matrix and characteristic-power ring homomorphism. It invokes
no structural existence theorem about reductive groups.

For a field `k`, a commutative `k`-algebra `B`, natural numbers `p,e` and a
subspace `V` of `B`, `Chevalley.frobeniusCoordinateSpan p e V` is the `k`-span of
`v^(p^e)` for all `v` in `V`. Its definition and the generator membership lemma
need no characteristic hypothesis. If `k` has exponential characteristic `p`,
`pow_eq_sum_basis` expands such a power in the powers of a supplied finite basis,
with the coefficients raised to the same power. Consequently the intrinsic
span equals the span of those powered basis vectors and is finite when `V` is
finite. These conclusions do not require reducedness or perfectness.

If `k` is also perfect at `p` and `B` is reduced, the powered basis vectors are
linearly independent. The proof transfers independence through the additive
power map, using surjectivity of iterated Frobenius on scalars and injectivity
of the power map on `B`: an element in its kernel is nilpotent and hence zero.
`frobeniusCoordinateBasis` is the resulting basis of the intrinsic powered
span, indexed by the same `Fin d` as the original basis. Its coercion to `B` is
exactly the corresponding powered original basis vector. No choice of roots
in `B`, and no perfectness assumption on `B`, is needed.

For a commutative bialgebra `B`, let `V` be stable under every right contraction
`rightAct f`, and let `b` be a basis indexed by `Fin d`. In exponential
characteristic `p`, `comul_basis_pow` proves

`Delta((b j)^q) = sum_i (b i)^q tensor (subspaceMatrix V b i j)^q`,

where `q=p^e`. It applies the characteristic-power ring homomorphism to the
existing finite coaction expansion. Tensor products of powers are the powers
of the corresponding pure tensors. Contracting the second factor gives
`rightAct_basis_pow`, and span generation gives stability of the entire
powered span. These results require neither perfectness nor reducedness.
With both additional hypotheses, contracting the first factor by a coordinate
functional of the powered basis proves that its `subspaceMatrix` is the
entrywise `q`th power of the original matrix.

`frobeniusRegularRepresentation` applies the existing actual regular
representation constructor to this powered span and basis. Its parameters are
a field of exponential characteristic `p` perfect at `p`, a reduced
commutative coordinate algebra corepresenting a group-valued functor, and a
supplied finite regular subspace and basis. The universal matrix is the powered
coaction matrix. The existing matrix Frobenius representation has the same
universal matrix. `intertwines_frobeniusRegularRepresentation` therefore proves
that the identity matrix intertwines the two representations on every affine
algebra test, using the existing universal-point criterion and naturality.

`affineFrobeniusRegularRepresentation` transports that construction to an
arbitrary supplied affine reduced group scheme over the same perfect field.
Reducedness of its chosen coordinate algebra follows from the actual group
scheme isomorphism with its relative spectrum and the reduced-spectrum
criterion. The transported identity intertwiner and
`affineFrobeniusRegularRepresentation_affineMatrix` show that its matrix on every
affine test algebra is the entrywise `q`th power of the original actual regular
representation matrix. The test algebras may be nonreduced; the reducedness
hypothesis concerns the represented group scheme.

The covariance lemmas have a separate, more general scope. For any algebra map
`r:B -> C`, a coordinate covariant with weight `chi` has its `n`th power
covariant with weight `chi^n`, for every natural `n`. This follows from
multiplicativity of comultiplication and of the tensor algebra map. The span of
the `q`th powers is thus contained in the covariance subspace of weight
`chi^q`, with no characteristic, reducedness, perfectness or group-like
hypothesis on `chi`. The final `AffineCoordinates` adapter states the same
containment for an actual affine group morphism. Existing tensor covariance
comparisons retain its meaning on every relative scheme test.

The powered span is only a subspace of the entire covariance space at the new
weight. No equality with that whole space, irreducibility, tensor-product
irreducibility or general Steinberg existence is asserted here. Those are
separate obligations for `SteinbergBigCellStatement`.
