# Factor transport for one positive block

Author: Worker 20.

This internal module specializes the published single-block evaluation
equivalence to the successor-rank notation used by Rankin–Selberg
multiplicativity. It also transports the existing symmetric gamma and
L-polynomial certificate relations across that equivalence.

## Construction

For a prime `p`, a canonical p-adic field `F : PadicField.{uF} p`,
`m : Fin 1 → ℕ`, complex modules `W i : Type uW`, and representations
`σ i` of `GL_(m i + 1)(F)`, the construction

```lean
Langlands.RankinSelberg.succSingleBlockNormalizedProductEquiv F m σ hσ
```

is an actual representation equivalence from

```lean
F.canonicalNormalizedProductInduced
  (succBlockShape m (show ∑ i, (m i + 1) = m 0 + 1 by simp)) σ
```

to `σ 0`. Its only representation hypothesis is that every `σ i` is
smooth for the canonical field topology and the induced general linear
group topology. The field universe `uF` and coefficient universe `uW`
remain independent. The source carrier has universe `max uF uW`,
and the target has universe `uW`.

The construction reuses
`PadicField.TopologicalData.singleBlockNormalizedProductEquiv` from
`Langlands.Representation.Induction.SingleBlock`. Its result initially
pulls `σ 0` back along the matrix reindexing associated to the equality
between the unique block rank and the ambient rank. Here both ranks are
`m 0 + 1`. Entrywise extensionality proves that this reindexing fixes
every matrix. An identity linear equivalence therefore intertwines the
pulled-back action with `σ 0`. Composing the two equivalences gives the
stated construction. The maps on vectors are those of the imported
evaluation equivalence, followed by the identity; invertibility and
equivariance are part of the resulting `Representation.Equiv`.

## Certificate relations

Fix a unitary additive character `ψ`, an additive Haar measure `ν`,
and a representation `π` of `GL_(r+1)(F)` on an independent carrier
`V : Type uV`. For any `t` and proof
`h : ∑ i, (m i + 1) = t + 1`, the lemmas

- `singleBlock_gamma_iff` identify the symmetric gamma relation for
  `π` and the actual induced representation with that for `π` and `σ 0`,
  at the same supplied rational function `G`.
- `singleBlock_L_iff` identify the symmetric L-polynomial relations
  for those pairs at the same supplied polynomial `P`.

Both are in `Langlands.RankinSelberg`. The proofs simplify the one-term
sum in `h`, cancel the successor to obtain `t = m 0`, and eliminate
that equality. They then apply the corresponding published
`IsPadicSymmetricGammaFactor.congr_equiv` or
`IsPadicSymmetricLPolynomial.congr_equiv`, with the identity equivalence
on `π` and the constructed equivalence on the induced representation.
These imported lemmas cover both rank orders and independent carrier
universes. The measure is unchanged. No self-duality hypothesis is
needed for this transport; in the multiplicativity application one
uses the supplied self-dual measure's underlying Haar measure.

## Provenance and scope

The module is derived entirely from the published actual normalized
induction, single-block evaluation, successor block shape, and factor
equivalence lemmas in its imports. It introduces no new literature
claim and does not modify any imported Lean/Markdown pair.

These results supply the representation and certificate transport for
the one-block case. They do not assert the existence of a gamma factor
or L-polynomial, a closed multiplicativity theorem, or a comparison
between inductions with two or more blocks. Smoothness is sufficient;
neither irreducibility nor finite-dimensionality is assumed. For the
parent theorem, smoothness follows from the admissibility clause of
each block's full Whittaker-type hypothesis, while factor existence
remains a separate analytic obligation.
