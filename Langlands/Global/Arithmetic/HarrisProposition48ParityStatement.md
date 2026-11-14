# Parity correction and untwisting inputs

`Langlands.Global.Harris.Proposition48ParityNormalizationStatement`
and `Proposition48ParityUntwistStatement` isolate two derived obligations
in the Proposition 4.8 proof route. Their conjunction
`Proposition48ParityTransportStatement.{uF,uV}` is a focused proof target.
No proof is supplied.

The normalization statement quantifies over every bundled problem valid
at an explicitly supplied parity `b`. It supplies a genuine Hecke
character `ν` of the base field and new local characters on the same
local extension. `IsParityNormalization` requires conjugate inversion,
the correcting infinity parity, trivial correction if the parities agree,
and all original validity conditions for the character
`ξ · (ν ∘ N_{E'/E})`. Thus it includes preservation of relative regularity,
the actual local components and general position. It supplies no
automorphic existence conclusion.

The untwisting statement takes such a normalization and a supplied
solution class for its corrected character. It realizes that very class
as `T.isoClass`, and supplies a cuspidal realization `S` for the raw
character, with conjugate self-duality and the same designated
supercuspidal place. The required determinant relation is on actual
automorphic realizations: `T` is obtained from `S` by multiplication by
`ν(det g)`. The normalized realization is regular algebraic. No regular
algebraicity of the raw realization is asserted when the parity differs.

These statements make explicit an additional construction in this
formalization route. Harris (1998), printed p.195, uses algebraicity after
the rank-dependent half-norm twist; p.191 records half-integral absolute
value twists; Proposition 4.8, pp.201–203, changes constituent ranks
through the induction. These passages motivate the obligation but do not
state this particular correcting-character theorem. A proof must
construct a conjugate-inverse CM base character of the specified parity,
with the trivial choice when possible, then verify all arithmetic and
automorphic transport. The imaginary quadratic subfield already included
in the datum is available for the character construction. The existence
claim is not being attributed verbatim to Harris.

In particular, a half-norm twist alone need not preserve conjugate
self-duality. These statements instead retain that property explicitly
and use an actual base character. They do not infer unitarity of the
central character for cyclic transfer; the transfer bridge must supply
that separate predicate. Nor do they assert compatibility of a
coefficient representation without a named compatibility and twist
transport input.

The top reduction must list the two named statements separately among
its explicit premises. A proof of the conjunction supplies them both.
Their scope is arbitrary local-field universe `uF` and local
factor-carrier universe `uV`, with number fields in `Type 0`.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`: p.195 normalization; p.191 remark
(TeX `math_9611226v1.tex`, lines 866–875); Proposition 4.8 proof,
pp.201–203 (lines 1574–1675). The split into correction and actual
determinant untwisting is internal derived content.
