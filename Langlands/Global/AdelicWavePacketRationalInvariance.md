# Rational invariance of Eisenstein continuations and wave packets

`Langlands.Global.EisensteinContinuationRationalInvarianceStatement`
supplies the pointwise left `G(F)`-invariance needed to descend the
wave packets of `LocalWavePacketInnerProductStatement` to the rational
quotient and to apply pointwise truncation exhaustion. Use the actual
rational parabolic and Levi presentation, geometric unipotent radical, and
compact Iwasawa subgroup of the Eisenstein-series formula. The input
function is invariant under `U(𝔸) M(F)` and need not satisfy the other
conditions for an automorphic form. A pointwise continuation must be
meromorphic in complex linear coordinates for every adelic argument, with
a common holomorphy domain `D`, and agree with the defining sum for
sufficiently regular real part. Then every parameter in `D` gives a
left-rational-invariant function. The statement assumes continuations; it
does not construct them.

## Provenance and implemented proof

Derived from the Eisenstein sum and wave packet definitions in E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series*, Clay Math. Proc. 13 (2011), pp. 309–331, §2, p. 311 and §3, p. 314
(PDF pp. 320 and 323 in the registered source
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`). The proof
uses the following steps.

1. `eisensteinSeries_leftRationalInvariant` reindexes the rational right-coset
   sum by right multiplication with the translating rational point. The
   twist takes the same value for each representative of a coset, by the
   published `eisensteinTerm_eq_of_representative`. The identity also holds
   with the Library's total sum convention in the nonsummable case.
2. The regular region is open in a complex linear chart by the strict
   inequalities defining it. To show it is nonempty for each threshold,
   scale the positive split-component cocharacter evaluation so that every
   positive root evaluation exceeds the threshold. The nondegenerate
   Weyl-induced form represents that functional by a real character.
   Pull the character back to a parameter using the surjectivity of
   restriction to the Levi (the Levi retraction), rational restriction to
   its split component, real base change, and the real-part map. This
   adapts the private regular-region argument in the Library's
   `AdelicIntertwiningCocycleReduction` (itself based on the helpers of
   `AdelicEisensteinRegularRegion`), without requiring injectivity of restriction to the Levi.
3. For fixed adelic arguments `g` and `δg`, apply the scalar identity
   theorem `IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open` to the two
   evaluations of the continuation. The reindexing identity on the regular
   region therefore holds on all of `D`, not only on a dense subset.
4. `packetIntegral_leftRationalInvariant` applies the resulting identity to
   the finite integrand sum: each coefficient is either zero or evaluated
   at a parameter in `D`. Integrating the pointwise equality gives left
   rational invariance of the packet. No growth, smoothness, or
   integrability of the packet is claimed at this step. In the local target,
   the support condition follows from vanishing outside the supplied
   compact set and regularity on its parameter image.

This proves only rational invariance, not the automorphic smoothness,
finite-type, or growth conclusions of the Library's separate pointwise
continuation automorphy statement.
