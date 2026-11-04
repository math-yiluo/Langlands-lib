# Coherence and reversal of arbitrary bounded target-chart changes

For an arbitrary actual indexed affinoid atlas over a complete ultrametric
normed field, this internal unit proves composition of the universal bounded
chart-change law through three arbitrary original charts. No saturation or
domain representation of the image is assumed.

`chart_eq_of_factor` expresses the ambient chart equation of a bounded map
factored through an original subchart, after any bounded affinoid coefficient
test. The equation follows directly from the original atlas restriction
equation and the given equality of bounded factorizations.

`IsMapChartChange.trans` takes the universal laws for `φ → ψ` from chart `i` to
`j` and for `ψ → χ` from chart `j` to `k`, together with the containment of the
entire image of `φ` in chart `j`. To test the law from `i` to `k`, start with an
arbitrary affinoid test factoring through a common subchart `m` of `i` and `k`.
Its image lies in `j` by `chart_eq_of_factor`. The actual finite common-chart
cover for `m` and `j` pulls back to a cover of the whole test spectrum. Each
cover chart is contained in `m` and `j`, hence also in `i` and `k`. The two
universal laws apply successively on these actual quotient algebras.
Original restriction composition and the pullback structural square identify
the final restrictions. Finite-cover algebra separation proves the global
bounded-map equation.

`changeMapChart_trans` applies this transitivity to the constructed changes and
uses their universal uniqueness theorem: changing from `i` to `j` and then to
`k` equals the direct change from `i` to `k` as a complete bounded map. Its
explicit image hypotheses apply to the direct and iterated changes.
`reverseMapChartChange` constructs the change back to the original chart; the
proved ambient equation supplies its image condition. `reverseMapChartChange_eq`
uses transitivity and same-chart recovery to recover the original bounded map.

The provenance is internal, from actual finite inverse-image covers, the
universal law established in `AtlasMapChartChangeNaturality`, and original
atlas restriction equations. No algebra-map equality is inferred merely from
spectrum-point equality, and no new literature assertion is attributed here.
Empty spectra, empty covers and nonreduced algebras remain included. This unit
does not construct strong morphism composition or analytic sites.
