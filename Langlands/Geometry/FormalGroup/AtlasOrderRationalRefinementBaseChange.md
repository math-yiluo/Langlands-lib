# Actual rational chart maps for refinement and coefficient extension

This is internal coherence for the existing actual formal atlases with full
order action. It uses the already constructed `orderBaseChangeIso`; it makes
no new representability or moduli claim.

Let `q` refine an atlas `X` with order action `E`, and extend coefficients from
`R` to a supplied commutative `R`-algebra `S`. A generator of the extended finer
cover can acquire different selected original charts in the two constructions.
`baseLeftOrderChartIso` identifies the extended refined chart with the original
chart selected before extension. `baseRightOrderChartIso` identifies the refined
extended chart with the original chart selected after extension. Both maps are
actual order-linear formal isomorphisms on every supplied `S`-algebra test.

`orderBaseChangeQuasi` evaluates the rationalization of the specified
`orderBaseChangeIso` on that test chart. `orderBaseChangeQuasi_chart` proves
that this map followed by the second identification equals the first
identification followed by the actual original transition. The proof compares
the full coordinate series using `baseChangeChartIso_coordinates` and then uses
compatibility of rationalization with composition. `orderBaseChangeChartSquare`
retains these four actual maps and their equation as commuting-square data.

The coefficient ring and order are arbitrary subject to the displayed ring
and algebra instances. Rationalization additionally retains an integral domain
`O`, a fraction field `F`, and the existing finite coordinate type. No
injectivity of the coefficient map, preservation of selected charts, finiteness
of the cover, or pointwise detection of formal maps is assumed.
