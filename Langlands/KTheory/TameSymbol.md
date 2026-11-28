# The tame pairing of an integer-valued valuation

Let `v : Valuation F ℤᵐ⁰` be a valuation on a field. Write `A` for
`v.valuationSubring` and `κ` for `IsLocalRing.ResidueField A`. The order
`valuationOrder v a` of `a : Fˣ` is `-WithZero.log (v (a : F))`. Thus
valuation `WithZero.exp (-1)` gives order one. For a supplied
`Langlands.LocalFieldData` datum `T`, the expression
`valuationOrder T.discreteValuation a` agrees definitionally with
`T.ord (a : F)`.

For orders \(r=\operatorname{ord}_v(a)\) and \(s=\operatorname{ord}_v(b)\),
`tameSymbolUnit v a b` is the element of `A.unitGroup` with underlying
field unit \((-1)^{rs}a^sb^{-r}\). The lemmas `coe_tameSymbolUnit` and
`val_tameSymbolUnit` give the formula in `Fˣ` and `F` respectively.
The proof applies additivity of order, the integer-power rule and
\(\operatorname{ord}_v(-1)=0\), giving order \(sr-rs=0\). Since the
valuation of a field unit is nonzero, `WithZero.exp_log` identifies order
zero with valuation one. Mathlib's `Valuation.mem_unitGroup_iff` then
certifies membership in `A.unitGroup`.

`tameSymbol v a b : κˣ` applies `ValuationSubring.unitGroupToResidueFieldUnits`
to this unit. The formula is defined directly from `v`, including when `v`
is surjective as in the normalized discrete case. All powers are integer
powers, and the construction and evaluations apply in residue
characteristic two as well.

For `u : A.unitGroup`, the first-argument evaluation
`tameSymbol_unitGroup_left` gives \(\overline{u}^{\operatorname{ord}_v(b)}\).
The sign and the power of the second entry both have exponent zero, and
reduction preserves the remaining integer power. Consequently
`tameSymbol_unitGroup_unitGroup` gives one when both entries are valuation-ring
units. With `π : Fˣ` of order one, `tameSymbol_unitGroup_uniformizer` gives
\(\overline{u}\) on \((u,\pi)\), in Milnor's orientation.

## Sources

- John Milnor, *Introduction to Algebraic K-Theory* (1971), Lemma 11.5,
  printed p. 98, PDF p. 102, gives the signed quotient and its unit calculation.
  Registered as `milnor-1971-introduction-algebraic-k-theory` with SHA-256
  `cf793856c54a428593940eef304c4cec35478966b8b8525ccfc153473f3d157a`.
- Hyman Bass and John Tate, *The Milnor ring of a global field* (1973),
  Proposition 4.5(c–e), typescript pp. 22–23, PDF pp. 24–25, gives the
  unit-first evaluation in degree two, the independence of the uniformizer
  and the same signed quotient. Registered as `bass-tate-1973-milnor-ring-global-field`
  with SHA-256 `e1ac8c15b1d5c1ef9d1512e7aec48720aa1ce97880e5b55e002d9617b361654f`.
