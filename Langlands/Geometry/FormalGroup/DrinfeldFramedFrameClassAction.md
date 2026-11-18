# Original framed comparisons under integral fixed-frame automorphisms

`Comparison.frameAct` retains exactly the original target comparison and
residue equality, and proves the original all-test framing certificate after
inverse precomposition by an actual integral full-order frame automorphism.
It does not introduce a new comparison relation or require an extra framing
compatibility premise.

The implemented proof first normalizes restriction of an actual global
integral formal map: `globalOrderChartIso_natural` identifies the whole
normalized chart map with its original coefficient-extended global map, by
complete formal-series extensionality. This gives `chartFraming_frameAct`
and `refinedChartFraming_frameAct`: on every test and original refinement,
the new normalized framing is the inverse actual coefficient-extended frame
automorphism followed by the old normalized framing.

`frameAutomorphismTestIso_residue_square` proves that those actual source
automorphisms commute with the exact residue-forced integral frame map.
Eliminating the stored residue-map equality reduces it to actual integral
identity composition. Rationalizing that equation and pasting it with the
original supplied framing square proves `FramingSquare.frameAct`.

`ComparisonClass.frameAct` descends through the same original finite-chain
framed comparison quotient using those constructed actual comparisons.
Quotient induction carries the already proved representative identity and
multiplication equations to the classes and packages a group action. The
actual descended residue map, original height-certified target class and
quotient-reduced target class are fixed by this action.

The generic normalization lemma has separate scalar, acting and coefficient
universes and arbitrary finite coordinate types. The framed assertions retain
the local-field, central finite-dimensional division-algebra, embedded-field,
coefficient/residue-field and fixed height-certified-frame assumptions, with
Nilp universes {v,u}. Covers may be infinite. All quasi-isogeny equations are
whole actual tensor equations or their mapped restrictions; no global tensor
is detected by point evaluations or chartwise equality.

This internal action uses integral full-order frame automorphisms. Naturality
under varying Nilp bases remains subsequent work. No identification with a
matrix group, full Drinfeld product-group action, Frobenius/height formula,
representability or universal object is asserted.
