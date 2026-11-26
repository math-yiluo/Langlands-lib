# Actual integral order operators in normalized Harris frames

The fixed Harris integral order acts on the fixed integral source span
by the restriction `harrisIntegralSourceOrderOperator` of
`CentralSimpleUnitaryData.harrisIntegralAdeleOrderAction`. The
restriction uses `CentralSimpleUnitaryData.harrisIntegralAdeleOrderAction_mem`.

For the Harris number fields, algebra and signature charts, fix a
positive-auxiliary polarized action on a quasi-separated scheme and a
normalized Weil frame at a field-valued point. Use the relative finite
Weil transitions and the comparison of rational profinite integers
with finite adeles. A supplied `IntegralActionRestriction` is an
actual integral order action on this same family with its given
rationalization.

`harrisIntegralFrameFull_order` identifies the map of the actual
endomorphism on the full integral Tate group with the fixed source
operator through `harrisIntegralFrameFull`. The proof uses
`GroupScheme.Tate.full_toRational_injective` and the formula
`harrisIntegralFrameFull_toRational`. On rationalizing, functoriality
of Tate maps and the restriction's agreement reduce the equation to
`harrisIntegralFrame_order` for the original rational frame.
