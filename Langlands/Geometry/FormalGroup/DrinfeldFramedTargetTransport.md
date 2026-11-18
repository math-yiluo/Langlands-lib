# Actual target-isomorphism transport of framed formal atlases

This internal construction replaces the target of an actual height-zero framed
representative through a specified integral full-order atlas isomorphism. It
constructs a comparison in the original framed relation and proves equality in
its existing comparison-class quotient.

The ambient hypotheses are the existing local field, central finite-dimensional
division algebra, embedded field, residue field, fixed height-certified special
frame `Φ`, and Nilp object `A`. Given a representative `X`, a height-certified
special atlas `Y` over `A`, an equality `h` of their original target covers, and
an actual integral full-order isomorphism `t : X.target.val.Iso Y.val h`, all
objects and both formal inverse maps are supplied actual formal atlases and
maps. No representing or universal object is an input.

`targetTransportSourceIso` identifies the same extended fixed frame on the two
equal reduced target covers. It is the actual cover-equality isomorphism and has
complete identity formal series on every coefficient test, as proved in
`targetTransportSourceIso_hom_coordinates`.

`transportTarget` retains `X.residueMap`, stores exactly the target `Y`, and
transports the whole global rational framing through this source isomorphism
and the actual quotient reduction of `t`. Its forward framing is the original
framing precomposed with the inverse source comparison and postcomposed with
the reduced target map. Its inverse is transported at the same time. Actual
local kernel-rank height zero follows from the existing integral-isomorphism
transport theorem for rational atlas maps; it is not an additional premise.

`transportTarget_rho` proves the whole global rational framing square. It
unfolds the specified transport, reassociates actual global tensor
quasi-isogenies, and cancels the two inverse source maps. No equality of global
rational tensors is inferred from chartwise or pointwise equality.

`targetTransportTargetComparison` is exactly the original comparison induced
by `t` on the reflexive common refinement. `targetTransportComparison` retains
this comparison, with residue equality by definition. The existing
`ReducedFramingSquare.of_induced_global_square` applies to the proved whole
framing square, the source's complete identity series, and the inducing
certificate for the exact reduced target comparison. It therefore proves the
original all-test framing certificate with no extra compatibility premise.
`comparisonClassOf_transportTarget` then gives equality in the same original
framed comparison quotient, by its defining comparison-to-class map.

The provenance is internal: this is a formal consequence of actual integral
isomorphism transport, actual quotient reduction, and the original framed
comparison definition. It is reusable for integral changes of target, including
integer-unit conjugation. It does not identify a matrix group of rational frame
endomorphisms, construct the full division-group or Frobenius action, or prove
representability.
