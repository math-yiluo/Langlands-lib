# Transport of reduced framing squares through source changes

This is internal content derived from the existing formal comparison and
normalized framing constructions. It adds no original-literature assertion.

Let `X,Y` be framed atlases over the same fixed Nilp object, and let `e` identify
their stored residue maps. Let `c,d` be two specified actual comparisons of their
reduced targets. Suppose `hL` identifies their left finer covers and `hR`
identifies their right finer covers. The selected original source charts may
still differ. The existing `orderSourceIso` maps give corrections `sL` from the
left refinement of `c` to that of `d`, and `sR` on the right.

`ReducedFramingSquare.of_source_square` assumes the actual equation of whole
order-linear formal isomorphisms

```text
sL.trans d.coordinateIso = c.coordinateIso.trans sR.
```

Given `ReducedFramingSquare e c`, it proves `ReducedFramingSquare e d` for that
same specified comparison `d`. Thus the predicate is transported along a
supplied concrete formal-map square, without replacing either comparison by an
unspecified representative or assuming an equality of their selected sources.

For each test algebra and invertible finer generator, the proof maps the
supplied formal-isomorphism equation to rational quasi-isogenies and then
evaluates it on the actual chart. The existing `ofIso_trans` and `onChart_trans`
identities identify its edges with the two rational source corrections and the
two comparison chart maps. The existing normalized framing source-choice laws
identify each original framing followed by its correction with the framing
for `d`. Associativity and the framing equation for `c` then prove the framing
equation for `d`. All these equalities are in whole rational formal-map tensors;
there is no inference from equal point families to equal formal maps.

`sourceTransportedReducedComparison` retains `d` itself as a subtype value,
together with the transported `ReducedFramingSquare e d` certificate. Its
underlying comparison is exactly the supplied `d`.

The construction retains the supplied local field, central division algebra,
embedded subfield, coefficient ring, residue field, height-certified fixed
frame, one fixed Nilp object and the existing test universes. Coordinate types
are those of the framed targets. Covers may be different or infinite, and
source choices need not agree. Both finer-cover equalities, the actual formal
source square and the input reduced framing square are hypotheses.

Compatibility of quotient reduction with refinement or composition of original
target comparisons, direct original framed comparison composition, finite-chain
collapse, varying-base framed functoriality, actions and representability remain
separate obligations. This transport result does not supply the formal source
square needed for those applications.
