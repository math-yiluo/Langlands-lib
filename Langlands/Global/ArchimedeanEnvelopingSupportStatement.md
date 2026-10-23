# Support of genuine enveloping differential operators

This is an internal locality prerequisite for convolution smoothing on the
published actual infinite adelic matrix group. `EnvelopingSupportStatement K n`
in namespace `Langlands.Global.ArchimedeanGL` states that for every element of
the complex enveloping algebra and every member of the actual smooth-function
space, the topological support of its genuine enveloping derivative is contained
in the original topological support. Here `tsupport` is the closure of the set
where the complex function is nonzero. The statement concerns the existing
`envelopingAction`, not a supplied abstract action.

`EnvelopingCompactSupportStatement K n` states the resulting preservation of
`HasCompactSupport`. The implemented conditional theorem
`envelopingCompactSupport_of_support` uses closedness of topological support and
the asserted inclusion to regard the derivative support as a closed subset of
the original compact support. Neither Prop definition is itself a proof of
locality. Both retain arbitrary number fields, carrier universe, and natural
ranks, including zero. They require no automorphic, growth, compact-finiteness,
or center-finiteness hypotheses.

This is internal differential-calculus infrastructure: the intended proof
uses local vanishing outside support, transports that vanishing through the
published open units chart, and uses locality of the real Fréchet derivative.
Complexification and algebra sums/products then extend the inclusion to every
enveloping operator. No original-literature theorem is being quoted or
reinterpreted by these two propositions. Their downstream use is to ensure that
the derivatives of a compact smooth reproducing kernel can be inputs to the
separate compact-kernel convolution bound. Existence of a reproducing kernel
and differentiation under the integral are independent obligations.
