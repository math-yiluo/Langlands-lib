# Original framed comparison for composition of Nilp-base extension

`baseChangeCompositionComparison X f g` constructs an actual comparison in
the original framed relation from `(X.baseChange f).baseChange g` to
`X.baseChange (f ≫ g)`. It retains exactly the original
`X.target.val.baseAlongCompComparison` for the two actual Nilp scalar maps,
including the specified refinements and actual formal isomorphism. Its
residue equality is the forced composition residue equation. Its framing
field proves the original all-test `FramingSquare`, with no new compatibility
or framing premise.

The specified source map has complete identity formal series. Supplied
coefficient extension preserves this certificate for actual integral atlas
maps. The corrected coefficient-composition map also has identity series
when all original transition series do; the proof uses the existing complete
coefficient-composition chart formula and equality transport, rather than
eliminating a large dependent composite equality. The original source atlas
comes from a global fixed frame and has complete identity transition series.
The actual integral inverse law and composition give the certificate for
the full specified source composite.

The existing original target coefficient-composition comparison is induced
by its actual atlas isomorphism, by the restriction construction. Quotient
reduction retains exactly that comparison and its complete inducing
certificate. Applying `ReducedFramingSquare.of_induced_global_square` to
the previously proved whole framing tensor square, the source series
certificate and the target inducing certificate proves its original refined
framing field. Independent selected parent charts and the actual test
refinement equations are retained throughout.

The resulting original comparison proves
`comparisonClassOf_baseChange_comp`. Quotient induction gives
`ComparisonClass.baseChange_comp` for the same original framed chain
quotient. Combined with the identity law, these are the laws needed for the
subsequent actual Nilp functor.

The integral auxiliary lemmas use arbitrary commutative coefficient rings,
an acting ring in a separate universe, and an arbitrary finite coordinate
type; they require no domain hypothesis. The framed construction retains
the local-field and central finite-dimensional division-algebra hypotheses,
the embedded field, coefficient/residue fields, fixed height-certified frame,
and explicit Nilp universes {v,u}. Covers may be infinite and coefficient
maps may merge generators. This is internal coherence. No global rational
tensor equality is inferred from charts or points, and no representing or
universal object is assumed.
