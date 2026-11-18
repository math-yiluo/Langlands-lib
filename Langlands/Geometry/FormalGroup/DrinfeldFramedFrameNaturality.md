# Varying-Nilp naturality of integral fixed-frame automorphisms

`frameAutomorphismActionHom` is a group homomorphism from the actual integral
full-order fixed-frame automorphism group to the group of natural
automorphisms of `comparisonClassFunctor Φ`. Its evaluation is exactly the
existing action on the same original framed comparison quotient. Its inverse
natural transformation uses the same actual inverse integral frame map.

The implemented proof first establishes the integral source naturality square
through the actual `quotientFrameBaseChangeIso`. The two actual source
automorphisms have the same complete series after base extension: coefficient
extension retains the original selected chart map, the global restriction
formula retains the full coefficient-extended frame series, and composition
of coefficient ring maps identifies the two routes. The quotient-frame
comparison has complete identity series, so integral formal-map
extensionality gives the actual whole integral square.

`frameAct_baseChange_rho` uses that integral square on whole rational tensors.
Extend the original inverse-precomposition formula by the actual quotient
scalar map, rationalize the inverse integral source square, and use tensor
associativity to compare the two stored framings through the same actual
target correction. No tensor equality is inferred from local data.

The target and residue maps agree exactly. Equality of those stored data and
the whole framing tensor gives equality of framed representatives; the local
height field is a proof certificate. Quotient induction then proves
`ComparisonClass.frameAct_baseChange`. It supplies the naturality field of
`frameAutomorphismNatTrans`; actual inverse group laws give
`frameAutomorphismNatIso`. The proved class identity and multiplication laws
show the construction is the stated group homomorphism to natural
automorphisms, with ordinary functional group multiplication.

The local-field, central finite-dimensional division-algebra, embedded-field,
coefficient/residue-field and fixed height-certified-frame assumptions are
retained, with explicit Nilp universes {v,u}. Covers may be infinite and
coefficient maps may merge principal generators. This is an internal action
by actual integral full-order frame automorphisms. Identification with a
matrix group, the full Drinfeld product-group/Frobenius/height action,
representability and universal objects remain further obligations.
