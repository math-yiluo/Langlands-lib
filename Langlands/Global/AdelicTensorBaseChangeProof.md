# The canonical full adelic tensor comparison in both characteristics

`adelicTensorBaseChangeProof` proves exactly the proposition
`Langlands.Global.AdelicTensorBaseChangeStatement` in an arbitrary universe.
It conjoins the already proved bijectivity of the two original canonical
algebra homomorphisms.

The function-field branch uses `curvePlaceAdeleTensorMap_bijective`. Its
hypotheses are a finite constant field `k`, a function field `K` with its given
rational-function presentation, and a finite-dimensional extension `L/K`
compatible with the constant-field actions. The upper rational-function
presentation and its scalar towers are derived internally. No separability
is required. The underlying proof constructs a projective model of the upper
affine line and uses the canonical adelic Weil counit comparison. Naturality
of tensor-valued affine-line points identifies the resulting bijection with
the literal tensor algebra map.

The number-field branch uses `numberFieldAdeleTensorMap_bijective` for
arbitrary number fields with a given algebra structure. Its underlying proof
assembles the finite-adele tensor equivalence with the product of all infinite
completed-field tensor equivalences, then proves equality with the canonical
map by tensor induction. Every infinite factor and the actual finite
restricted-product condition are retained.

Both canonical maps send `a ⊗ x` to the principal adele of `a` times the
original inclusion of `x`. Their algebra-homomorphism structures are unchanged.
The focused proof introduces no additional arithmetic or topological premises.

The arithmetic identity is derived from Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed pp.9–10:
the natural adelic Weil point identification, specialized to the upper affine
line, gives scalar extension of the full adelic ring. The source is registered
as `conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The exact conjunction and this proof's packaging are derived internal content.
No tensor topology or additional point-space homeomorphism is asserted here.
