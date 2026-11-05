# Actual arithmetic models retaining a specified projective immersion

This derived construction supplies the arithmetic model existence step used in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10, especially the choice of a quasi-projective integral
model on p.10. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The input is an actual quasi-compact scheme X with a specified locally closed
immersion j into projective n-space over the original field F. Both constructors
retain this same n, including n = 0, and allow an arbitrary initial finite set S
of nonarchimedean places. The output has a finite exceptional set T containing S
and an actual model over the original outside-T integer ring. The geometric data
contain its immersion into projective n-space over that ring, its locally finitely
presented quasi-compact structural morphism, a Cartesian comparison with X over
the original literal field inclusion, and equality with the specified original
projective map after the canonical coefficient change.

`numberFieldProjectiveImmersionModel` uses all finite places of any number field
F and its actual outside-T integer subalgebra. Archimedean factors do not enter
this coefficient-ring construction. `curvePlaceProjectiveImmersionModel` uses
all discrete curve places trivial on a perfect constant field k, with the original
k → RatFunc k → F scalar tower and `FunctionField k F`. Finiteness of k is not
needed here; finite constants give the global function field case. Both branches
use one arbitrary common universe, impose no separability hypothesis, and allow
the initial set to be empty.

The private finite-coefficient argument works for any increasing subring family
indexed by finite sets that covers the ambient commutative ring. A finitely
generated integer subalgebra has finitely many ring generators. Choose a stage
containing each generator, take the finite union of these stages with S, and use
monotonicity and closure under ring operations to contain the entire subalgebra.
The function-field and number-field instances use the published finite-pole
exhaustion and monotonicity proofs for their actual integer rings.

Each constructor first obtains the published finite coefficient projective model
by its proved existence construction. The preceding finite-support argument
places its actual coefficient subring inside an actual integer stage. The
literal inclusion defines the intermediate algebra, and its composite into F
is the original inclusion. The coefficient base-change constructor then supplies
the geometric model and both original-map comparisons. Existence and the
geometric properties are constructed, not assumed as additional input data.

The finite exceptional sets in Conrad's extension setup must come from a common
lower-field set. Arranging that common set, integral Weil restriction and its
generic fiber, and the comparison of adelic topologies remain subsequent steps;
this module proves only the individual arithmetic model construction.
