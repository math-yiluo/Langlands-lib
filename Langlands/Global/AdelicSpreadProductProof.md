# Products on adelic points for independent arithmetic spreads

`Langlands.Global.adelicSpreadProduct` proves
`Langlands.Global.AdelicSpreadProductStatement`, with named function-field
and number-field clause proofs. The point types, finite-type spreads,
arbitrary specified generic-fiber isomorphisms and topologies are exactly
those in that statement. The factors and product vertex may have three
unrelated finite sets of allowed poles. Neither factor is required to be
separated or affine. The number-field branch uses full adeles, including
every infinite factor. The curve branch retains arbitrary perfect constant
fields and all the statement's compatible function-field scalar actions.
The universe `u` is arbitrary and initial finite sets may be empty.

This is a derived comparison in the setting of Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), printed pp.8–9. Its
proof uses the existing fixed-model pullback and arbitrary-spread topology
independence results, rather than a new descent theorem for diagrams.

First, the product of two finite-type models over the same arithmetic
integer ring is finite type: its first projection is a base change of the
second factor's structure map, and composing with the first factor's
structure map preserves local finite type and quasi-compactness. This
argument imposes no separatedness on either factor.

Apply the fixed-model adelic pullback theorem over the terminal object
`Over.mk (𝟙 _)`. Its structure morphism is the identity, hence is finite
type and separated. Compatibility of two points over this terminal base
is automatic. The forgetful map from the compatible-pair subtype to the
ordinary product is a homeomorphism; composing removes the subtype from
the fixed-model theorem.

Actual generic-fiber pullback preserves binary products. Composing the
two preserved cone legs with the given factor isomorphisms gives a
limiting binary fan. Uniqueness of its limit identifies the generic fiber
of the actual model product with the independently specified field product
cone. The two cone-leg equations follow from that uniqueness construction.
Naturality of the generic-fiber point equivalences gives the corresponding
point equations. The three defining spread point homeomorphisms then
transport the fixed-model product comparison to the actual field-scheme
point comparison. Equality transport identifies the composite function
with `fun p => (p ≫ c.fst, p ≫ c.snd)`.

Topology independence permits replacing the resulting product-model spread
by the arbitrary spread specified for the product vertex. For independent
factor bases, enlarge both finite sets to their union. The canonical
iterated-pullback isomorphisms identify the new generic fibers with the
original ones; finite type is preserved by these base changes. Topology
independence identifies both new factor topologies with the specified
original topologies. The common-base argument now applies. The number-field
proof repeats this construction with its original integer and full-adele
algebras, retaining every infinite factor.

Worker 208 authored this proof and its original explanation. The pair imports
the published predecessor results by module name. It establishes binary
products for supplied spreads; general generic-fiber pullbacks and the
remaining whole-paper obligations are separate.
