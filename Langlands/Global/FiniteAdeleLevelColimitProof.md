# Categorical colimit proof for actual finite-adelic level rings

Authors: Worker 208 (proof); Worker 695 (source and interface audit,
verification and submission preparation).

`finiteAdeleLevelColimit` proves the exact proposition
`FiniteAdeleLevelColimitStatement` in an arbitrary universe `u`.

The proof first constructs the algebraic extension of a compatible family
of ring homomorphisms on a monotone cover by subrings indexed by finite
sets. For each element it chooses a level containing the element and
evaluates that level's homomorphism. Compatibility makes this value
independent of the choice: compare two choices in their union level.
One and zero lie in the empty level, and any two elements lie together in
a union level, which proves the ring homomorphism laws.

Apply this construction to the actual finite adelic levels and to the
legs of an arbitrary cocone in `CommRingCat`. Naturality gives the required
compatibility. The evaluation formula proves factorization through each
level. Exhaustion proves uniqueness, by evaluating an arbitrary adele in
one level containing it. This supplies an actual `IsColimit` structure
for the already defined ring cocone.

For a cocone in `TopCommRingCat`, forget its topology and use the same
algebraic extension. On each level it agrees with the original continuous
leg. The proved final-topology criterion for the actual finite adele ring
therefore makes the extension continuous. The same factorization and
exhaustion arguments give the topological categorical universal property.

This is the derived finite-sector version of the direct-limit assertion in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed/PDF p.1, beginning of Section 2. Registered
source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The general Dedekind-domain statement and its finite-sector scope are
explained in the paired statement Markdown; the implemented universal
property proof is the compatible-family argument above.

All constructions retain the target's arbitrary common universe and its
stated Dedekind-domain and fraction-field assumptions. The finite-place
set and each level index may be empty: finite unions and the empty level
remain available, and no nonempty-place premise is used. The proof uses
the existing level subrings, induced topologies, transition inclusions
and canonical cocone legs without changing their definitions.

This proves only the named ring-level target. The parent retains all five
sections, actual global fields of both characteristics, the all-place
convention and archimedean factors, nonaffine and algebraic-space point
comparisons, model descent and all remaining assertions.
