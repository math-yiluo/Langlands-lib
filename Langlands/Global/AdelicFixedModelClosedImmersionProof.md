# Closed embeddings for full-adele fixed-model points

Author: Worker 208.

`adelicFixedModelClosedImmersion` proves exactly
`Langlands.Global.AdelicFixedModelClosedImmersionStatement` in the original
arbitrary common universe. Both clauses use actual relative scheme morphisms,
the original outside-S integer scalar actions and the independently defined
final topologies on points over the actual full adele rings. Every infinite
number-field factor is retained. The curve clause preserves the specified
k → RatFunc k → F scalar tower, arbitrary constants and inseparable function
fields. Both initial finite sets may be empty. There is no affineness,
separatedness or quasi-separatedness assumption.

The first private helper proves that the spectrum of an injective ring map has
zero kernel ideal sheaf. Naturality of `Scheme.ΓSpecIso` identifies its global
sections map with the given injective map up to the canonical ring
isomorphisms. `Scheme.ker_of_isAffine` then computes the kernel ideal sheaf.

Suppose an A-valued Y-point becomes the image of a B-valued X-point under a
closed immersion f after an injective coefficient map A → B. The kernel of f
is contained in the kernel of the composite B-point. The composition formula
for scheme kernel ideal sheaves and the zero-kernel calculation identify the
latter with the kernel of the original Y-point. The universal closed-immersion
lift therefore gives an A-valued X-point. Its base equation follows from the
base equations of f and the Y-point, and the monomorphism property of f
identifies its B-extension with the original X-point.

Consequently, for any subset C of full X-points, the preimage of f(C) at any
stage equals the stage image of the preimage of C. If C is closed, the latter
is closed by continuity of the source stage inclusion and closedness of the
stage map. The final topology on Y therefore makes f(C) closed. Continuity
of the full map follows from continuity at every stage, and injectivity follows
from the monomorphism property. These three properties give a closed embedding.
This internal argument needs neither a point-colimit bijection nor open stage
inclusions.

For each arithmetic branch, base change of f is a closed immersion and base
change of the target structure morphism remains finite type. The actual level
closed-embedding theorem applies. Naturality of `ringPointBaseChangeEquiv`
and the published fixed-model stage homeomorphisms transport this result back
to the original fixed-base point spaces. The actual level-to-adele coefficient
maps are literal subring inclusions, so their injectivity is
`Subtype.val_injective`. The generic final-topology argument now proves both
clauses of the exact target.

The source assertion is Brian Conrad, *Weil and Grothendieck approaches to
adelic points*, December 31, 2011, printed p.9, beginning of Section 4; its
preceding Corollary 3.7 uses the arithmetic-level closed-embedding assertion.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The kernel-detection route is an internal proof of the derived fixed-model
statement, including its documented broader curve scope. Comparison with
generic-fiber adelic points and eventual descent of generic-fiber closed
immersions remain separate results.
