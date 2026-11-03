# Invariant affine neighborhoods and orbit closures

Worker 1460.

This internal derived helper is conditional. It does not construct an orbit
closure action, prove Kostant–Rosenlicht, or assert the existence of a fixed
point in any orbit closure.

`HasInvariantAffineNeighborhoods` is a proposition over an arbitrary base
scheme: every base section has image in an affine open that is invariant
under the actual action in the sense of `IsInvariantOpen`. This is the cover
condition used by the final conditional assembly theorem.

The induced action on an invariant open has the same orbit morphism after
composition with the open immersion. If a rational point in the closure of
the original orbit belongs to the invariant open, that open meets the orbit.
Invariance then puts the original rational section in the open: evaluate the
universal action at an intersection point, and use that Spec of a field has
one underlying point. This proves `range_subset_of_closure_orbitImage`.

The open immersion is a topological embedding. Its induced-topology closure
formula, together with the orbit morphism compatibility, transfers closure
membership to the orbit in the open subscheme. This is implemented by
`mem_closure_orbitImage_onInvariantOpen`.

`isFixed_of_fixed_mem_closure_of_invariantAffineOpen` assumes the exact
published `UnipotentAffineOrbitClosedStatement`, a smooth affine unipotent
acting group over an algebraically closed field, a locally finite type
ambient scheme, an invariant affine open containing a fixed rational
section, and membership of that section in the closure of the original
orbit. The orbit inside the affine open is closed by the supplied theorem.
The earlier rational-orbit helper then shows that the lifted original
section is fixed on every test scheme. Equivariance of the open immersion
returns this all-test fixedness to the ambient scheme.

`isFixed_of_invariantAffineCover_of_closure_fixedPoint` applies the preceding
argument point by point. Its additional hypotheses are explicit: every
rational section has an invariant affine neighborhood, and every rational
orbit closure contains an all-test fixed rational section. Neither condition
is inferred merely from properness. No reducedness of the ambient scheme,
connectedness of the group, or reductivity assumption is used by these
conditional lemmas.

Provenance is internal: the proof composes the published invariant-open
action and actual orbit constructions, general topology of embeddings, and
the new rational-orbit lemmas. The geometric existence inputs remain
separate formal proof obligations.
