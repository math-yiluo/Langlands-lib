# Inner-conjugation triviality on continuous degree-two cohomology

Proof implementation: Worker 134. Worker 160 supplied the prism formula and the
compatibility conventions for the inner-conjugation map. The proof imports
Worker 284's continuous prism construction from
`Langlands.Cohomology.Continuous.InnerConjugationPrism`.

`Langlands.Continuous.innerConjugationH2Triviality` proves exactly the imported
proposition `Langlands.Continuous.InnerConjugationH2Triviality.{u,v,w}`:
`innerConjugationMap A a 2` is the identity morphism of Mathlib's actual
`continuousCohomology 2 A` for every compact Hausdorff topological group `G`
and every topological representation `A` over a ring equipped with a topology.

The ring has universe `u`, the group has universe `v`, and the representation
carrier has universe `max v w`. The three universe parameters are independent.
The ring need not be commutative, and no discreteness assumption is made.
The algebraic and homology lemmas need neither compactness nor Hausdorffness.
The imported prism construction uses compactness to obtain local compactness
for continuous uncurrying; Hausdorffness is retained from the exact target but
is not needed in the construction.

## Implemented argument

`innerConjugationCochains_two_apply` evaluates the invariance identity of a
homogeneous cochain at three right-translated arguments. The coefficient action
by `a⁻¹` and the variable substitution by conjugation combine to give simultaneous
right translation of the three arguments by `a⁻¹`.

`homogeneousTwoCocycle_identity` unfolds Mathlib's recursive continuous
resolution differential on four arguments. This yields the alternating
four-term identity. `homogeneousTwoCocycle_prism_identity` applies it at
`(x,xt,yt,zt)`, `(x,y,yt,zt)`, and `(x,y,z,zt)`. An additive-group calculation gives

    d(s f)(x,y,z) = f(xt,yt,zt) - f(x,y,z),
    s f(x,y) = f(x,xt,yt) - f(x,y,yt).

`homologyMap_two_eq_id_of_boundaries` applies to an arbitrary cochain complex of
topological modules. It cancels the epimorphism from cycles to homology. For each
cycle, a supplied degree-one boundary witness identifies the difference between
its transformed and original cycle with `toCycles` of that witness. Injectivity
of `iCycles` follows by forgetting to modules, where monomorphisms are injective.
The actual homology projection kills `toCycles`, so the two homology classes
agree. This uses Mathlib's chosen cycles, homology, and canonical maps throughout.

`innerConjugationH2_eq_of_prism` combines these facts for any function
from degree-two cochains to degree-one cochains satisfying the displayed prism
formula with `t = a⁻¹`. It produces a boundary witness for each cocycle and applies
the preceding homology lemma. The definition of the imported inner-conjugation
map identifies it with the induced homology map of `innerConjugationCochains`.

Finally, `innerConjugationH2Triviality` instantiates this conditional lemma with
`innerConjugationPrism A a⁻¹` and `innerConjugationPrism_apply A a⁻¹`. The imported
construction supplies actual invariant nested continuous maps: it uncurries the
three-variable cochain twice, precomposes with the two continuous substitutions,
subtracts, and curries back. Its invariance follows because left multiplication
by a group element commutes with right multiplication by `a⁻¹`. Thus the final
theorem has exactly the target's hypotheses, with no additional prism or
comparison premise.

## Provenance and scope

These lemmas are a derived proof for the imported statement. The prism expression
was proposed by Worker 160 and verified by Worker 134 directly against Mathlib's
differential signs; Worker 284 constructed the continuous invariant prism in its
separate module. The proof route and homology argument are internal formalization
work. The statement's paired Markdown records Serre's abstract inner-conjugation
theorem and distinguishes it from this continuous adaptation. This module proves
only the stated degree-two result; it makes no assertion of an all-degree result
or of arithmetic closure-choice independence.
