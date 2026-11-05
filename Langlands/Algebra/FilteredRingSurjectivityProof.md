# Proof of finite-type surjectivity descent

Worker 105 proves `FiniteTypeSurjectivityDescent` with
`finiteTypeSurjectivityDescent`, uniformly in universe `u`.
The source and derived scope are explained in the paired statement.

The proof equips `B.obj j₀` with the algebra structure induced by
`α.app j₀` and chooses a finite set of algebra generators. For each
generator, surjectivity of `φ` supplies an element of the limiting
ring of `A`. Joint surjectivity of the legs of the ring-colimit
cocone supplies a stage representative. Commutation with `φ` and
the filtered-colimit equality criterion for the underlying types
then give a later stage where the generator's image belongs to
the range of `α`.

A filtered cocone on the finite wide span of these arrows supplies
a single object `d.pt` and a single arrow `t : j₀ ⟶ d.pt`.
Its commutation equations preserve every generator witness along
that same arrow, including when parallel arrows exist in `J`.
The empty set of generators is allowed by this construction.

`Algebra.adjoin_eq_ring_closure` expresses generation as the
statement that the subring closure of the coefficient range and
the finite generators is the whole initial ring. The preimage of
`range (α.app d.pt)` under `B.map t` contains both subsets:
naturality handles coefficients, and the common-stage witnesses
handle generators. Therefore the entire range of `B.map t` lies
in the range of `α.app d.pt`.

Finally, `CommRingCat.closure_range_union_range_eq_top_of_isPushout`
uses the actual outgoing pushout square to generate `B.obj d.pt`
by these two incoming ranges. Both lie in the range of
`α.app d.pt`, so this range is the whole ring and the map is
surjective. The argument never cancels a transition map or assumes
one injective. It proves only the stated algebraic prerequisite;
the geometric chart and global-section comparisons remain separate.
