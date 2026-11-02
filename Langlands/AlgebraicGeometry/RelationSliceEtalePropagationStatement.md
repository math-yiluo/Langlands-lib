# Etale propagation and shrinking for a relation slice

`RelationSliceEtalePropagationStatement.{u}` is an internal supporting
proposition for the smooth equivalence relation slicing theorem. It
uses the unchanged published `AlgebraicSpace.AtlasRelation.IsEquivRel`
on `t,s : R → U`, with `U`, `R`, and the slicing scheme `V` in an
arbitrary universe `u`.

For a morphism `g : V → U`, write `B = V ×_{g,U,t} R`, let `p : B → V`
be the first projection, and let `h : B → U` be the second projection
followed by `s`. Assume that `s` is flat and that `h` is locally of
finite presentation. For any section `σ : V → B` of `p` and any
`v ∈ V` where the actual stalk map of `h` at `σ(v)` is formally etale,
there is an open neighborhood `W ⊆ V` of `v` such that the slice map
`W ×_{W→V→U,U,t} R → U` induced by `s` is etale.

The section is arbitrary: it need only satisfy `σ ≫ p = id`. In the
intended application, reflexivity of the relation supplies its identity
section. The hypotheses ask for local finite presentation of `h`
itself and do not assert finiteness of `g`, smoothness of either
projection, existence of the initial etale section point, surjectivity
of the resulting slice, or any quotient.

The internal derivation uses the difference map on `B ×_V B`. Its
two endpoint squares express it as the base change of `h` along `t`
and along `s`. At the pair `(σ(p(b)),b)`, an etale neighborhood of
`σ(p(b))` pulls back along `t` to make the difference map etale.
Pointwise descent along the flat morphism `s` gives formal etaleness
of `h` at `b`. The etale locus of a locally finitely presented
morphism is open. Taking its inverse image under `σ` as `W`, this
propagation shows that every stalk of the restricted slice is
formally etale, so that the entire slice is etale.

Worker 303 supplied the double-pullback propagation route. Worker
101 supplied the scheme etale-locus API used in its private
implementation. This pair states the resulting intermediate
proposition; its formal proof is a separate contribution.
