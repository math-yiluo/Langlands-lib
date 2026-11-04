# Smoothness of actual semisimple Lie-element centralizers

`Lie.SemisimpleCentralizerSmoothStatement.{u}` asks for smoothness of every
closed group-scheme representative of `Lie.elementCentralizer G X`, for a
smooth connected affine group scheme over an arbitrary field `k : Type u`
and a `Lie.IsSemisimpleElement G X`.

The centralizer is the actual adjoint stabilizer: it tests commutation with
the coefficient extension of the dual-number tangent point on every affine
refinement of every scheme test. `IsRepresentedBy j` includes monicity and
equality with the all-test range of `j`. The statement also explicitly
requires `j` to be a closed subgroup embedding. Closed representability
itself is provided by the separate
`Lie.elementCentralizer_isClosedRepresentable` construction, for affine
locally finite type groups over any field.

The semisimplicity convention is the one in `Lie.SemisimpleElement`:
every finite-dimensional algebraic group representation defined over `k`
has a geometrically semisimple actual differential at `X`. Its matrix is
extended entrywise to an algebraic closure before semisimplicity is
tested. This convention does not quantify over all abstract representations
of the underlying Lie algebra.

This is a derived target for the smoothness part of Milne, *Algebraic
Groups* (2017), Proposition 17.76, printed p.377 / PDF p.393, registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The original proposition asserts smoothness of the adjoint stabilizer of a
semisimple Lie element in a connected group variety. The source's
semisimplicity paragraph uses abstract Lie representations; the changed
representation convention here is explicit and must be handled by the
proof. No equivalence of the conventions is asserted. The affine
restriction matches the consumer's setting. Smoothness and affineness of
`G` imply finite type over `k`.

The complete registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to this
passage. This file supplies a proposition, not its proof. It does not
state the additional Lie-bracket centralizer identification in 17.76, nor
connectedness of the full centralizer. There is no infinitude, perfection,
splitting, characteristic, positive-dimension or positive-rank assumption.
