# Tangent spanning by noncentral semisimple centralizers

`Lie.SemisimpleCentralizerSpanningStatement.{u}` is a derived target for
Milne's Proposition 17.79. For a smooth connected affine group scheme `G`
over any infinite field `k : Type u`, suppose its actual base change to
`AlgebraicClosure k` has a semisimple Lie element whose tangent centralizer
is proper. The conclusions are:

1. Such a Lie element exists over `k` itself.
2. The supremum of the tangent centralizers of all these elements over
   `k` is the entire actual Lie module
   `Additive (lieKernel G k)`.

The supremum is the smallest `k`-submodule containing each
`Lie.elementCentralizerLie G X` for which
`Lie.IsSemisimpleElement G X` and
`Lie.elementCentralizerLie G X ≠ ⊤`. Thus the spanning conclusion
retains all vectors in each centralizer, rather than only the
semisimple vectors themselves. The explicit existence conclusion also
retains the source's descent assertion.

The raw `lieKernel` is the identity kernel of actual points over the dual
numbers. `elementCentralizerLie` is the tangent submodule of the actual
all-test adjoint stabilizer. Properness of this submodule is the
noncentrality convention in this target. For a faithful matrix
representation, the dual-number commutation computation identifies
this carrier with vanishing of the commutator with `X`. That
identification and its compatibility with the source's Lie-bracket
language remain proof obligations; this statement file does not supply
them. The geometric premise uses the actual scheme base change and its
Lie kernel, not an unrelated supplied Lie algebra or a supplied
scalar-extension comparison.

Semisimplicity uses the algebraic-representation convention in
`Lie.SemisimpleElement`: every finite-dimensional algebraic group
representation has a geometrically semisimple actual differential at
`X`. The definition tests all such representations over the relevant
base field, and tests their matrices after entrywise algebraic closure.
It does not assert equivalence with all abstract Lie representations,
nor use a supplied Jordan decomposition as an extra hypothesis.

The original source is J. S. Milne, *Algebraic Groups* (2017),
Proposition 17.79, printed p.378 / PDF p.394, registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The source asserts descent of a noncentral semisimple Lie element from
an algebraic closure over an infinite field and spanning by their Lie
centralizers. Proposition 17.76 on printed p.377 / PDF p.393 gives
the intended tangent-centralizer interpretation. This target uses
the explicit algebraic-representation convention and the actual
tangent carrier, and restricts to connected affine group varieties
as needed by Cartan generation. A proof must justify these concrete
versions of the source assertions.

The complete registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction
to 17.76 or 17.79. This module states a proposition and provides no
proof. The statement does not assume perfection, splitting,
reductivity, a characteristic restriction, positive rank or positive
dimension. It makes no assertion when the geometric premise fails,
and supplies no conclusion about generation of rational points.
