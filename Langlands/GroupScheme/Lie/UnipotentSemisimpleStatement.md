# Semisimple tangent elements of unipotent algebraic groups

`UnipotentSemisimpleStatement` says that for every field `k` and every actual
affine unipotent group scheme of finite type over `k`, a semisimple actual
tangent element is zero. The actual tangent space is written as the kernel of
reduction from dual-number points, so its zero is the raw group identity `1`.
The statement is general in the field universe. It assumes neither smoothness
nor connectedness, perfection, splitting, characteristic zero, or infinitude.

Semisimplicity has the precise published meaning
`Lie.IsSemisimpleElement`: the actual differential in every algebraic
representation `G → GL_(Fin n)` is geometrically semisimple, after extending
its matrix to the algebraic closure. It does not quantify over arbitrary
abstract Lie-algebra representations.

The source is the unipotent assertion in Milne, *Algebraic Groups* (2017),
Example 17.75, printed p.377 / PDF p.393. This is a derived formulation using
the algebraic-representation convention just described. A route to proving
it is to differentiate the uniform all-test product bound for unipotent
representations, obtaining nilpotent tangent matrices. A closed linear
embedding then detects zero after geometric semisimplicity is applied.
This file states the assertion and does not prove it.
