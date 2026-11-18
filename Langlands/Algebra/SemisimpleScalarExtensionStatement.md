# Semisimple algebras after scalar extension

`Langlands.Algebra.SemisimpleScalarExtensionStatement.{uk,uK,uA}` is an internal
Prop-valued statement. This module proves nothing.

For fields `k` and `K`, a `k`-algebra structure on `K`, and an associative unital
algebra `A` finite-dimensional over `k`, the statement asserts:
if `A` is a semisimple ring, then `K ⊗[k] A` is a semisimple ring provided either
`K/k` is separable algebraic or the centre of `A` is an étale `k`-algebra.
The three types may occupy independent universes. Neither commutativity nor
nontriviality is assumed for `A`. The zero algebra is included.

`IsSemisimpleRing` is Mathlib's complemented-submodule-lattice formulation of
semisimplicity of the regular left module. `Algebra.IsSeparable k K` means that
every element of `K` is separable over `k`, so in particular the extension is
algebraic. The finite-dimensional centre `Subalgebra.center k A` is a commutative
`k`-algebra; being étale means being formally étale and finitely presented.

The provenance is internal. This is the finite-dimensional algebra prerequisite
for the proposed operator-algebra proof of Milne, *Algebraic Groups* (2017),
Proposition 4.19(c), pp. 90–91 (registered source
`milne-2017-algebraic-groups`). Milne states the representation theorem there and
refers to the analogous algebra results; this precise Lean statement is not
attributed to a numbered theorem of that source.

One possible proof uses the algebra form of Wedderburn–Artin. Write a semisimple
algebra as a finite product of matrix algebras over finite division algebras.
Under either hypothesis the tensor extension of each centre is reduced and
finite-dimensional over `K`, hence a product of fields. Over each such field
factor, central-simple scalar extension preserves simplicity, so each factor is
semisimple. These are proposed proof obligations, not results supplied by this
statement module. Existing central-simple scalar-extension results are in
`Langlands.Algebra.CentralSimpleScalarExtension`.
