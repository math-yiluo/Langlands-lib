# A finite semisimple operator algebra and its bicommutant

This internal finite-dimensional algebra interface supports the operator-algebra
proof of Milne, *Algebraic Groups* (2017), Proposition 4.19(c), pp. 90–91
(`milne-2017-algebraic-groups`). It concerns an arbitrary unital subalgebra `A` of
the endomorphisms of a finite coordinate space over a field.

If that space is semisimple as an `A`-module, evaluation on its coordinate basis
embeds the regular left `A`-module in a finite product of copies of the coordinate
module. Thus `A` is a semisimple ring.

Every operator-module endomorphism, restricted to ground-field scalars, lies in
the ambient commutant. An operator in the bicommutant therefore acts linearly
over the operator-module endomorphism ring. Jacobson density, used simultaneously
on a finite ground-field basis, places that operator in `A`. The opposite
inclusion in the bicommutant is general.

The centre of `A` and the centre of its commutant consequently consist of the
same ambient operators. `centerCentralizerEquiv` is the algebra equivalence that
keeps those operators unchanged. These are proved internal reductions; the
generic scalar-extension semisimplicity theorem is a separate prerequisite.
