# Unrestricted exponential growth on compressed lattices

`Langlands.UnrestrictedCompressedLatticeBoundStatement.{uG,uV,uI}` is an
internal, derived prerequisite for coefficientwise moderate growth. It is not
an assertion from the original literature in this general form.

For an admissible smooth complex representation of a topological group, fix a
compact open subgroup `K`, three subgroups `N`, `M`, `Nbar`, and a homomorphism
from a finite natural-coordinate lattice into the group. Assume the stated
opposite Iwahori factorization of `K` and the three explicit conjugation
conditions. These hypotheses make the actual compressed operators on the
finite-dimensional space of `K`-fixed vectors multiplicative.

The conclusion gives one real radius greater than one for each coordinate,
chosen before the vector and functional. Every coefficient of a `K`-fixed
vector and a `K`-fixed algebraic dual functional is bounded by a positive
constant times the product of these coordinate powers. The constant may depend
on the vector and functional. There is no spectral, temperedness or
finite-length premise. The index type may be empty and the fixed-vector space
may be zero. The group, representation carrier and index universes are
independent.

The derivation uses finite-dimensional operator norms and the existing
multiplicativity and coefficient-compression identities, rather than a bound
on Jacquet exponents. This statement supplies a local analytic estimate only:
it asserts no Cartan decomposition, existence of compatible compact open
subgroups, finite generation of a dominant cocharacter monoid, or comparison
with an algebraic matrix height. Those inputs are still required to deduce
moderate growth on actual reductive rational points.
