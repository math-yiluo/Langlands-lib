# The cyclic Herbrand quotient of the infinite-place permutation lattice

`CyclicInfinitePlaceLatticeHerbrandQuotient.{u,v}` states the following
proposition for every pair of number fields `F : Type u` and `E : Type v`,
with an `F`-algebra structure on `E`, such that `E/F` is Galois and
`G = E ≃ₐ[F] E` is cyclic. The universes are independent, and there is
no restriction excluding degree-one extensions.

Let `N` be the published `infinitePlaceLatticeRepresentation F E`.
It is the integer permutation lattice on the actual infinite places of
`E`, using `ULift.{v} ℤ` as coefficient ring. Its finite function
realization has action `(g f)(w) = f(g⁻¹ • w)`, where the action on
places is the arithmetic action. Write
`Hⁱ = infinitePlaceLatticeCohomology F E i` for its ordinary group
cohomology, and `D∞ = archimedeanHerbrandFactor F E` for the product
of stabilizer orders, one per orbit of infinite places.

The statement asserts that `H¹` and `H²` are finite and that

\[
  \lvert H^2(G,N)\rvert = D_\infty\,\lvert H^1(G,N)\rvert.
\]

Both cardinalities in Lean are `Nat.card` of the underlying types of
the corresponding cohomology modules. The explicit finiteness clauses
ensure that these are finite group orders. This cross-multiplied
formula avoids introducing rational division or a second definition
of cohomology.

The source is Milne, *Class Field Theory*, v4.03 (2020), Chapter VII,
proof of Proposition 3.1, printed page 209 (PDF page 218). Specialize
its finite set `T` to all infinite places of `E`. The source decomposes
`Hom(T, ℤ)` into permutation modules for the place orbits and applies
Shapiro's lemma and the trivial-integer calculation to obtain the
product of decomposition-group orders. In the present formulation,
those groups are the stabilizers used by `archimedeanHerbrandFactor`.
For a finite cyclic group, ordinary degree two identifies with Tate
degree zero, while ordinary degree one agrees with Tate degree one.
Thus the displayed ordinary-cohomology equality, together with its
finiteness assertions, expresses the source's Herbrand calculation.
The lifted coefficient ring is ring-equivalent to `ℤ`.

This is a derived specialization and reformulation of the source's
permutation-lattice calculation. It is a `Prop`-valued definition,
not a proof. It asserts no Dirichlet logarithm comparison, unit or
integral-idele formula, or idele-class theorem, and does not identify
the stabilizer orders with local degrees in Lean. Those results are
separate prerequisites or applications.

Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
