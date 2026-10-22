# Normalized rational profinite-integer and finite-adele comparison

`Langlands.Global.RationalProfiniteIntegerAdeleComparison : Prop` is an
internal comparison statement between already published constructions. It has
no parameters or assumptions. It asserts the existence of two compatible maps:

- A ring equivalence `e₀` from `ProfiniteIntegerRing` to the actual subring
  `integralFiniteAdeles ℚ`, continuous in both directions. On the integer residue
  family for `z`, its value in the ambient finite adele ring is the diagonal
  image of the rational integer `z`.
- A `ℚ`-algebra equivalence `e` from `ℚ ⊗[ℤ] ProfiniteIntegerRing` to
  `FiniteAdeles ℚ`, with `e (q ⊗ a) = q · e₀(a)` in the ambient finite adele
  ring for every rational `q` and every compatible residue family `a`.

The Lean file defines this proposition only. It does not prove it, choose an
equivalence, install a finite-adelic scalar action, or assume the statement in
a data structure. A separate proof task must establish the comparison.

## Exact objects and topology

The source ring is the inverse limit of `ZMod n` over positive integers and all
divisibility reduction maps, imported from `Langlands.Global.ProfiniteIntegerRing`.
It has the subspace topology of the product of finite discrete residue rings.
`ProfiniteIntegerRing.intCastHom` sends an integer to its residue family.

The target `FiniteAdeles ℚ` is the existing Mathlib finite adele ring of the
rationals, imported through `Langlands.Global.Adelic`. Its index set is
`HeightOneSpectrum (NumberField.RingOfIntegers ℚ)`, and its factors are the
actual adic completions. It is a restricted product relative to the actual
valuation subrings, with its existing restricted-product topology.
`integralFiniteAdeles ℚ` is the published subring of families integral at every
finite place, with the inherited subspace topology. Both continuity clauses
refer to these exact topologies. No alternative product indexed by natural
primes is silently substituted; any proof using that model must establish the
necessary place and completion identifications.

The rational tensor product is the algebraic tensor product over `ℤ`. Its
`ℚ`-algebra structure is the one from its first factor. No topology on this
tensor product is asserted here. Thus the first equivalence is a topological
ring comparison, while the second is an algebraic comparison. The formula
couples them explicitly; a bare unrelated algebra isomorphism would not meet
the proposition. Since pure tensors generate the tensor product, the formula
fixes the extension once `e₀` is fixed. The statement does not separately claim
uniqueness of `e₀`.

## Provenance and scope

This is an internal comparison obligation needed to use the published scalar
residue ring with Harris–Taylor's rational Tate space. Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), Chapter I,
printed p.18 (PDF p.26), defines the rational Tate space as `TA ⊗_ℤ ℚ`.
Chapter III, printed p.91 (PDF p.99), uses its finite-adelic scalar structure in
the level-structure definition. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The present two-model comparison is an internal precise formulation of the
required bridge, not a theorem quoted verbatim from those passages.

This proposition concerns the scalar rings only. It does not identify Tate
modules with restricted products of prime-adic Tate spaces, assert ranks or
geometric torsion properties, or address the prime-to-p variant. It does not
tensor a Tate module over `ℤ` with the finite adele ring. Downstream finite-adelic
actions must use the actual rationalization `ℚ ⊗_ℤ TA` and the comparison stated
here, or a scalar extension over the profinite-integer ring. A topology on the
rationalized scalar ring or Tate space needs its own definition and comparison.
