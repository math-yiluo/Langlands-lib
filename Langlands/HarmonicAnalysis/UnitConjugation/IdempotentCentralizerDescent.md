# Centralizers of regular elements in idempotent Levis

Let `A` be a finite-dimensional algebra over an infinite field `F`, `e ∈ A` an
idempotent, and `M = Subalgebra.centralizer F {e}`. Write `N` for the complement
`e A (1 - e) ⊕ (1 - e) A e` of `M` from `IdempotentCentralizer.offDiagonal`.
Suppose `X ∈ M` is regular in `A` in the sense of `regularSet F A`.

- `offDiagonalAdjoint_bijective_of_mem_regularSet` proves that `ad X` restricts
  to a linear bijection on `N`. For `Y ∈ M`, the multiplicity of zero in the
  characteristic polynomial of `ad_A Y` is the sum of the multiplicities on
  `M` and `N`. `exists_regular_offDiagonal_invertible` gives a `Y` attaining
  the Lie-algebra rank of `M` on `M` and zero on `N`. Hence the rank of `A`
  is at most the rank of `M`. At `X`, the sum equals the rank of `A`, and the
  multiplicity on `M` is at least the rank of `M`. The multiplicity on `N`
  must therefore be zero. The restriction to `N` has trivial kernel and is
  bijective by finite dimensionality.
- `centralizer_le_of_mem_regularSet` proves that the algebra centralizer
  of `X` is contained in `M`. The diagonal projection commutes with left
  and right multiplication by `X`. If `y` commutes with `X`, the
  off-diagonal component of `y` is in the kernel of the restricted
  commutator. Thus `y` equals its diagonal projection, which lies in `M`.
- `conjugationCentralizerEquiv` is the continuous multiplicative equivalence
  from the centralizer of `X` in `Mˣ` to the centralizer of `X` in `Aˣ`,
  with the topologies induced by the given topology on `A`.
  `conjugationCentralizerEquiv_apply_val` identifies the forward map on units
  with the inclusion. A unit of `A` centralizing `X` and its inverse both lie
  in `M`, giving the inverse map. Continuity in both directions follows by
  checking the unit and inverse coordinates in the topology on units.

The declarations are in
`Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups* (notes by DeBacker and Sally, 1999), §1.2, Lemmas 1.5–1.7, printed
pp. 7–8, compares orbital integrals in a Levi subgroup and the ambient
group using the same Cartan subgroup. In the unit group of a
finite-dimensional semisimple algebra, the idempotent centralizer gives
the block diagonal Levi. The equivalence above gives the comparison of
centralizers for elements of that Levi regular in the ambient algebra.
The argument uses the characteristic polynomial of the restricted
commutator to give this comparison over any infinite field.
