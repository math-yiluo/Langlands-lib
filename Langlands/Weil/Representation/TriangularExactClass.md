# Exact classes of upper triangular continuous representations

Internal helper module for the principal-series pair gamma comparison. It contains no
new statement taken from the literature. It records the standard linear-algebra fact
that a representation whose action is upper triangular in a basis has a flag of
subrepresentations with one-dimensional successive quotients. Each quotient is the line
on which the group acts by a diagonal entry. In the exact Grothendieck group of
continuous representations, the representation is therefore the sum of its diagonal
characters.

## Definitions (internal)

- `lineQuotientMap T P w` is the linear map `c ↦ [c • w]` from the carrier
  `ULift ℂ` of a character line to the quotient `T ⧸ P` of a subrepresentation by an
  invariant submodule.
- `IsUpperTriangularBasis A b`, for a finite-dimensional representation `A` and a
  basis `b : Fin n → A`: for every group element `g` and all `j < i`, the `b i`
  coordinate of `g • b j` vanishes. In matrix terms every `g` acts by an upper
  triangular matrix. This is the hypothesis of the target statement
  `PrincipalSeriesPairGammaMatchStatement`, with the quantifiers in the same order.
- `flagSubmodule A b k` is the span of `b l` for `l < k`. `flagSubrepresentation hb k`
  is the same submodule as a subrepresentation, invariant by upper triangularity.
  `flagFiltration hb` is the resulting object filtration
  `0 = S_0 ≤ S_1 ≤ … ≤ S_n = A` (`ObjectRepFiltration.ofSubrepresentations`).

## Results

- `lineQuotientEquiv`: suppose the quotient `T ⧸ P` is spanned by the class of `w`,
  `c • w ∈ P` only for `c = 0`, and `g • w - χ(g) w ∈ P` for every `g`. Then the
  character line of `χ` is equivalent to the quotient representation. The map is
  `lineQuotientMap`, which is bijective under these hypotheses and intertwines the
  two actions.
- `mem_flagSubmodule_iff`: `v` lies in the `k`-th flag step iff its coordinates of
  index `≥ k` vanish. Also `flagSubmodule_le_comap`, `flagSubmodule_mono`,
  `flagSubmodule_zero` and `flagSubmodule_length`.
- `repr_map_apply`, `IsUpperTriangularBasis.map`: moving a basis along a
  representation equivalence `f : B ≃ A` keeps the coordinates of the action, so upper
  triangularity and the diagonal entries transfer.
- `ofRepresentation_eq_sum_characterClass_of_triangular`: for a continuous `A` with an
  upper triangular basis whose diagonal entries are given by continuous characters
  `χ i`, the exact class of `A` is `∑ i, characterClass (χ i)`.
  *Proof:* `VirtualRepresentation.Weil.exactClass_eq_sum_of_filtration` applied to
  `flagFiltration` expresses the class as the sum of the graded pieces
  `S_{i+1} ⧸ S_i`. For each piece, `w = b i` satisfies the three hypotheses of
  `lineQuotientEquiv`; this is checked coordinatewise with `mem_flagSubmodule_iff`.
  Equivalent representations have equal classes.
- `ofRepresentation_eq_sum_characterClass_of_equiv_triangular`: the same conclusion for
  any `A` equivalent to a representation `B` with such a basis. The basis is moved
  to `A` along the equivalence.
- `ofRepresentation_tensor_eq_sum_characterClass`: if the classes of `A` and `A'` are
  `∑ i [χ i]` and `∑ j [η j]`, then the class of `A ⊗ A'` is
  `∑ i ∑ j [χ i * η j]`. The proof uses bilinearity of the continuous tensor product of
  exact classes (`continuousTensor_ofRepresentation`). It then uses
  `continuousTensor_characterClass` and `continuousTwist_characterClass`; the product
  order is fixed by commutativity of `ℂˣ`.
