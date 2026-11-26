# Character twists across a normal subgroup with abelian quotient

This internal module proves the twisting part of Clifford theory: two
finite-dimensional complex representations of a group `H` whose restrictions
to a normal subgroup `N` agree and are irreducible differ by a character of
`H` trivial on `N`, when `H / N` is abelian. The twist is the Library's
`Langlands.twist χ τ`, the representation `h ↦ χ h • τ h`. Groups need not be
finite and carry no topology here. The statement is the classical one behind
the "little group" description of J.-P. Serre, *Linear Representations of
Finite Groups* (1977), registered as `serre-1977-linear-representations`,
§8.2, Proposition 25 (printed pp. 62–63), for a quotient that is abelian
rather than a semidirect factor.

## Basic facts

- `isIrreducible_of_equiv`: irreducibility passes along an equivalence.
- `Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp` shows that if the pullback of `ρ` along a homomorphism is
  irreducible, so is `ρ`; every subrepresentation of `ρ` is one of the
  pullback.
- `Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero` shows that a nonzero intertwiner between irreducible
  representations is bijective (kernel and image are subrepresentations), so
  it gives an equivalence.
- `twist_comp_subtype`: a twist by a character trivial on `N` has the same
  restriction to `N`.
- `exists_common_eigenvector`: a pairwise commuting set of endomorphisms of a
  nonzero finite-dimensional complex vector space has a common eigenvector.
  The proof takes a nonzero subspace of least dimension that is stable under
  the whole set; in it each member has an eigenvalue, and the eigenspace is
  again stable under the set, so by minimality it is the whole subspace.

## Twists

- `restrictIntertwiners N β τ` is the subrepresentation of the Library's
  `linHom β τ` formed by the `N`-invariant linear maps, that is, the linear
  maps intertwining the restrictions to `N`. It is `H`-stable because `N` is
  normal.
- `exists_twist_intertwining`: if all commutators of `H` lie in `N` and there
  is a nonzero `N`-intertwiner from `β|_N` to `τ|_N`, then there are a
  character `χ` of `H` trivial on `N` and a nonzero intertwiner from `β` to
  `twist χ τ`. The group `H` acts on the finite-dimensional space of
  `N`-intertwiners through the abelian quotient `H / N` (by
  `T ↦ τ(h) ∘ T ∘ β(h)⁻¹`), so the operators of this action commute; a common
  eigenvector gives a nonzero `N`-intertwiner `T` with
  `τ(h) ∘ T ∘ β(h)⁻¹ = η(h) T` for a character `η` of `H` trivial on `N`. Hence
  `T ∘ β(h) = η(h)⁻¹ τ(h) ∘ T`, and `T` is an intertwiner from `β` to
  `twist η⁻¹ τ`; the proof takes `χ = η⁻¹`.
- `exists_twist_equiv`: if all commutators of `H` lie in `N`, `τ` and `τ'` are
  finite-dimensional, `τ|_N` is irreducible and `τ'|_N` is equivalent to it,
  then `τ'` is equivalent to `twist χ τ` for some `χ` trivial on `N`. Both
  sides are irreducible because their restrictions to `N` are, so the nonzero
  intertwiner above is an equivalence.
- `eq_of_twist_equiv`: if `τ` is finite-dimensional, `τ|_N` is irreducible and `twist χ τ` is equivalent
  to `twist χ' τ` for characters trivial on `N`, then `χ = χ'`. The
  equivalence is an endomorphism of `τ|_N`, hence a nonzero scalar by Schur's
  lemma (`CyclicRestriction.end_eq_smul_one`), and comparing the
  intertwining identity at a nonzero vector gives `χ x = χ' x`.
