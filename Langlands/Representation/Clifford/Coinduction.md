# Clifford theory for coinduction from a finite-index subgroup

This internal module is the first layer of an abstract Clifford theory for a
group `G`, a normal subgroup `N` and an intermediate subgroup `N ≤ H ≤ G` of
finite index. It works with complex representations of arbitrary groups,
without a topology, and with the coinduction model of the Library and Mathlib:
`Representation.coind H.subtype θ` acts by right translation on the space
`coindV H.subtype θ` of functions `f : G → V` with `f (h * x) = θ h (f x)`.

The mathematical content is Mackey's irreducibility criterion for an induced
representation in the case of a normal subgroup (J.-P. Serre, *Linear
Representations of Finite Groups* (1977), registered as
`serre-1977-linear-representations`, §7.4, Proposition 23, and the proof of
Proposition 25 (a) in §8.2, printed pp. 59–63), carried out here directly in
the function model of coinduction and for groups that need not be finite.

## Extension by zero

- `extendByZero H θ v` is the equivariant function supported on `H` whose
  value at `1` is `v`; on `H` it is `y ↦ θ y v`. It is linear, injective
  (`extendByZero_injective`) and `H`-equivariant (`coind_extendByZero`,
  bundled as `extendByZeroIntertwining`).
- `sum_coind_extendByZero`: every equivariant function is the sum over right
  cosets `q` of `H` of the translates by `q.out⁻¹` of the extensions by zero
  of its values `f q.out`. The proof compares values at an arbitrary point:
  every summand for a coset other than the coset of that point vanishes there,
  and the summand for its coset takes the value of `f` there.

## Disjoint conjugates

`ConjugatesDisjoint H N hNH θ σ` says: for every `x ∉ H`, every intertwiner
from the conjugate of the restriction of `θ` to `N` by `x` (via the Library's
`Weil.InductionSemisimplicity.conjugateInclusion`) to the restriction of `σ`
to `N` vanishes.

- `intertwining_apply_eq`: under this condition, an `H`-intertwiner `ψ` out of
  the restriction of the coinduction to `H` satisfies
  `ψ f = ψ (extendByZero H θ (f 1))`. By the coset decomposition, it suffices
  to show that `ψ` kills the translates of extensions by zero for cosets other
  than `H`; restricted to `N`, such a translate spans a copy of a conjugate of
  `θ|_N`, so the composite is an intertwiner of the forbidden kind.
- `coind_apply_eq_one`, `evalOneComp` and `intertwining_coind_apply`: an
  intertwiner `F` between two coinductions is recovered from the
  `H`-intertwiner "evaluate `F f` at one".
- `coind_end_scalar`: if `θ` is irreducible and finite-dimensional and its
  conjugates are disjoint from it, every endomorphism of the coinduction is a
  scalar. Evaluation at one composed with the endomorphism is determined by
  its restriction along extension by zero, an endomorphism of `θ`, which is
  scalar by Schur's lemma (`CyclicRestriction.end_eq_smul_one` from the module
  `Langlands.Representation.CyclicRestriction`).
- `coind_isIrreducible`: hence the coinduction of a nonzero such `θ` is
  irreducible, by `CyclicRestriction.isIrreducible_of_scalar_ends` and the
  semisimplicity of the coinduction of a semisimple representation,
  `Weil.InductionSemisimplicity.coind_semisimple`.
- `exists_ne_zero_of_coind`: a nonzero intertwiner between two coinductions,
  with disjointness from `θ'` to `θ`, yields a nonzero intertwiner `θ' → θ`.

## Vanishing, conjugation and reciprocity

- `intertwining_eq_zero`: an `N`-intertwiner from the restriction of a
  coinduction to `N` into a representation `σ` of `N` vanishes when no
  conjugate of `θ|_N` maps nontrivially to `σ`. The argument again goes
  through the coset decomposition.
- `restrictAut α hα` restricts an automorphism `α` of `G` preserving `H` to
  `H`. `coindCompEquiv` is the equivalence between the pullback of the
  coinduction along `α` and the coinduction of `θ ∘ restrictAut α hα`, given by
  precomposition with `α`. `coindEquivOfEquiv` is the coinduction of an
  equivalence.
- `coindLift H σ P` is Frobenius reciprocity into coinduction: an
  `H`-intertwiner `P : σ|_H → θ` gives `v ↦ (x ↦ P (σ x v))`, and
  `coindLift_ne_zero` shows that it is nonzero when `P` is.
