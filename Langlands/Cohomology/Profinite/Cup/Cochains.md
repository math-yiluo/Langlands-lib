# The cup product of inhomogeneous cochains

`Langlands/Cohomology/Profinite/Cup/Cochains.lean`, namespace `Langlands.ProfiniteCohomology`.

The cup product of a `p`-cochain `f` of `A` and a `q`-cochain `g` of `B` is the `n`-cochain of
`A ⊗ B` (`p + q = n`) given by `(f ∪ g)(x₁,…,xₙ) = f(x₁,…,x_p) ⊗ (x₁⋯x_p)·g(x_{p+1},…,xₙ)`. It is the
Library's cochain cup `Langlands.Tate.ordinaryCochainCup` for the tensor pairing; this file reads it
in degree `n` and gives the formula and the identities the profinite cup products use.

## Declarations

- `partialProd_add`, `partialProd_contractNth_of_lt`, `partialProd_contractNth_of_le`,
  `contractNth_prefix`, `contractNth_prefix_of_le`, `contractNth_suffix`, `contractNth_suffix_of_lt`,
  `partialProd_prefix`, `partialProd_mk_zero`, `prod_ofFn_eq_partialProd`: index computations with
  partial products and face maps of tuples.
- `cupCochain h f g`: the cup product of cochains, defined as
  `Langlands.Tate.ordinaryCochainCup (Langlands.Tate.tensorPairing A B) p q f g` read through
  `Fin.cast h`; `ordinaryCochainCup_apply_partialProd` and `cupCochain_apply`: the explicit formula
  above.
- `d_cupCochain`: the Leibniz rule `d(f ∪ g) = df ∪ g + (-1)ᵖ f ∪ dg`.
- `tensor_ρ_tmul`, `leftUnitor_hom_tmul`, `rightUnitor_hom_tmul`: the action and the unitors of
  `Rep k G` on pure tensors.
- `cupₗ h`: the cup product of cochains as a bilinear map; `tensorHom_cupCochain`: naturality in
  the coefficients.
- `oneCochain`: the constant `0`-cochain `1` of the unit object; `leftUnitor_oneCochain_cupCochain`,
  `rightUnitor_cupCochain_oneCochain`: it is a unit for the cup product of cochains.

## Source and licence

Taken from `src/GroundTheory/TateCohomology/CupCochains.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). That source directory is not
taken as a whole (its uses are bound to the Library's Tate cohomology): `cupCochain` is redefined
from the Library's `ordinaryCochainCup` (whose formula uses the list product of the first `p`
entries and degree `p + q`), and the source's formula is proved as the adapter
`ordinaryCochainCup_apply_partialProd`; the index lemmas, the unitor lemmas, `cupₗ`,
`tensorHom_cupCochain` and `oneCochain` have no counterpart in the Library and are taken with
their source names and proofs (namespace `GroundTheory.GroupCoh` → `Langlands.ProfiniteCohomology`).
The source's `associator_hom_tmul`, `cupCochainsTensor` and `associator_cupCochain` are not taken
(no end result uses them).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §4, p. 36 (the cup product of cochains and Proposition
  (1.4.1)). They define it on homogeneous cochains,
  `(a ∪ b)(σ₀, …, σ_{p+q}) = a(σ₀, …, σ_p) ⊗ b(σ_p, …, σ_{p+q})`; the inhomogeneous formula here
  corresponds to it under the isomorphism of chapter I, §2, p. 14.
