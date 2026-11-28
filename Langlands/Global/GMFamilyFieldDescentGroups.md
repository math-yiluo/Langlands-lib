# Roots and characters of nested split components across a field extension

Let `K/k` be a field extension, `A` a split torus over `k`, `A₁` a split torus over `K`, and
`j : A_K ⟶ A₁`. This module compares roots and rational characters through `j`, in the setting
of J. Arthur, *An introduction to the trace formula* (2005), §17, printed pp.99–100,
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`. Declarations are in
`Langlands.GMFamily.FieldDescentTori`.

## Roots

For `i : A ⟶ G` and `i₁ : A₁ ⟶ G_K` with `i_K = j ≫ i₁`:

- `exists_fine_of_mem_roots`: every root `β` of `A` in `G` lifts to a root `α` of `A₁` in `G_K`
  with `j ≫ α = β_K`;
- `exists_coarse_of_mem_roots`: every root `α` of `A₁` with `j ≫ α ≠ 0` restricts to the scalar
  extension of a root of `A`.

Both combine `mem_roots_baseChange_iff` (roots are unchanged by scalar extension) with
`mem_roots_comp_iff` (roots for an action through a homomorphism of split tori are the nonzero
restrictions of roots).

## Rational characters

For `a : A ⟶ M`, `a₁ : A₁ ⟶ M₁`, `m : M₁ ⟶ M_K` with `j ≫ a₁ ≫ m = a_K`:

- `fineCharacter a₁ m χ` restricts the scalar extension of a rational character `χ` of `M` to
  `A₁`; `fineCharacterHom` and `fineEval` are the corresponding additive maps to characters and to
  real functionals.
- `comp_fineCharacter`: `j ≫ fineCharacter a₁ m χ` is the scalar extension of the restriction of
  `χ` to `A` (`characterLattice.baseChange_torusCharacterRestrict`).
- `eval_fineCharacter_inclusion`: on the image of `fieldCocharacterInclusion j`, the real
  functional of `fineCharacter a₁ m χ` is that of the restriction of `χ` to `A`.
- `fineKernel a₁ m` is the common kernel of the functionals of all `fineCharacter a₁ m χ`
  (`mem_fineKernel`).
- `eq_zero_of_forall_eval`: if the restrictions of rational characters to `A` have finite index in
  the character lattice of `A`, they separate real cocharacters (perfect pairing of a split torus).
  Hence `fieldCocharacterInclusion_injective`.
- `isCompl_fineKernel`: if restriction of rational characters to `A` is injective with finite index
  image (as provided by `characterRestriction` for a split component), the image of the real
  cocharacters of `A` and `fineKernel a₁ m` are complementary in `V A₁`. Disjointness comes from
  `eval_fineCharacter_inclusion` and separation; for the dimension count, the real span `W` of the
  functionals of the fine characters satisfies `fineKernel a₁ m = W.dualCoannihilator`, and
  restriction to the image of `A` is injective on `W` (flatness of `ℝ` over `ℤ`), so
  `finrank W ≤ finrank (V A)`.
