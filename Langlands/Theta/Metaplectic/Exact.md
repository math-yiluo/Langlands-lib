# The metaplectic group is an extension of the symplectic group by `ℂˣ`

**GKT §2.1.1–§2.1.2** (pp. 47–49: the Weil projective representation, the exact sequence
`1 → ℂˣ → Mp(W)^{ℂˣ}_{ψ,S} → Sp(W) → 1` by the Stone–von Neumann theorem and Schur's lemma),
**Proposition 6.8 (1)** (independence of the isomorphism of models) and §12.2.1 (two splittings
differ by a character).

The module `Langlands.Theta.Metaplectic.Exact` proves, over a nonarchimedean local field, that the
group of pairs `MetaplecticGroup ρ` of a smooth irreducible model `ρ` of the Heisenberg
representation is an extension of the symplectic group by `ℂˣ`.

## Content

Let `F` be a nonarchimedean local field with `⅟2`, `W` a finite-dimensional `F`-vector space with its
module topology, `B` a bilinear form on `W`, and `ρ` a representation of `HeisenbergGroup B` on a
complex vector space.

- General facts: `isIrreducible_comp_mulEquiv_iff` (irreducibility is unchanged by composing with
  an automorphism of the group), `nontrivial_of_isIrreducible` (an irreducible representation is on
  a non-zero space); `HeisenbergGroup.continuous_isometryAction`,
  `HeisenbergGroup.isSmooth_comp_isometryAction`,
  `HeisenbergGroup.hasCentralCharacter_comp_isometryAction`: the representation `h ↦ ρ(g · h)` of
  an isometry `g` is smooth with the same central character when `ρ` is.
- `MetaplecticGroup.ker_proj` (smooth irreducible `ρ`): the kernel of the projection is the group
  of scalars; by the Library's Schur lemma (`HeisenbergGroup.equiv_eq_smul`).
- `MetaplecticGroup.exists_scalar_mul_eq`: two elements with the same projection differ by a
  scalar.
- `MetaplecticGroup.proj_surjective` (`B` alternating non-degenerate, `ψ` continuous non-trivial,
  `ρ` smooth irreducible with central character `ψ`): every isometry lifts; by the Stone–von Neumann
  theorem (`HeisenbergGroup.nonempty_equiv`) applied to `ρ` and `h ↦ ρ(g · h)`.
- `MetaplecticGroup.exact`: the three statements together.
- `MetaplecticGroup.congr_eq`: `congr e = congr e'` for two isomorphisms `e, e' : ρ ≃ ρ'` of a smooth
  irreducible `ρ` (they differ by a scalar).
- `MetaplecticGroup.Splitting.exists_eq_twist`: two splittings `s, s'` of the same
  `ι : G →* Sp(W)` satisfy `s' = s.twist α` for a character `α : G →* ℂˣ` (the quotient
  `s'(g) s(g)⁻¹` is a scalar, and the scalars are central).

## Declarations

- `Langlands.isIrreducible_comp_mulEquiv_iff`, `Langlands.nontrivial_of_isIrreducible`.
- `Langlands.HeisenbergGroup.continuous_isometryAction`, `isSmooth_comp_isometryAction`,
  `hasCentralCharacter_comp_isometryAction`.
- `Langlands.Theta.MetaplecticGroup.ker_proj`, `exists_scalar_mul_eq`, `proj_surjective`, `exact`,
  `congr_eq`, `Splitting.exists_eq_twist`.

## Dependencies

`Langlands.Theta.Metaplectic.Defs`, `Langlands.Theta.Heisenberg.StoneVonNeumann`.
