# The character lattice of `D(X)`

Module `Langlands.GroupScheme.SplitExistence.Characters`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). That the characters of the diagonalizable group
`D(X)` are the elements of `X` is classical (e.g. Milne, *Algebraic groups*, Thm. 12.9). Here it
is derived from the Library's computation for split tori.

## Declarations

- `evalChar ξ R`: evaluation `χ ↦ χ(ξ)` of characters `Multiplicative X →* Rˣ` at `ξ ∈ X`.
- `charPoints ξ T`: the induced map from the points of `D(X)` over a test scheme `T` to the
  points of `𝔾ₘ`. `charPoints_naturality` says it is natural in `T`.
- `charOf k ξ : characterLattice (Tk k)`: the character `χ ↦ χ(ξ)` of `D(X)`, defined by
  `homOfPoints`.
- `gmPoints_charOf`: on every test scheme, `charOf ξ` sends a point with character `χ` to the
  unit `χ(ξ)`.
- `charOf_add`: `charOf (ξ₁ + ξ₂) = charOf ξ₁ + charOf ξ₂`, checked on points.
  `charOfHom k` is the resulting additive map, and `charOfHom_apply` unfolds it.
- `basisIndex X`, `basisEquiv X` (`X` finite free over `ℤ`): the index type of a chosen basis
  of `X`, and the coordinate isomorphism `X ≃+ (basisIndex X → ℤ)`. `basisEquiv_symm_eq`
  expands an element in the basis.
- `splitIsoX k`: the Library's splitting isomorphism `D(X) ≅ 𝔾ₘ^I`
  (`Diagonalizable.splitIso`).
- `charOf_eq_split`: `charOf ξ` is the composite of the splitting isomorphism with the Library
  character of `𝔾ₘ^I` that has coordinates `basisEquiv ξ`
  (`splitTorus.characterLatticeEquiv`). This is checked on points: both sides send a point to
  `∏ χ(e_i) ^ ξ_i`.
- `precompEquiv k`: precomposition with the splitting isomorphism, an additive equivalence
  between the character lattices of `𝔾ₘ^I` and of `D(X)`.
- `charEquiv k : X ≃+ characterLattice (Tk k)`: the composite of `basisEquiv`, the inverse of
  the Library's `splitTorus.characterLatticeEquiv`, and `precompEquiv`.
- `charEquiv_apply`: `charEquiv k ξ = charOf k ξ`, by `charOf_eq_split`.
