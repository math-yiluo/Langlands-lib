# Affine schemes of finite type in a standard open of projective space

Helper module for the proof of `ProperSchemeCoverStatement` (weak Chow lemma route).

## Declarations

- `stdAway C n`: the ring `C[X₀, …, Xₙ]_{(X₀)}` of degree-zero fractions with powers of `X₀` as
  denominators, so that `Spec (stdAway C n)` is the standard affine open `D₊(X₀)` of `ℙⁿ_C`.
- `stdAwayι C n`: the open immersion `D₊(X₀) ⟶ Proj C[X₀, …, Xₙ]`, i.e. Mathlib's `Proj.awayι`
  for the degree-one element `X₀`.
- `exists_closedImmersion_stdAway`: for an affine scheme `W` with a morphism
  `s : W ⟶ Spec C` locally of finite type, there are `n` and a closed immersion
  `ι : W ⟶ D₊(X₀) ⊂ ℙⁿ_C` with `ι ≫ stdAwayι C n ≫ ProjSpace.π C n = s`.

## Proof

The global sections `Γ(W)` form a finitely generated `C`-algebra via `s`; choose generators
`t = {a₁, …, aₙ}`. The library theorem `ProjSpace.exists_algHom_away_apply_ratio_eq` gives a
`C`-algebra map `φ : C[X₀, …, Xₙ]_{(X₀)} → Γ(W)` sending `Xₖ/X₀` to `b k`, where
`b = (1, a₁, …, aₙ)`. Its range contains the generators, so `φ` is surjective, and
`ι := W.isoSpec.hom ≫ Spec.map φ` is a closed immersion
(`IsClosedImmersion.spec_of_surjective`). Compatibility with the structure maps reduces, via
`ProjSpace.awayι_comp_π`, to `φ` being a `C`-algebra map.
