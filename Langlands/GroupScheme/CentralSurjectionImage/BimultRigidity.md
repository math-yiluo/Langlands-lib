# Rigidity of bimultiplicative maps out of split tori

Author: Worker 1387.

This internal module, in the namespace
`Langlands.GroupScheme.CentralSurjectionImage`, works over a field `k : Type u`
with an affine group scheme `G` over `Spec k`; `G` need not be commutative.

## Rigidity over a domain

`IsMultG.eq_one_of_isDomain`: let `R` be a domain and a `k`-algebra, and `p` a
multiplicative point of `G` over `R[Λ]`. If the coefficient change of `p` along
some `ev : R →ₐ[k] k` is the identity point, then `p = 1`. The proof fixes `b`,
a nonzero exponent `γ`, and a matrix of coefficients `M` with
`comul M_ij = ∑ M_il ⊗ M_lj`, `counit M_ij = δ_ij` and `b` in the span of the
entries (published `AffineLinearEmbedding.exists_matrix_coefficients`). The
matrices `P δ = (weight p δ (M_ij))` over `R` satisfy
`P δ * P ε = if δ = ε then P δ else 0` (`IsMultG.conv_weight`), and `P 0`
specializes to `1` along `ev`. So `det (P 0)` is an idempotent of the domain `R`
specializing to `1`, hence equals `1`. Then `P 0` is invertible and idempotent,
so `P 0 = 1`, and `P γ = P γ * P 0 = 0`. Thus `weight p γ` vanishes on the span
of the entries, in particular on `b`.

## Bimultiplicative maps

`Dg Λ` is the diagonalizable group `D(Λ)` (published `Diagonalizable`), and `chi`
identifies its points over a `k`-algebra `A` with characters `Λ → Aˣ`
(published `Corepresented.affinePointsEquiv`), naturally in `A` (`chi_affineMap`,
`chi_symm_affineMap`). `affineMap_lift_comp` moves coefficient changes through
`lift x y ≫ β`, and `exists_affine_factor` factors any pair of points over a
test scheme `U` through the unit `U ⟶ Spec Γ(U)` of the published
`algΓAlgSpecAdjunction`.

- `lift_comp_eq_one_of_bimul_aux`: let `R` be a domain carrying a character
  `ιc : Λ → Rˣ` that is universal among characters of `Λ` and killed by some
  `ev : R →ₐ[k] k`. Let `β : D(Λ) × D(Λ) → G` be multiplicative in the first
  variable and trivial on `D(Λ) × 1`, on points over all `k`-algebras. Then `β`
  is trivial on affine points. The point `v = β(x_A, y_A)` over
  `A = R[Λ]`, with outer and inner universal characters, is multiplicative and
  specializes to `β(·, 1) = 1`, so `v = 1` by the previous result. Every pair of
  points over `A₀` is a coefficient change of `(x_A, y_A)` along a map built with
  `AddMonoidAlgebra.liftNCRingHom`.
- `lift_comp_eq_one_of_bimul`: if `k[Λ]` is a domain, the same conclusion holds
  for points over every test scheme. Take `R = k[Λ]` and `ιc` the monomials in
  the previous item, and use `exists_affine_factor`. The universal ring is kept
  abstract in the auxiliary lemma because typeclass synthesis of the group
  structure on `Λ → (k[Λ][Λ])ˣ` fails.

This is internal derived content (rigidity of homomorphisms from tori); no
literature result is attributed to it.
