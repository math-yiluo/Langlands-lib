# Algebraic input for the density of rational points of tori

Worker 1110. This module is the algebraic part of the proof that the
rational points of a torus split by a finite Galois extension are Zariski
dense (`Langlands.GroupScheme.Torus.RationalDensity`, Milne, *Algebraic
Groups*, Corollary 12.65). Milne derives that corollary from
unirationality via induced tori. This development takes a different route:
it uses norms of `K`-points and Dedekind's independence of characters. The
results here are internal lemmas and are not numbered results in the
literature.

All declarations are in the namespace `Langlands.GroupScheme.TorusDensity`.
The Laurent polynomial algebra `R[t_i^{±1} : i ∈ I]` is modelled by
`AddMonoidAlgebra R (I →₀ ℤ)`, the same model the Library uses for split
tori. Universes are arbitrary.

## Evaluation of Laurent polynomials

For a commutative ring `A` and a family of units `t : I → Aˣ`,

- `evalMonoid t` is the monoid homomorphism sending the monomial with
  exponent `m` to `∏ i, t i ^ m i`, written as a finitely supported product.
  `evalMonoid_eq_prod` gives the finite product form when `I` is a
  `Fintype`. There are also lemmas for a single coordinate
  (`evalMonoid_single`), for products of families (`evalMonoid_mul`), for
  ring maps (`evalMonoid_map`), for renaming variables
  (`evalMonoid_mapDomain`), and for the trivial family (`evalMonoid_one`,
  `evalMonoid_const_one`).
- `monomialUnit R` sends a monomial to the unit `single m 1` of the Laurent
  algebra, and `coord R i` is the coordinate unit `t_i`.
- `lev R t`, for an `R`-algebra `A`, is the `R`-algebra map from the Laurent
  algebra to `A` sending `t_i` to `t i`. `lev_single`, `lev_coeff_sum` and
  `lev_coord` compute it on monomials, on a general element via its
  coefficients, and on coordinates.
- `algHom_ext_coord`: two `R`-algebra maps out of the Laurent algebra agree
  if they agree on all coordinates `t_i`. `monoidHom_ext` is the same
  statement for monoid homomorphisms out of the monomials, and
  `evalMonoid_coord` says that evaluating monomials at the coordinates gives
  the monomials themselves.

## Galois characters

Let `K / k` be an extension of fields. `gal σ` is the action of
`σ : K ≃ₐ[k] K` on `Kˣ`.

- `exponents_eq_zero`: let `K / k` be finite separable and `k` infinite.
  If `∏_σ σ(s) ^ d σ = 1` for every unit `s` of `K`, then all exponents
  `d σ` are zero. Proof: take a primitive element `α`
  (`Field.powerBasisOfFiniteOfSeparable`). Its conjugates `σ α` are
  pairwise distinct. Split `d = e - f` into positive and negative parts, and
  form `P n = ∏_σ (X - σ α) ^ n σ`. Applying the hypothesis to the units
  `c - α` with `c ∈ k` shows that `P e` and `P f` agree at the infinitely
  many points of `k` other than `α`, so `P e = P f`. Evaluating at a
  conjugate `σ₀ α` shows that `e σ₀ = 0` exactly when `f σ₀ = 0`. Since one
  of them is always zero, both are zero. This is the only place where the
  infinitude of `k` is used.
- `conjFamily t` is the family `(σ, i) ↦ σ (t i)`. `galChar m` is the
  character `t ↦ ∏_{σ, i} σ (t i) ^ m (σ, i)` of the group `I → Kˣ`.
  `galChar_mulSingle` evaluates it on a family that is `s` at one index and
  `1` elsewhere. `galChar_injective` (finite `I`) follows from the
  previous lemma.
- `exists_lev_conjFamily_ne_zero`: for finite `I`, let `H` be a nonzero
  Laurent polynomial over `K` in the variables `t_{(σ, i)}`. Then some
  `t : I → Kˣ` gives `H(σ (t i)) ≠ 0`. The value of `H` at `conjFamily t` is
  a `K`-linear combination of the characters `galChar m`, which are
  pairwise distinct. Mathlib's `linearIndependent_monoidHom` (Dedekind
  independence of characters) shows that the combination vanishes
  identically only if all coefficients of `H` are zero.

## Norm-shaped points

- `twist σ` applies `σ` to the coefficients of a Laurent polynomial in the
  variables `t_i` and renames `t_i` to `t_{(σ, i)}`.
  `lev_conjFamily_twist` shows that evaluating `twist σ x` at
  `conjFamily t` gives `σ` applied to the value of `x` at `t`.
- Let `u σ i` be units of the Laurent algebra over `K`. `normFamily u t` is
  the family `i ↦ ∏_σ σ (u σ i (t))`, where `u σ i (t)` is the value of
  `u σ i` at `t`. `normSubst u` is the `K`-algebra map
  `t_i ↦ ∏_σ twist σ (u σ i)`. By `lev_conjFamily_comp_normSubst`,
  evaluating at `normFamily u t` equals `normSubst u` followed by evaluation
  at `conjFamily t`.
- `collapse` is the `K`-algebra map with `t_{(1, i)} ↦ t_i` and
  `t_{(σ, i)} ↦ 1` for `σ ≠ 1`. It undoes `twist 1` (`collapse_twist_one`),
  and it sends `twist σ x`, for `σ ≠ 1`, to the constant `σ (x(1))`, where
  `x(1)` is the value of `x` at the family of ones
  (`collapse_twist_of_ne_one`). `rescale c` is the rescaling `t_i ↦ c_i t_i`
  by units `c_i` of `K`. It is injective because `rescale c⁻¹` inverts it.
- `normSubst_injective`: if `u 1 i = t_i` for all `i`, then
  `collapse ∘ normSubst u` is a rescaling, so `normSubst u` is injective.
- `exists_lev_normFamily_ne_zero`: let `K / k` be finite separable with
  `k` infinite, `I` finite, and `u` with `u 1 i = t_i`. Every nonzero
  Laurent polynomial `F` over `K` has some `t : I → Kˣ` with
  `F(normFamily u t) ≠ 0`. Since `normSubst u F` is nonzero, apply
  `exists_lev_conjFamily_ne_zero` to it and rewrite with
  `lev_conjFamily_comp_normSubst`.

In the geometric module, `u σ i` is the image of the coordinate `t_i` under
the ring map that the Galois twist induces on the coordinate ring of the
split torus `T_K`. Then `normFamily u t` gives the coordinates of the norm
`∏_σ σ(y)` of the `K`-point `y` with coordinates `t`.

Sources: Milne, *Algebraic Groups* (2017), Corollary 12.65 (printed p.251,
PDF p.267), is the geometric result this algebra serves. The Milne errata
snapshot of 2 November 2026 has no entry for printed pp.250–251. The proofs
here use only Mathlib: the primitive element theorem, polynomials agreeing
at infinitely many points, and linear independence of characters.
