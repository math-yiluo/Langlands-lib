# Weight estimate for the generic unitriangular product

Module `Langlands.GroupScheme.UnitriangularUnipotent.WeightCore`. It imports only Mathlib
(`Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous`, `Mathlib.Data.Matrix.Mul` and
`Mathlib.RingTheory.TensorProduct.Basic`).
This is the polynomial core of the proof that the upper unitriangular group scheme
`U_N` is unipotent. The final assembly lives in
`Langlands.GroupScheme.UnitriangularUnipotentProof`.

## Provenance

The coordinate ring of `U_N` over a field `k` is the polynomial ring in the entries
`x_ij` with `i < j`. Milne (2017), *Algebraic Groups*, proof of Theorem 14.5, gives
`x_ij` the weight `j - i` and uses that the comultiplication
`Δ(x_ij) = ∑_l x_il ⊗ x_lj` is `x_ij ⊗ 1 + 1 ⊗ x_ij` plus terms of lower weight
in the second factor. The definitions here encode that setting in the form agreed with
Worker 1405, who supplied them verbatim. The theorems are derived lemmas for that
proof and do not appear separately in the literature.

## Definitions

- `Pos N`: the subtype `{p : Fin N × Fin N // p.1 < p.2}` of positions strictly above
  the diagonal. It indexes the coordinates `x_ij`.
- `posWeight p`: the weight `j - i` of `p = (i, j)`, as a natural number. It is at
  least `1` (`one_le_posWeight`).
- `upperTri v`: the `Fin N × Fin N` matrix over a commutative ring with `v p` at each
  position `p` above the diagonal, `1` on the diagonal and `0` below it.
- `comulPoly k`: the `k`-algebra map
  `MvPolynomial (Pos N) k → MvPolynomial (Pos N) (MvPolynomial (Pos N) k)` sending
  `X p` to the `p`-entry of `upperTri (C ∘ X) * upperTri X`. The *inner* variables
  `C (X q)` form the first tensor factor and the *outer* variables `X q` form the
  second. So `comulPoly` is the comultiplication `Δ(x_ij) = ∑_l x_il ⊗ x_lj`, written
  with the second tensor factor as the outer polynomial variables.
- `TotalWeightLE F s` (auxiliary): every outer monomial `d` and inner monomial `e`
  with `((F.coeff d).coeff e) ≠ 0` satisfy `wt d + wt e ≤ s`, where `wt` is
  `Finsupp.weight posWeight`.

## Main result

`coeff_comulPoly_of_weight_le`: let `f : MvPolynomial (Pos N) k` and let
`m : Pos N →₀ ℕ` be such that every monomial in the support of `f` has weight at most
`wt m`. Then the coefficient of the outer monomial `m` in `comulPoly k f` is the
constant inner polynomial `C (f.coeff m)`.

The helper lemmas are also public. They are `map_constantCoeff_comulPoly`, which says
that setting the inner variables to zero undoes `comulPoly`, the `upperTri` entry
lemmas, and the closure properties of `TotalWeightLE`.

## Proof

1. `TotalWeightLE` holds for `0` at every bound and is monotone in the bound. It is
   closed under addition and finite sums (at the same bound), multiplication (bounds
   add, by `coeff_mul` for both the outer and inner products), powers and finite
   products. `1`, `X q` and `C (X q)` satisfy it at `0`, `wt q` and `wt q`.
2. The matrix entries `upperTri (C ∘ X) i l` and `upperTri X l j` satisfy it at
   `l - i` and `j - l`. Entries below the diagonal are `0` and diagonal entries are
   `1`. In `comulPoly k (X p) = ∑_l upperTri (C ∘ X) i l * upperTri X l j` every
   summand is either `0` (if `l < i` or `j < l`) or bounded by
   `(l - i) + (j - l) = j - i`. So `comulPoly k (X p)` has total weight at most
   `posWeight p`.
3. Writing a monomial as `C c * ∏ X p ^ a p` shows that `comulPoly k (monomial a c)`
   has total weight at most `wt a`. Then `f = ∑ monomial a (f.coeff a)` gives total
   weight at most `wt m` for `comulPoly k f`.
4. So an inner monomial `e` occurring in the outer coefficient at `m` has
   `wt m + wt e ≤ wt m`. Hence `wt e = 0`, and `e = 0` because every position has
   weight at least `1`. That outer coefficient is therefore an inner constant.
5. `map constantCoeff ∘ comulPoly = id`, checked on `C r` and on `X p`. Under it,
   `upperTri (C ∘ X)` becomes `upperTri 0 = 1` and `upperTri X` stays the same. So
   that constant is the `m`-coefficient of `f`.

## Extracting an outer coefficient through a tensor product

`rid_lTensor_eval₂Hom` is an auxiliary lemma requested by Worker 1405 for the final
assembly. Its setting is a `k`-algebra map `θ : MvPolynomial σ k →ₐ[k] B` (with
`DecidableEq σ`), a `k`-linear functional `φ : B →ₗ[k] k`, and an exponent `m` with
`φ (θ (monomial d 1)) = if d = m then 1 else 0` for every `d`. For every
`F : MvPolynomial σ (MvPolynomial σ k)`, send `F` to `B ⊗[k] B` by `eval₂Hom`. That map
sends the coefficients through `θ` into the left factor and the outer variables `X q`
to `1 ⊗ θ (X q)`. Applying `φ` to the right factor and then `TensorProduct.rid` gives
`θ (F.coeff m)`.

Proof: by `MvPolynomial.induction_on'`. Both sides are additive. For a monomial
`monomial d c`, writing `monomial d 1 = ∏ X q ^ d q` and using that
`b ↦ 1 ⊗ b` is the algebra map `includeRight` shows that the image is
`θ c ⊗ θ (monomial d 1)`. Then `rid ∘ lTensor φ` gives `φ (θ (monomial d 1)) • θ c`.
By the hypothesis on `φ` and `coeff_monomial`, this equals `θ ((monomial d c).coeff m)`.
