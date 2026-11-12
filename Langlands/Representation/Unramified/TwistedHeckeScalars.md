# Standard Hecke scalars of character twists

Author: Worker 5137.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
contains the local spherical computation of the automorphic half, stated for abstract
smooth representations of `GL_(r+1)(F)` over a p-adic field `F`. It is the standard fact
that twisting an unramified representation by an unramified character `ψ ∘ det`
multiplies its Satake parameters by `ψ(ϖ)`. The proof works with the Library's standard
Hecke elements and their coset sums; it does not use the Satake isomorphism.

Stating it for abstract carriers `V`, `W` (rather than for the realization spaces of
`OperatorRealization`) also keeps elaboration fast: applying a linear equivalence between
two concrete realization spaces of `GL_(r+1)` exhausts the instance-synthesis budget.

## `Langlands.Unramified.eq_of_standardHeckeScalar_eq`

The standard Hecke scalars determine the spectrum: if
`standardHeckeScalar K s i = standardHeckeScalar K t i` for all `i : Fin (r + 2)`, then
`s = t`. The scalar is `(√q) ^ (i (r + 1 - i))` times the signed Euler coefficient
`(-1) ^ i · coeff_i (eulerPolynomial s)`, where `q > 1` is the residue cardinality. Cancelling
the nonzero factors shows that the Euler polynomials have the same coefficients in
degrees `≤ r + 1`; higher coefficients vanish as both polynomials have degree `r + 1`
(`Eigenvalues.eulerPolynomial_natDegree`). Injectivity of the Euler polynomial
(`Eigenvalues.eulerPolynomial_injective`) concludes.

## Namespace `Langlands.Unramified.PairedHecke`

Throughout, `F` is a p-adic field with its canonical topology (the local instances of
`PairedHeckeScalars`), `sphericalSubgroup F r = GL_(r+1)(𝒪_F)`, and `corner F ρ hρ` is
the action of the spherical Hecke algebra on the spherical vectors of a smooth
representation `ρ`.

- `character_labelledRep`: let `ψ : GL_(r+1)(F) →* ℂˣ` be trivial on
  `sphericalSubgroup F r`. Then `ψ` takes the same value on every labelled coset
  representative `labelledRep ϖ (residueLift F) α` of the `i`-th standard double coset
  as on the standard diagonal `standardDiagonal F r i = diag(ϖ, …, ϖ, 1, …, 1)` (with
  `i` entries `ϖ`). Each representative lies in `K t K` for the torus element
  `t = subsetTorus ϖ (initialSegment r i)` (`labelledRep_mem_doubleCoset`), and
  `t` is the standard diagonal (`standardDiagonal_eq_subsetTorus`); the two factors
  from `K` contribute `1`.
- `eq_scale_of_twist`: let `ρ` on `V` and `σ` on `W` be smooth representations of
  `GL_(r+1)(F)`, and `e : V ≃ₗ[ℂ] W` a linear equivalence with
  `σ g (e x) = ψ(g) · e (ρ g x)` (`he`), where `ψ` is trivial on `GL_(r+1)(𝒪_F)` (`hψ`)
  and `ψ(standardDiagonal F r i) = u ^ i` (`hu`). Suppose that on all spherical vectors
  the `i`-th standard Hecke element acts on `ρ` by `standardHeckeScalar F s i` (`hs`)
  and on `σ` by `standardHeckeScalar F t i` (`ht`), and that `ρ` has a nonzero
  spherical vector `a`. Then `t = Eigenvalues.scale u s`.

  Proof. Since `ψ` is trivial on `K = GL_(r+1)(𝒪_F)`, `b = e a` is a nonzero spherical
  vector of `σ`. On spherical vectors the `i`-th standard Hecke operator is the sum over
  the labelled coset representatives `x_α` (`standardHecke_cornerAction_eq_sum`). By `he`,
  `character_labelledRep` and `hu`, every term satisfies
  `σ(x_α)(e a) = u ^ i · e (ρ(x_α) a)`; summing,
  `corner σ (T_i) b = u ^ i · e (corner ρ (T_i) a) = (u ^ i · standardHeckeScalar F s i) · e a`.
  Comparing with `ht` and cancelling the nonzero vector `e a` (`smul_left_injective`)
  gives `standardHeckeScalar F t i = u ^ i · standardHeckeScalar F s i`, which is
  `standardHeckeScalar F (scale u s) i` by `standardHeckeScalar_scale`. The first lemma
  concludes.
