# Proof of the compact last-row cutoff for zero-row Whittaker coefficients

Author: Worker 252.

This module proves the published proposition
`Langlands.RankinSelberg.ZeroRowLastRowCutoffStatement.{uF,uV}` from
`Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`. The
theorem is

```lean
theorem Langlands.RankinSelberg.zeroRowLastRowCutoff :
    ZeroRowLastRowCutoffStatement.{uF,uV}
```

Its type is exactly the closed statement constant with independent universe
parameters `uF` and `uV`. The proof adds no hypotheses and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. It works with
the topology, valuative relation, valuative extension, module topology and
local-field structure supplied by `T`, which the statement installs. It covers
every `n` and `k`, including `n = 0` and `k = 0`. It also covers zero
functionals and zero coefficients.

## Auxiliary lattice lemmas

These lemmas are in namespace `Langlands.PadicField.TopologicalData`. They use
the published convention `additiveLattice m = π^(-m) O`.

The compactness and openness lemmas are imported from
[PadicLatticeTopology](../../HarmonicAnalysis/PadicLatticeTopology.md), where
their original names, statements and proofs are preserved. The conductor
lemma below remains in this module.

- `mem_additiveLattice_of_forall_mul_eq_one`: suppose `ψ (a * x) = 1` for every
  `x ∈ additiveLattice m`. Then `a ∈ additiveLattice (additiveConductor ψ - m)`.
  The hypothesis implies `ψ(t · π^(-m) a) = 1` for every integer `t`. By
  `integer_annihilator_iff_mem_additiveLattice`, `π^(-m) a` therefore lies in
  `additiveLattice (additiveConductor ψ)`. Since `ord (π^(-m)) = -m` (by
  `ord_zpow` and `ord_uniformizer`), `mul_mem_additiveLattice_iff` moves the
  level to `additiveConductor ψ - m`.

These are short consequences of the published conductor and integer-ring
facts. No Haar measure or self-duality is used.

## Column unipotents

Fix `n d : ℕ` and the rank `n + (d + 1) + 1`. For `y : Fin (n + 1) → F`, the
matrix `zeroRowColumnEntries n d y` places `y` in rows `0, …, n` of column
`n + 1`, which is the first appended coordinate, and has zeros elsewhere. Any
two such matrices multiply to zero. Hence `zeroRowColumnUnipotent n d y`, the
unit `I + E(y)` with explicit inverse `I - E(y)`, is a group element. The
following facts are proved about it.

- It is upper triangular with unit diagonal, so it lies in the actual
  `upperUnipotent` subgroup.
- Its only first-superdiagonal entry is at position `(n, n + 1)`, and it equals
  `y_n`. By `standardCharacter_apply`, the standard Whittaker character takes
  the value `ψ (y (Fin.last n))` on it
  (`standardCharacter_zeroRowColumnUnipotent`).
- Conjugation identity (`appendIdentity_mul_zeroRowColumnUnipotent`):
  `diag(g, I) · (I + E(y)) = (I + E(g y)) · diag(g, I)`.
  Here `diag(g, I) = appendIdentity n (d + 1) g`. Left multiplication by
  `diag(g, I)` sends the column `y` to `g *ᵥ y`. Right multiplication fixes
  `E(z)`, because row `n + 1` of `diag(g, I)` is the standard basis row.
- `y ↦ I + E(y)` is continuous into the general linear group with its
  units-of-matrices topology. Both the matrix and its explicit inverse depend
  continuously on `y`.

## Main proof

Let `f` be in the coefficient model of `ℓ`. By `Whittaker.modelMap_surjective`,
`f` is the coefficient of some vector `v`, so
`f.val.val x = ℓ (π x v)`. Smoothness of `π` gives an open subgroup `K` fixing
`v`.

Next, choose a lattice of columns inside `K`. Take the intersection over
`i : Fin (n + 1)` of the preimages of `K` under
`x ↦ I + E(Pi.single i x)`. This set is open by continuity and contains `0`.
By `exists_additiveLattice_subset` it therefore contains some
`additiveLattice m`. So every single-coordinate column unipotent with entry in
`additiveLattice m` fixes `v`.

The cutoff is defined from `M = additiveConductor ψ - m`. Let `B` be the box
`∏_i additiveLattice M` in `Fin (n + 1) → F`. It is compact
(`isCompact_univ_pi`) and open (`isOpen_set_pi`). Take
`Φ = compactOpenIndicator B`, the published Schwartz–Bruhat indicator from
`Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`. Every value
of `Φ` is `0` or `1`.

Fix `g` and write `h = diag(g, I)`. If `ℓ (π h v) = 0`, both sides of the
required identity vanish. Otherwise we show that `lastRow g ∈ B`. Fix a
coordinate `i` and some `x ∈ additiveLattice m`, and set
`z = g *ᵥ Pi.single i x`. By the conjugation identity,
`(I + E(z)) h = h (I + E(Pi.single i x))`. Since `I + E(Pi.single i x) ∈ K`
fixes `v`, the vector `π h v` is fixed by `I + E(z)`. The covariance
`ℓ (π u w) = θ(u) ℓ w`, stored as `ℓ.property`, then gives
`ℓ (π h v) = ψ(z_n) ℓ (π h v)`. Cancelling the nonzero value yields
`ψ(z_n) = 1`, and `z_n = g_{n,i} x`. Thus `ψ (g_{n,i} * x) = 1` for every `x`
in `additiveLattice m`. By `mem_additiveLattice_of_forall_mul_eq_one`,
`g_{n,i} ∈ additiveLattice M`. Since every coordinate of `lastRow g` lies in
the box, `Φ (lastRow g) = 1`, and the identity holds.

## Source and derived scope

The motivating source is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of
Mathematics 105 (1983), 367–464, §8.3, printed pp.450–451 (registered
`jpss-1983-rankin-selberg`; retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The rendered scan was read directly. No erratum for this source is registered
in the project literature. On p.450 the authors observe that
`W(diag(g, 1)) ≠ 0` forces the last row `η_t g` into a fixed compact subset of
`F^t`. They use the Iwasawa decomposition `g = nak` and the bound
`|α(diag(a, 1_(r-t)))| ≤ 1` for positive roots `α`. On p.451 they then insert a
nonnegative `Φ ∈ S(F^t)` evaluated at `η_t g` into the convergence integral.
Their ranks are `t = n + 1` and `r = n + (0 + k + 1) + 1`.

The Lean proof takes a different route. It does not use the Iwasawa
decomposition or root bounds. Instead it uses the smoothness of the vector
directly: small column unipotents, conjugated by `diag(g, I)`, together with
the character conductor bound the last row. The scope proved here is a derived
internal formulation, not a verbatim JPSS theorem. It covers all smooth
coefficient images, with no irreducibility, unitarity or square-integrability
assumption, and gives an explicit zero-or-one cutoff that preserves the
original coefficient.
