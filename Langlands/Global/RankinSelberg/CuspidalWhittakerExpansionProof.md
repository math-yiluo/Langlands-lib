# Proof of the Whittaker expansion of the cusp forms of cuspidal realizations

This module proves `Langlands.Global.RankinSelbergGlobal.CuspidalWhittakerExpansionStatement`
(module `Langlands.Global.RankinSelberg.ProjectionExpansionReduction`). The proof is the theorem

```
theorem Langlands.Global.RankinSelbergGlobal.cuspidalWhittakerExpansionStatement_proof :
    CuspidalWhittakerExpansionStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Statement proved

Let `F : Type u` be a number field with `𝔸_F/F` compact, let `r : ℕ`, and let
`T : CuspidalOperatorRealization F r` be an actual cuspidal realization of `GL_(r+1)`. Then
`CuspidalWhittakerExpansion F T` holds (definition in module `ProjectionExpansion`). For every
standard additive character `ψ`, every vector `v` and every `g ∈ GL_(r+1)(𝔸)`, write
`W = cuspWhittaker F T ψ v` and `φ = cuspFunction F T v`. Then:

- `q ↦ ‖W(cornerAdelicPoint F r q.out * g)‖` is summable over `N_r(F) \ GL_r(F)`, and
- `q ↦ W(cornerAdelicPoint F r q.out * g)` has sum `φ(g)`.

This is the expansion `φ(g) = Σ_(γ ∈ N_r(F) \ GL_r(F)) W_φ(diag(γ, 1) g)`, with absolute
convergence, of J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §1,
Theorem 1.1 (printed p.200; source `cogdell-2004-analytic-theory-gln`). It is also
J. A. Shalika (1974), §5, Theorem 5.9 (source `shalika-1974-multiplicity-one`). The target fixes
all simple-root coefficients of the Whittaker character to `1`.

## The proof

The theorem itself is one line: `fun F _ _ _ r T => Unfolding.cuspidalWhittakerExpansion F T`.
The work lies in the helper modules `Langlands.Global.RankinSelberg.WhittakerExpansionCore.*`.
Each has its own Markdown file. The route is a direct analytic proof. It does not use the
Library statement `WhittakerExpansionStatement`. The overall shape
follows the classical Piatetski-Shapiro–Shalika argument: Fourier expansion along the columns of
the unipotent radical, with constant terms removed by cuspidality. The decay estimates
behind the convergence were designed for this proof.

1. **Interface** (`Interface`). This module defines the Whittaker function `whittaker F r ψ f`
   (all coefficients `1`), the majorant property `HasWhittakerMajorants`, and the class
   `WhittakerDecayClass`. The class contains spaces of functions that are continuous, left
   invariant under rational points and of finite level, bounded on determinant bands, and closed
   under archimedean derivatives along square-zero directions. It also states half (S),
   `WhittakerMajorantsStatement`.
2. **Half (S): summable majorants** (`WhittakerBasic`, `WhittakerDeriv`, `WhittakerCharDeriv`,
   `WhittakerWords`, `WhittakerHeights`, `WhittakerFrequency`, `WhittakerCosets`,
   `WhittakerSupport`, `WhittakerDecay`, `WhittakerStep`). This half proves
   `whittakerMajorantsStatement_proof`. Let `f` be in a decay class and `j ≤ r`. Then on every
   compact set the terms `W_f(diag(γ_q, I) x)` over `N_j(F) \ GL_j(F)` have a summable majorant.
   The proof inducts on `j`. Repeated archimedean derivatives along the last column turn `W_f`
   into a polynomial multiple of itself. Finite level confines the relevant frequencies to a
   lattice. Coset representatives with controlled heights then give lattice sums that converge.
3. **Half (E): the expansion** (`ColumnTorus`, `ColumnsB`, `ExpansionGSide`,
   `ExpansionInduction`). This half proves `hasSum_whittaker_of_levelPropsB`. Let `f` be
   continuous and left invariant under `GL_(r+1)(F)`, with vanishing block constant terms
   (`LevelPropsB r`). Assume its Whittaker terms are summable at every level `k ≤ r`. Then `f` is
   the sum of its Whittaker expansion. The proof is an upward induction over the columns. At each
   step, the difference of the projection coefficient and the partial Whittaker sum has vanishing
   torus Fourier coefficients, so it is zero by Fourier uniqueness on `(𝔸/F)^k`.
4. **Realizations** (`ExpansionRealization`). The cusp functions of the vectors of `T` form a
   `WhittakerDecayClass`, with derivatives given by the enveloping-algebra action. Boundedness on
   bands comes from the Library's Siegel decomposition and chamber decay for cuspidal
   realizations. Cuspidality at the top level comes from the Library's
   `CuspidalWhittaker.levelProps_top` and `constantTerm_eq_zero`. The theorem
   `cuspidalWhittakerExpansion` combines (S) and (E) into `CuspidalWhittakerExpansion F T`.

Half (S) proves more than the target needs: its majorants are uniform for `x` in a compact set
`C`. The target records only pointwise absolute summability, and only that is used here.
