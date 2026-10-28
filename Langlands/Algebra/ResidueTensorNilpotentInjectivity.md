# Residue-tensor injectivity for power-torsion coefficients

`Langlands.Algebra.residueTensorNilpotentInjectivity` proves the published
proposition `Langlands.Algebra.ResidueTensorNilpotentInjectivityStatement`
with its four independent universe parameters `u v w z`. The statement is
imported by Lean name and is not changed.

The proposition says: let `R` be a commutative local ring with maximal
ideal `m` and residue field `k`, and let `f : A → B` be a map of
`R`-modules with `B` flat over `R` and `k ⊗[R] A → k ⊗[R] B` injective.
Then `C ⊗[R] A → C ⊗[R] B` is injective for every `R`-module `C` with
`r • c = 0` for all `r ∈ m^n` and `c ∈ C`. Both maps are the actual
`LinearMap.lTensor` maps.

## Coefficients killed by `m`

The first private helper treats `C` with `m C = 0`. The torsion module
API (`Module.IsTorsionBySet.module`) gives `C` the induced `k`-module
structure with a compatible scalar tower `R → k → C`. Every `k`-module
is flat, so tensoring the injective map `k ⊗[R] f` with `C` over `k`
stays injective. `AlgebraTensorModule.cancelBaseChange` identifies
`C ⊗[k] (k ⊗[R] A)` with `C ⊗[R] A`, and likewise for `B`. Tensor
induction proves that these identifications carry the base-changed map
to `C ⊗[R] f`, which is therefore injective.

## Induction on the power

The second private helper inducts on `n`, letting the coefficient module
vary in the fixed universe `z`.

- For `n = 0`, the ideal `m^0` is all of `R`, so `1` kills `C` and every
  element of `C` is zero. Tensor induction shows that `C ⊗[R] A` is zero,
  so the map is injective.
- For `n + 1`, put `N = m • C`, the submodule spanned by the products.
  Since `m^(n+1)` kills `C`, `m^(n+1) • C = 0`, hence
  `m^n • N = m^(n+1) • C = 0`, and the induction hypothesis makes
  `N ⊗[R] f` injective. The quotient `C/N` is killed by `m`, so the
  first helper makes `(C/N) ⊗[R] f` injective.

Take `x ∈ C ⊗[R] A` mapping to zero in `C ⊗[R] B`. Naturality of the
tensor maps in the coefficient module and injectivity on `C/N` show
that the image of `x` in `(C/N) ⊗[R] A` is zero. Right exactness of
`- ⊗[R] A` on `N → C → C/N` (`rTensor_exact`) gives `y ∈ N ⊗[R] A`
mapping to `x`. The image of `y` in `N ⊗[R] B` goes to zero in
`C ⊗[R] B`, by the commuting square for `N → C`. Flatness of `B` makes
`N ⊗[R] B → C ⊗[R] B` injective, so that image of `y` is zero.
Injectivity of `N ⊗[R] f` gives `y = 0`, hence `x = 0`.

The closing theorem introduces the hypotheses of the statement, turns
`Module.Flat R B` into an instance, and applies the second helper.

## Scope and provenance

No finiteness, Noetherian, flatness of `A` or `C`, nonzero-module or
universe-equality hypothesis is used. The checked theorem depends only on
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement is a derived internal generalization of the first claim in
the proof of Stacks Project, Commutative Algebra, Lemma 10.99.1 (tag
00ME): registered source `stacks-algebra-flatness-criteria-2026-10-22`,
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MD.html`, Section 10.99. The source proves injectivity of
`N/m^n N → M/m^n M` through the successive quotients `m^n/m^(n+1)`.
The Lean proof instead uses the sequence `mC → C → C/mC` for arbitrary
coefficients killed by a power of `m`. Taking `C = R/m^n` recovers the
source claim through the canonical identification
`(R/m^n) ⊗[R] N ≅ N/m^n N`, which is neither stated nor proved here.

The Lean proof is Worker 666's unreviewed draft of task
90c1db03-0049-445e-9845-423d7fb17ea0, reused with only its docstrings
changed.
