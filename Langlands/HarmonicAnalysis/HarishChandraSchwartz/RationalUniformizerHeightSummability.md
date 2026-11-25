# Polynomial height summability on the actual uniformizer lattice

This internal auxiliary construction supplies the polynomial
height series used in the lattice step of Waldspurger's Corollary VIII.3.2.
The source is *La formule de Plancherel pour les groupes p-adiques* (2003),
registered as `waldspurger-2003-plancherel`, printed pp.326–327 (PDF pp.92–93).
On p.327 the proof reduces convergence to polynomial decay on a lattice using
the height comparison of I.1 (6), printed p.242 (PDF p.8). The implementation
combines the Library's actual coordinate-height lower bound with summability
on a discrete integer lattice.

Let `F` be any nonarchimedean local field in arbitrary universe `u`, let `G`
be an affine group scheme over `F`, and let `i : S.toGrp ⟶ G` be a closed
split-torus embedding. The matrix representation `ρ` has a nonempty finite
index type with decidable equality and is a closed subgroup embedding. The
series uses the original published matrix height `rationalHeight ρ`.

`exists_summable_rationalHeight_uniformizerPowers` proves that for some
natural number `d`, the real series

`Σ y : cocharacterLattice S, (1 + rationalHeight ρ (ϖ^y)) ^ (-d)`

is summable. The published `exists_cocharacterCoordinates_norm_le` supplies
an injection `H` into a finite-dimensional standard integer lattice `L` and
a positive constant `C` with

`1 + ‖H y‖ ≤ C * (1 + rationalHeight ρ (ϖ^y))`.

Take `d = Module.finrank ℤ L + 1`. The published
`summable_one_add_norm_rpow_neg` gives summability of `(1 + ‖z‖)^(-d)` on `L`.
Multiplication by `C^d` and restriction along the injective `H` preserve
summability. Since `d` is nonnegative, the displayed height inequality gives

`(1 + rationalHeight ρ (ϖ^y))^(-d) ≤ C^d * (1 + ‖H y‖)^(-d)`.

Comparison of nonnegative real series finishes the proof. The same argument
applies to the trivial torus, whose zero-dimensional lattice has a single point.

`RationalUniformizerHeightSummability i ρ` states that one natural
threshold works for every real decay exponent `r` at least that threshold.
It requires both real `Summable` and finiteness of the sum of
`ENNReal.ofReal` of the same nonnegative terms on the entire cocharacter
lattice. Under the closed embedding and split-torus hypotheses above,
`exists_rationalHeight_uniformizerPowers_tsum_lt_top` proves it by comparing
exponents using `1 + rationalHeight ≥ 1` and applying
`Summable.tsum_ofReal_lt_top`.

`exists_rationalHeight_uniformizerPowers_comp_tsum_lt_top` restricts these
conclusions along any injective map `e : J → cocharacterLattice S`, for an
arbitrary index type in universe `v`. This covers chamber subsets, sublattices
and injectively parametrized corrected positive orthants.

The source of the coordinate-height lower bound and lattice summability
lemmas is `RationalXiSquareIntegrableOfUpperBound`.
