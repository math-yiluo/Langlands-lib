# Multiplicative polynomial functions and roots

This module proves the two polynomial lemmas in Milne's proof of Proposition 12.9 (*Abelian Varieties*, author revision 2022, p. 23, Lemmas 12.10 and 12.11), in the forms used by `Langlands.Algebra.DegreeDeterminant.DegreeData.det_eq`. It defines one counting function, `rootCount`.

## Lemma 12.11

`eq_prod_eval_roots`: let `L` be an algebraically closed field, `B` and `m` natural numbers with `m` even, and `Φ : L[X] → L` a function such that

- `Φ (F * G) = Φ F * Φ G` whenever `F.natDegree ≤ B` and `G.natDegree ≤ B`;
- `Φ (C c) = c ^ m` for every `c`;
- `Φ (X - C x) = Q.eval x` for every `x`, where `Q` is monic of degree `m`.

Then `Φ F = ∏_{q ∈ Q.roots} F.eval q` for every `F` with `F.natDegree ≤ B`.

Proof. `map_C_mul_prod_X_sub_C` shows by induction on a multiset `s` with at most `B` elements that `Φ (C c * ∏_{r ∈ s} (X - C r)) = c ^ m * ∏_{r ∈ s} Q.eval r`. Over an algebraically closed field, `F = C lc * ∏_{r ∈ F.roots} (X - C r)` and `Q = ∏_{q ∈ Q.roots} (X - C q)` (Mathlib's `C_leadingCoeff_mul_prod_multiset_X_sub_C`). Expanding both sides gives double products of `r - q` and `q - r`. They agree because `Q` has an even number `m` of roots, and the factor `lc ^ m` appears on both sides.

Milne's Lemma 12.11 assumes multiplicativity on a whole algebra. Here it is assumed only for polynomials of degree at most `B`, and the conclusion is stated only for such polynomials. Milne's sign `±` is `+` because `m` is even.

## Lemma 12.10

- `rootMultiplicity_zero_prod`: the order of vanishing at `0` of `∏_{q ∈ s} (X + C (f q))` is the number of `q ∈ s` with `f q = 0`, counted with multiplicity.
- `rootCount L F π` (definition): for `F π : K[X]` and a `K`-algebra `L`, the number of roots of `F` in `L`, counted with multiplicity, at which `π` vanishes. `rootCount_mul` and `rootCount_one` give its additivity in `F`.
- `exists_minpoly_dvd` and `dvd_of_rootCount_pos`: for `L` algebraically closed and algebraic over `K`, a nonconstant `F` has a root `θ` in `L`. The minimal polynomial of `θ` is monic, irreducible and divides `F`, and it is counted at least once. Conversely, a monic irreducible `π` that vanishes at a root of `F` is a minimal polynomial and divides `F`.
- `eq_of_rootCount_eq`: two monic polynomials `Q, χ` over `K` of degree at most `B` are equal if `rootCount L Q π = rootCount L χ π` for every monic irreducible `π` of degree at most `B`. The proof is by strong induction on the degree of `Q`. If `Q` is nonconstant, take the minimal polynomial `π` of one of its roots. The hypothesis shows that `π` also divides `χ`. Divide both by `π` and apply additivity of `rootCount`. If `Q = 1`, then `χ` has no root, so `χ = 1`.

Milne's Lemma 12.10 compares `|∏ F(a_i)|_l` and `|∏ F(b_i)|_l` for all `F` and cites Lang. Here the analytic part is separated out (module `PadicComparison`). The algebraic conclusion is stated through root counts with respect to monic irreducible polynomials. The proof by division by minimal polynomials is internal to this module; it is not taken from a source.
