# Bounded approximation of a field generator

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, the termination argument after (2.4.6), printed pp. 69–70 (PDF pp. 81–82), in the proof of (2.4.1)(i). There the source assumes that iterating (2.4.5) never stops, giving simple strata `[𝔄_m, n_m, r_m, γ_m]` and conjugates `β_m` of `β` with `β_m ≡ γ_m (mod 𝔓_m^{−r_m})`. All `γ_m` lie in the compact lattice `𝔭_F^g End_{𝔬_F}(L_0)`, so a subsequence `γ_{m_j}` converges to some `γ`. Since `r_m / e(𝔄_m) → −∞`, the differences `β_m − γ_m` tend to zero, so `β_{m_j} → γ` as well. Comparing characteristic polynomials then gives the contradiction: `γ` inherits the irreducible polynomial of `β` from the `β_{m_j}` and a proper power of an irreducible polynomial from the `γ_{m_j}`. `BoundedApproximationStatement` is an algebraic statement that can replace this compactness step. It is a derived result; the source does not state it in this form.

## Statement

`BoundedApproximationStatement` is a closed proposition over every nonarchimedean local field `F` and every finite-dimensional `F`-space `V`. Let `β ∈ End_F(V)` generate a field `F[β]`, and let `π` be a uniformizer of `𝒪[F]`. Then there is an integer `M` with the following property. For every lattice chain `𝓛` on `V`, every `γ ∈ End_F(V)` and every integer `t`, if

- `β` and `γ` lie in the order `𝔄(𝓛) = 𝓛.endFiltration 0`,
- `[F[γ]:F] < [F[β]:F]`, and
- `π^{−t}(β − γ) ∈ 𝔄(𝓛)`,

then `t ≤ M`. The bound depends on `β` and `π`, but not on the chain, on `γ`, or on `t`. Thus elements generating algebras of smaller degree cannot approximate `β` arbitrarily closely inside any chain order.

## Implemented proof

`exists_common_denominator` concerns a finite extension `E/F` and finitely many `F`-linear functionals `E → F`. It gives one nonzero `s ∈ 𝒪[F]` such that `s` times any of these functionals is integral on all of `𝔬_E = subfieldIntegers F E`. The images of the finitely generated `𝒪[F]`-module `𝔬_E` (Library instance `subfieldIntegers_finite`) span a finitely generated `𝒪[F]`-submodule of `F`. Mathlib's `FractionalIdeal.isFractional_of_fg` then supplies the common denominator.

`boundedApproximation_aux` applies this to `E = F[β]`, given its field structure. The functionals are the coordinates of the power basis `1, β, …, β^{D−1}`, where `D = [F[β]:F]`. This basis is constructed inside the commutative field `F[β]` from `elementGenerator β`, because `End_F(V)` is not commutative. Set `M = ord(s)`.

Given `𝓛`, `γ` and `t`, the element `γ` is integral over `𝒪[F]` as an element of the finitely generated order. Its minimal polynomial over `F` divides the image of a monic integral polynomial. By the Gauss lemma (`IsIntegrallyClosed.eq_map_mul_C_of_dvd`) it is therefore the image of a monic `p ∈ 𝒪[F][X]`. The degree of `p` is at most `[F[γ]:F]` (`minpoly.algHom_eq`, `minpoly.natDegree_le`), hence less than `D`. Since `p(γ) = 0`, the identity `x^{i+1} − y^{i+1} = x(x^i − y^i) + (x − y)y^i` gives `z = π^{−t} p(β) ∈ 𝔄(𝓛)`, using integral coefficients and multiplicativity of the order. So `z` is integral over `𝒪[F]`, and it lies in `F[β]`; hence `z ∈ 𝔬_E`. Its coordinate at index `deg p < D` is `π^{−t}`, because `p` is monic. The common denominator gives `s π^{−t} ∈ 𝒪[F]`, so `0 ≤ ord(s) − t`.

The proof uses neither compactness nor any conjugation of `β`. Only `propext`, `Classical.choice` and `Quot.sound` are used. This module proves only the bound; choosing an optimal approximation with it is left to later steps.
