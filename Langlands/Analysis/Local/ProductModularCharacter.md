# Modular characters of binary and finite products

This internal analytic unit computes the intrinsic modular character of actual binary products and finite dependent products of locally compact Hausdorff topological groups. It supplies the finite-product part of the adelic product-of-local-moduli comparison in Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Section 3.6, equations (3.12)–(3.13), printed pages 89–90. The five-page October 2026 errata contain no correction to Section 3.6. The implemented proof is derived from closed-normal restriction and continuous multiplicative equivalence transport, rather than from a construction of product Haar measure.

Let `G : Type u` and `H : Type v` be locally compact Hausdorff topological groups. They carry their given topologies, and `G × H` carries the usual product group and topology. The universes `u` and `v` are independent. The theorem `Langlands.ProductMeasure.modularCharacter_prod` proves

\[
\Delta_{G\times H}(g,h)=\Delta_G(g)\Delta_H(h).
\]

The auxiliary theorems `modularCharacter_prod_one` and `modularCharacter_one_prod` compute the two factor insertions. The definition `productModularCharacter` makes the displayed local expression a monoid homomorphism `(G × H) →* ℝ≥0`; `productModularCharacter_apply` identifies it pointwise with the intrinsic modular character of this actual product.

For a finite type `ι : Type u` and a family `G : ι → Type v` of locally compact Hausdorff topological groups, use the existing dependent product group and product topology. The index universe and factor universe are independent. The theorem `modularCharacter_pi` states

\[
\Delta_{\prod_i G_i}(x)=\prod_i\Delta_{G_i}(x_i).
\]

The theorem `modularCharacter_pi_mulSingle` gives the formula for a single coordinate insertion. The definition `piModularCharacter` is the local product as a monoid homomorphism `(∀ i, G i) →* ℝ≥0`, and `piModularCharacter_apply` identifies it pointwise with the intrinsic modular character. The finite type may be empty. Neither result requires countability, distinguished compact open subgroups, or unimodularity.

The convention is positive right pushforward on left Haar measure: `Measure.map (· * x) haar = Δ(x) • haar`. With a supplied measurable structure satisfying `BorelSpace` on the respective product, `map_mul_right_haar_eq_prod` and `map_mul_right_haar_eq_pi` replace the scalar by the corresponding local product. The measure is the fixed Mathlib left Haar measure on that same actual product. The intrinsic modular-character formulas require no supplied measurable structure.

The implementation uses the following route.

1. `Langlands.QuotientIntegration.modularCharacter_subgroupEquiv` combines the proved closed-normal modular restriction with existing continuous multiplicative equivalence transport. If `A` is a locally compact Hausdorff topological group, `B` is a locally compact topological group, `K` is a closed normal subgroup of `A`, and `e : B ≃ₜ* K`, it proves `Δ_A(e b) = Δ_B(b)`. The group universes are independent. The proof derives local compactness of `K` from closedness and locally equips the actual groups and quotient carriers with Borel measurable structures needed by the restriction theorem. It assumes no modular equality or unimodularity.
2. The subgroup of `G × H` whose second coordinate is one is closed, normal, and continuously multiplicatively equivalent to `G` by insertion and first projection. The helper gives the first-factor modular formula. Swapping the factors gives the second-factor formula. The equality `(g,h) = (g,1) * (1,h)` and multiplicativity then give the binary formula.
3. For the dependent product, the subgroup equal to one away from a fixed coordinate is closed, by continuity of all coordinate evaluations, and normal, by pointwise conjugation. Single-coordinate insertion and evaluation give a continuous multiplicative equivalence with the original factor. The helper therefore gives `modularCharacter_pi_mulSingle`.
4. A private induction on a finite set of potentially nonidentity coordinates proves the local product formula. Removing coordinate `a` replaces `x` by `(Pi.mulSingle a (x a))⁻¹ * x`; its value at `a` is one and every other coordinate is unchanged. Multiplicativity and the single-coordinate comparison give the induction step without a product of elements in a noncommutative group. Taking the finite set to be `Finset.univ` proves the public finite-product formula, including the empty case.
5. The two local expressions satisfy the homomorphism laws by commutativity of nonnegative-real multiplication. Their pointwise comparison theorems use the corresponding intrinsic formulas. The Haar corollaries use the existing regular-Haar right-translation equality.

The closed-normal restriction module is a separately submitted prerequisite and must be integrated before this module. This unit does not prove the local determinant/Jacobian comparison, the actual adelic character-norm formula, reductive determinant triviality, or the universal `AdelicHaarUnimodularityStatement`.
