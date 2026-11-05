# Modular characters of actual restricted products

This is an internal analytic construction for the actual cofinite restricted product in Mathlib. It supplies the product-of-local-moduli step used in the adelic comparison in Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Section 3.6, equations (3.12)–(3.13), printed pages 89–90. The five-page October 2026 errata contain no correction to Section 3.6. The proof below is derived from existing modular-character transport, closed-normal restriction and compact-open triviality; it does not introduce a restricted-product measure.

Let `ι : Type u` be arbitrary and let `G : ι → Type v` be a family of locally compact Hausdorff topological groups. For each index let `K i` be a compact open subgroup of `G i`. Openness is supplied by `Fact (∀ i, IsOpen (K i : Set (G i)))` and compactness by `∀ i, CompactSpace (K i)`. The index universe and factor universe are independent. Write

\[
R=\prod_i'(G_i,K_i)
\]

for Mathlib's `RestrictedProduct` relative to the cofinite filter, with its existing group operations and restricted-product topology. These hypotheses give its locally compact Hausdorff topological group instances. Neither the groups nor the index set have a countability assumption. No group is assumed unimodular.

For `x : R`, `hasFiniteMulSupport_modularCharacter` proves that the function `i ↦ Measure.modularCharacter (x i)` has finite multiplicative support. The principal formula is `modularCharacter_eq_finprod`:

\[
\Delta_R(x)=\prod_i^{\mathrm{fin}}\Delta_{G_i}(x_i).
\]

The finite product is Lean's `finprod`; its finite-support hypothesis is proved, rather than inferred from the notation. The definition `modularCharacterHom K` is the right-hand side as a monoid homomorphism `R →* ℝ≥0`, and `modularCharacterHom_apply` identifies it with the intrinsic modular character. The more explicit theorem `modularCharacter_eq_prod` computes the same value over any finite set `s` outside which all coordinates lie in their distinguished subgroups.

The convention is positive right pushforward on left Haar measure. With any measurable structure satisfying `BorelSpace R`, `map_mul_right_haar_eq_finprod` states the actual measure equality

\[
(R_x)_*\operatorname{haar}_R
 =\left(\prod_i^{\mathrm{fin}}\Delta_{G_i}(x_i)\right)
   \operatorname{haar}_R,\qquad R_x(y)=yx.
\]

Here `haar` is the fixed Mathlib left Haar measure on this same restricted product. The intrinsic modular characters themselves require no supplied measurable structures; auxiliary Borel structures are chosen only within the closed-normal restriction proof.

The implemented proof proceeds as follows.

1. For each index `i`, the subgroup of restricted-product points equal to one away from `i` is closed: it is an intersection of preimages of the closed singleton `{1}` under continuous coordinate evaluations. It is normal by pointwise conjugation. Insertion at `i` and evaluation there give a continuous multiplicative equivalence between `G i` and this actual subgroup. Insertion is continuous because it factors through the principal restricted-product stage requiring integrality away from `i`.
2. The existing theorem `Langlands.Aubert.General.modularCharacter_continuousMulEquiv` transports the local modular character to that subgroup. The proved theorem `Langlands.QuotientIntegration.modularCharacter_normalSubgroup` compares it with the ambient modular character, with no unimodularity premise. Together these prove `modularCharacter_mulSingle`.
3. The all-integral subgroup is open by the defining restricted-product topology and compact as the range of the continuous structure map from the compact product `Π i, K i`. Existing compact-open triviality gives `modularCharacter_eq_one_of_forall_mem`. Applied to each `K i`, the same result gives `local_modularCharacter_eq_one`.
4. Induction on a finite exceptional set removes a coordinate `a` by replacing `x` with `(mulSingle K a (x a))⁻¹ * x`. Its coordinate at `a` is one, and every other coordinate is unchanged. Multiplicativity and the single-coordinate formula prove `modularCharacter_eq_prod`. This step does not form a product of elements of a potentially noncommutative group.
5. The restricted-product condition makes the exceptional set finite, and compact-open triviality makes every local modular value outside it equal to one. The finite product therefore equals `finprod`. Equality with the intrinsic modular character supplies the homomorphism laws of `modularCharacterHom`. The Haar scaling corollary follows from the existing regular-Haar right-translation formula.

The closed-normal restriction module is a separately submitted prerequisite and must be integrated before this module. This unit does not prove the local determinant/Jacobian formula, the comparison with the character norm of actual adelic algebraic-group points, reductive determinant triviality, or the universal `AdelicHaarUnimodularityStatement`.
