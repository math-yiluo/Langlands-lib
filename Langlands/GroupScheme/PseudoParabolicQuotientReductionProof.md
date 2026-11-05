# Pseudo-parabolic quotients as dynamic-parabolic quotients of pseudo-reductive groups

Authors: Worker 1527.

`Langlands.GroupScheme.pseudoParabolicQuotientPseudoReductiveReduction.{u}` proves the
unchanged published proposition
`Langlands.GroupScheme.PseudoParabolicQuotientPseudoReductiveReductionStatement.{u}`
from `Langlands.GroupScheme.PseudoParabolicQuotientReductionStatement`. The field,
universe, groups, pseudo-parabolic inclusion `i : P ⟶ G`, quotient `q : G.X ⟶ Q` and
hypotheses are exactly those of that statement. The proof adds no hypothesis: `k` may be
finite or imperfect of any characteristic, and `G` need not be pseudo-reductive. It uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The module reuses the auxiliary theorem
`PseudoParabolicQuotientSplitRadicalReduction.quasiCompact_of_surjective_comp`: for scheme morphisms
`p : X ⟶ Y` and `r : Y ⟶ Z` with `p` surjective and `p ≫ r` quasi-compact, `r` is
quasi-compact. The proof uses the identity `p((p ≫ r)⁻¹ U) = r⁻¹ U`, which holds by
surjectivity of `p`, and that continuous images of compact sets are compact.

## Proof

1. **Presentation of `P`.** `IsPseudoParabolicSubgroup i` gives that `G` is smooth,
   connected and affine. Its `presentation` field gives a ground-field unipotent radical
   `j : U ⟶ G` (`IsUnipotentRadical j`), a cocharacter `λ` (called `χ` in the Lean) and
   `IsFppfProduct (Dynamic.parabolic λ) (range j) i`. So on every test, a point lies in
   `range i` exactly when it is fppf-locally a product of a point of `P_G(λ)` and a
   point of `R_{u,k}(G)`.

2. **The pseudo-reductive quotient.** The Library theorem `unipotentRadicalQuotient`,
   applied to `j`, gives a group scheme `G'` with `IsPseudoReductive G'` and a
   homomorphism `π : G ⟶ G'` with `IsFppfQuotient (range j) π`. That is, `π` is flat,
   surjective and locally of finite presentation, and the range of its scheme-theoretic
   kernel is `range j`. Because `U` is smooth, connected, closed and unipotent,
   `HasSmoothConnectedUnipotentKernel.of_representative` applies to `π`, and its
   `smooth` field shows that `π` is smooth. `π` is also quasi-compact
   (`QuasiCompact.of_comp`): its composite with the structure map of `G'` is the affine
   structure map of `G`, and the structure map of `G'` is affine, hence quasi-separated.

3. **Corollary 2.1.9.** `Dynamic.parabolic_isFppfImage λ π` uses that `π` is smooth and
   surjective. It shows that `P_{G'}(λ ≫ π)` is the fppf image of `P_G(λ)` under `π`
   (`IsFppfImage`). With
   `IsFppfImage.fppfLocallyInProduct_kernel_iff`, the product description of step 1, and
   the kernel equality of step 2, this gives, for every test `T` and every
   `x : T ⟶ G.X`:
   `x ∈ range i ↔ x ≫ π ∈ P_{G'}(λ ≫ π)`.
   So `range i = (Dynamic.parabolic (λ ≫ π)).comap π`. Destructuring the fppf image
   gives a monomorphism `j₁` with `range j₁ = Dynamic.parabolic (λ ≫ π)`. Then
   `HomogeneousQuotientFactorization.kernel_le_of_comap` shows that `range i` contains
   the full kernel of `π`.

4. **Descent of `q`.** By step 2, `π` is flat, surjective and quasi-compact, so it is an
   effective epimorphism. Since `q` is constant on the cosets of `range i`, and these
   contain the kernel of `π`, `HomogeneousQuotientFactorization.desc` gives
   `q' : G'.X ⟶ Q` with `π ≫ q' = q` (`fac_desc`).

5. **Properties of `q'`.** The witnesses are `G'`, `χ' = λ ≫ π` and `q'`.
   - `IsPseudoReductive G'` comes from step 2.
   - `q'` is smooth by `Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp`,
     because `π` is smooth and surjective and `π ≫ q' = q` is smooth.
   - `q'` is surjective by `Surjective.of_comp`, because `π ≫ q' = q` is surjective.
   - `q'` is quasi-compact by the auxiliary theorem above, because `π` is surjective and
     `q` is quasi-compact.
   - The fibers: for every test `T` and `g h : T ⟶ G'.X`,
     `g ≫ q' = h ≫ q' ↔ g⁻¹ * h ∈ (Dynamic.parabolic (λ ≫ π)).carrier T`. This is
     `HomogeneousQuotientFactorization.desc_fibers` for the preimage equality
     `range i = (range j₁).comap π` of step 3, rewritten with
     `range j₁ = Dynamic.parabolic (λ ≫ π)`.

## Relation to the literature

This follows the proof of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition 2.2.10 (printed p.69–70, PDF p.95–96). That proof writes
`P = P_G(λ) R_{u,k}(G)` and uses Corollary 2.1.9 (printed p.58, PDF p.84) to get
`π(P) = P_{G'}(π ∘ λ)`, so `P = π⁻¹(P_{G'}(π ∘ λ))` and `G/P ≅ G'/P'`. Here the
isomorphism `G/P ≅ G'/P'` takes the form of the descended map `q'` on the given
quotient `Q`. The Library's version of Corollary 2.1.9 assumes that `π` is smooth, not
only flat. This holds because the kernel `R_{u,k}(G)` is smooth.
