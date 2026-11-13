# Second adjointness is equivalent to the Jacquet–contragredient formula

Author: Worker 5457. Module
`Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceProof`.

This module proves the Library proposition
`Langlands.Aubert.General.RepresentedParabolic.LeviSecondAdjointnessContragredientEquivalenceStatement`
as the theorem `leviSecondAdjointnessContragredientEquivalence`. It adds no hypothesis and keeps
the independent universes `u` (field) and `v` (carriers in `max u v`).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.9.6, printed pp.201–202 / PDF pp.207–208: the equivalence of Theorem
(VI.9.6.1), `i_P^G ⊣ r_{P̄}^G`, and Theorem (VI.9.6.2), `r_{P̄}^G(π~) ≅ (r_P^G π)~`. Registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Declarations

- `contragredient_compression_stationary_of_isLimit` (namespace `Langlands.Aubert.General`).
  Let `G` be locally compact and nonarchimedean, `U` a closed subgroup normalized by `Mb`,
  `e : M' ≃ₜ* Mb`, and `R = r_U ⋙ e^*` the transported normalized Jacquet functor. Assume that
  `R` sends the dual cone of the countable direct sum `⊕_ℕ A` (the cone `(⊕_ℕ A)~ → A~`) to a
  limit cone. Then for every compact open `K`, every `g` central in `Mb` with an Iwahori
  contraction `IsIwahoriContraction K U Mb O g`, the compression by `g` on the `K`-fixed
  smooth functionals of `A` has stationary power ranges and power kernels.
- `exists_central_hasOppositeIwahoriContractionBasis_of_dynamic`: subgroups equal to `N(χ⁻¹)`,
  `M(χ)` and `N(χ)` have an `M(χ)`-central element with an opposite Iwahori contraction
  basis (the contraction point of `χ⁻¹`). This is the first half of the Library proof of
  `RationalPointFamily.exists_isStableLiftDuality_of_dynamic`, stated for equal subgroups.
- `nonempty_leviSecondAdjunction_of_contragredientIso_of_dynamic`: the hypotheses of the
  Library theorem `nonempty_leviSecondAdjunction_of_dynamic`, with the VI.9.1 uniform
  stabilization hypothesis removed, together with a natural isomorphism
  `Ψ : r_{P̄}(π~) ≅ (r_P π)~`, give `i_P ⊣ r_{P̄}`.
- `nonempty_leviSecondAdjunction_of_contragredientIso`: (VI.9.6.2) ⇒ (VI.9.6.1) for one pair of
  represented parabolics with `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`.
- `leviSecondAdjointnessContragredientEquivalence`: the target statement.

## Implemented proof

**Forward direction.** (VI.9.6.1) ⇒ (VI.9.6.2) is the Library theorem
`nonempty_leviContragredientIso_of_secondAdjunction`.

**Reverse direction.** Renard deduces (VI.9.6.1) from (VI.9.6.2) by a Hom chain applied to
`π~~` and an exactness argument. Formalizing that chain needs compatibility of `Ψ` with
bidual evaluation, which an arbitrary natural isomorphism need not have. The Lean proof
uses `Ψ` only to get a limit-preservation property, and then reruns the Library's direct
VI.9 construction of second adjointness.

1. *Preserved countable powers.* With `F = leviFirstAdjointnessAdjunction` (`r_P ⊣ i_P`) and
   `C : (i_P τ)~ ≅ i_P(τ~)` from `nonempty_leviInductionContragredientIso`,
   `SmoothRep.frobeniusChainDualLimit F C Ψ` shows that `r_{P̄}` takes the dual of every colimit
   cocone to a limit cone. It is applied to the direct-sum coproduct
   `SmoothRep.directSumIsColimit (fun _ : ℕ => A)`.
2. *Stationary compression* (`contragredient_compression_stationary_of_isLimit`). Apply
   `Jacquet.stationary_of_powerFamily` with `ρ = A~`, `σ = (⊕_ℕ A)~` and
   `q n = ` the transpose of the `n`-th summand inclusion:
   - `hlift`: the dual cone `(⊕_ℕ A)~ → A~` is a limit, because the contragredient is a
     right adjoint (`contragredientAdjunction`). `SmoothRep.exists_fixed_eq_of_isLimit`
     turns a sequence of `K`-fixed functionals into one `K`-fixed functional on the sum.
   - `hinj`: the projections of the preserved limit are jointly injective
     (`SmoothRep.eq_zero_of_isLimit`). The normalized Jacquet module is carried by the
     coinvariants `Jacquet.Localization.Coinvariants _ U 1`. Its classes are compared with
     those of `Jacquet.mk` through the linear equivalence `Jacquet.Localization.trivialEquiv`.
   - `hsurj`: lift each Levi-fixed class `y n` to a vector `v n` and form the family
     `[v n]` in the vertices of the preserved limit. Each `[v n]` is fixed by the single open
     subgroup `e⁻¹((K ∩ Mb) ∩ ker δ^{-1/2})` of `M'`, by the twist formula
     `normalizedJacquetFunctor_obj_apply`. So `SmoothRep.exists_eq_of_isLimit` gives a vector
     of the cone point, which is the class of some `w` (`Jacquet.Localization.mk_surjective`).
   - Compatibility of families over `(Discrete ℕ)ᵒᵖ` is automatic
     (`SmoothRep.discreteOp_map_apply`).
3. *Second adjunction* (`nonempty_leviSecondAdjunction_of_contragredientIso_of_dynamic`). The
   proof follows the Library proof of `nonempty_leviSecondAdjunction_of_dynamic`. Its
   inner goal is reduced to point images by `nonempty_leviSecondAdjunction_of_pointImage`,
   with `Ubar = N̄(F)`, `M(F)` and `N(F)`. Only the source of the stable-lift duality
   changes:
   - `g`, its centrality and the opposite contraction basis come from
     `exists_central_hasOppositeIwahoriContractionBasis_of_dynamic`;
   - reciprocity of the inverse-half characters comes from
     `closedInverseHalfCharacter_mul_eq_one_of_closedRestrictCharacter`;
   - for each smooth `A` and each good `K` (compact, with contractions for `(Ubar, M, N, g)`
     and `(N, M, Ubar, g⁻¹)`), step 2 is applied with
     `Mb = pointImage (mbar ≫ pbar)`, which `hP` rewrites to `M(F)`, and
     `e = leviPointsEquiv pbar mbar`. This gives stationary compression by `g` on `A~`,
     hence the upper Fitting splitting (`Jacquet.compactCompressionSplits_of_stationary`).
     The lower splitting for `g⁻¹` on `A` follows by transposition
     (`Jacquet.compactCompressionSplits_inv_of_contragredient_stationary`);
   - these discharge `Admits` through `admits_of_iwahoriContractions_of_splits`, and
     `exists_isStableLiftDuality_of_admits` gives a natural isomorphism `Ψ₀` with the
     stable-lift formula;
   - `exists_isNaturalIntegralDuality_of_compactSpace` and
     `nonempty_secondAdjunction_of_stableLift` conclude exactly as in the Library proof.

   The new isomorphism `Ψ₀` (not `Ψ`) enters the stable-lift construction.
4. *Structure inputs* (`nonempty_leviSecondAdjunction_of_contragredientIso`). The proof copies
   `nonempty_leviSecondAdjunction_of_structure`, with all structural premises supplied by
   published proofs:
   - `parabolicDynamic` and `oppositeDynamicParabolicUniqueness` give the cocharacter `χ` and
     the identifications of `N(F)`, `M(F)` and `N̄(F)`;
   - `Dynamic.leviAdjointDeterminantReciprocity` gives Haar reciprocity;
   - `RationalPointFamily.rationalReductiveUnimodularity` with `standardCocharacter` gives
     unimodularity and the modular character of `P(F)`;
   - `arbitraryParabolicQuotientCompact` gives compactness of `P(F) \ G(F)`.

The final theorem introduces the binders of the statement, installs the canonical
rational-point topology, and pairs the two implications for the given pair of parabolics.

## Helper modules (same candidate)

- `Langlands.Representation.Category.ConcreteSmoothLimits`: concrete limits of smooth
  representations, joint injectivity of projections, and extraction of fixed vectors from
  compatible families.
- `Langlands.Representation.Jacquet.ProductCompressionStationarity`: stationarity of
  compression from a power family, splitting corollaries, and transposition.
