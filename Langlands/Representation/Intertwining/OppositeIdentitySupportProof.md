# Proof of the identity support image for opposite rational parabolics

Author: Worker 200. Module
`Langlands.Representation.Intertwining.OppositeIdentitySupportProof`.

The theorem
`Langlands.Aubert.General.RepresentedParabolic.oppositeIdentitySupport`
has exactly the published type `OppositeIdentitySupportStatement.{u, v}`, at
the independent field/group universe `u` and representation-carrier universe
`v`. No hypothesis is added: it applies to every connected reductive `G` over a
nonarchimedean local field, to arbitrary represented rational parabolics
`P = MN` and `Q = MU` with the same actual Levi map (`lQ ≫ q = l ≫ p`) and
`P(F) ∩ Q(F) = M(F)`, and to every smooth complex representation `σ` of
`M(F)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The support filtration of `r_Q ∘ i_P` and the identification of its identity
piece with the identity functor are VII.3.1–VII.3.2 (printed pp.232–234 /
PDF pp.238–240). The final paragraph of the proof of Lemma VII.4.1 (printed
p.242 / PDF p.248) uses that `1̄` is maximal for the Bruhat order of
`P̄ \ G / P`, that is, the identity double coset is open and dense. The Lean
proof follows this route; the density is proved below from published
algebraic geometry rather than from root data.

## Density of the identity double coset

`dense_identityParabolicDoubleCoset_of_opposite` proves that the identity
double coset `P(F) Q(F)` is dense in `G(F)` for the canonical evaluation
topology `RationalPointFamily.pointTopology`.

1. `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` (with
   `parabolicDynamic` and `dynamicGeometricUnipotentRadical`) gives a
   cocharacter `χ` with `P = P(χ)` and `M = Z(χ)` as subgroup functors.
2. `pointImage_opposite_radical_eq_dynamic` (with
   `oppositeDynamicParabolicUniqueness`) uses the common Levi and the
   hypothesis `P(F) ∩ Q(F) = M(F)` to identify the rational points of the
   unipotent radical `U` of `Q` with the rational points of the dynamic
   contraction subgroup `U(χ⁻¹)`.
3. `Plancherel.rationalDynamicOpenCellBoundary` writes the complement of the
   open cell `{a v⁻¹ : a ∈ P(χ)(F), v ∈ U(χ⁻¹)(F)}` as the preimage, under
   evaluation at the closed point, of a proper Zariski-closed subset `Z` of
   the underlying scheme of `G`.
4. `G` is smooth and connected, so its scheme is integral
   (`Plancherel.RationalCellConull.noetherian_and_integral`), and
   `Plancherel.RationalCellConull.interior_evaluation_preimage_eq_empty`
   shows that this preimage has empty interior. Hence the open cell is dense
   (`interior_eq_empty_iff_dense_compl`).
5. Each cell element `a v⁻¹` lies in `P(F) Q(F)`, because `a ∈ P(F)` and
   `v ∈ U(F) ⊆ Q(F)` (`pointImage_comp_le`); membership in the identity double
   coset is checked through `DoubleCoset.mem_quotToDoubleCoset_iff` and
   `DoubleCoset.eq`. A set containing a dense set is dense.

## The identity support image

In `oppositeIdentitySupport`, write `S = F^{≤1̄}` (`closureSupportImage`) and
`T = F^{<1̄}` (`boundarySupportImage`) at the identity double coset.

1. By density, the closure of `P(F) Q(F)` is all of `G(F)`.
2. `F̃^{≤1̄}(σ)` (`closureVanishingSubfunctor`) consists of the induced
   functions vanishing on that closure
   (`Geometric.mem_rawSmoothVanishingSubfunctor_iff`), so it is zero, and its
   image `S(σ)` in the Jacquet module is the zero submodule.
3. The pulled-back denominator `S.lowerInUpper T σ` is therefore zero, and
   `Submodule.quotEquivOfEqBot` gives an equivariant linear equivalence from
   `T(σ)` to the actual quotient `S.quotientObj T σ`; equivariance holds by
   definition of the quotient action.
4. The accepted theorem `pqSupportGraded` (`PQSupportGradedStatement`,
   applied with the common Levi equality `l ≫ p = lQ ≫ q`) supplies an
   equivariant linear equivalence `(F^{<1̄}/F^{≤1̄})(σ) ≃ σ`. Composing the
   two equivalences gives the required equivalence `T(σ) ≃ σ`.
