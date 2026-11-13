# Lower bound for the split rank of the symplectic group of an antihermitian form

Lean module: `Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankLower`
(namespace `Langlands.GroupScheme.AntihermitianSplitRank`).

Main result:

```
theorem wittIndex_le_splitRank (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
    (H : Matrix (Fin m) (Fin m) D) (hH : σ.IsAntihermitian H) (hu : IsUnit H) :
    (σ.wittIndex H : ℕ∞) ≤ splitRank (σ.symplecticGroup H)
```

for any field `K` (finite fields included) and finite-dimensional central division
`K`-algebra `D`.

## Provenance

The other half of Tits's formula (Tits 1966, Table II, type `C_n`): the hyperbolic planes of a
Witt decomposition carry a split torus of the group. The proof is direct from the Library
definitions; all other declarations are internal auxiliary constructions.

## Proof

1. **Monomials.** `monomial a t = ∏ₖ t_k^{a_k}` on `(Rˣ)^I`, a monoid homomorphism, additive
   in `a` (`monomial_add`, `monomial_sum`), with `monomial (Pi.single k 1) t = t k` and
   natural in `R` (`map_monomial`).
2. **Weighted diagonal units.** For `w : n → ℤ^I`, `weightUnits` sends `t` to the diagonal
   unit `diag(t^{w i})` of `R ⊗ M_n(D)`, built from the published `diagUnit`/`diagRingHom`
   of `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankLower`. It is natural
   (`weightUnits_map`), injective when every `Pi.single k 1` is a weight
   (`weightUnits_injective`, via `diagRingHom_injective`), an isometry of any `G` supported
   where the weights add to zero (`weightUnits_isometry`: through `coefficientEquiv` the unit
   is `diagonal (t^{w i} ⊗ 1)`, fixed by `σ`, and the `(i, j)` entry becomes
   `t^{w i + w j} ⊗ G i j`), and of reduced norm one when `∑ w i = 0`
   (`reducedNorm_weightUnits`, by the published `reducedNorm_diagRingHom_eq_one`).
3. **The scheme morphism.** `weightPoints` transports `weightUnits` through
   `splitTorus.pointsEquiv` and `FiniteAlgebraUnits.pointsEquiv`; naturality gives
   `weightHom : 𝔾ₘ^I ⟶ (units of M_n(D))` by `homOfPoints`, a monomorphism under the
   separation hypothesis (`mono_weightHom`). By `mem_range_symplecticAmbientι_iff` (unitary
   and reduced norm one; the norm via `reducedNormHom_points`) its range lies in the
   symplectic group (`range_weightHom_le`), so it lifts (`liftOfLE`) to
   `symplecticTorus : 𝔾ₘ^I ⟶ σ.symplecticGroup G`.
4. **Closedness.** The lift is a monomorphism; `σ.symplecticGroup G` is affine and locally of
   finite type (closed in the unit group); `IsTorus.isClosedSubgroup_of_mono` makes it a
   closed subgroup, and `card_le_splitRank` gives `|I| ≤ splitRank`
   (`card_le_splitRank_of_weights`).
5. **Conclusion.** `exists_wittBasis` (module `AntihermitianWittBasis`) gives an invertible
   `P` and weights in `ℤ^{Fin r}`, `r = σ.wittIndex H`, for `G = P H ᵗP^σ`;
   `symplecticGroupCongr` and `splitRank_eq_of_iso` identify the split ranks for `H` and
   `G`; the weights are transported to `ULift (Fin r)` to match the universe.
