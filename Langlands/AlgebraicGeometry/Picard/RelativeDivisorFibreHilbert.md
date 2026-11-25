# Hilbert functions of relative effective divisors on fibres: the core computation

The module `Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreHilbert` is an internal helper
for the proof of `ProjectiveRelativeDivisorFibreHilbertStatement`. It reduces that statement to
the first clause of `ProjectiveFibreTwistCohomologyStatement` (uniform vanishing of higher fibre
cohomology of large twists).

Twists here are the FLT twists `twist L M n` of `ProjectiveFibreTwistCohomologyStatement`:
`M(0) = M` and `M(n + 1) = M(n) ⊗ L`, with the FLT monoidal tensor. The module removes the
Library's second (localized) monoidal instance with `attribute [-instance]`, so that `⊗` and `𝟙_`
denote the FLT structure used by the statements.

## Helper declarations

- `fltTensorIso A B : A ⊗ B ≅ tensorObj A B` is the inverse of FLT `tensorIsoSheafify`. Its
  target is the explicit sheafified tensor. `twistIsoTwistObj L M n : twist L M n ≅ twistObj L M n`
  compares the two kinds of twist.
- `twistCongr`: functoriality of `twist` in isomorphisms of both arguments.
- `pullbackTwistIso φ L M n : φ^*(twist L M n) ≅ twist (φ^* L) (φ^* M) n`, from FLT
  `pullbackTensorObjIso`.
- `isInvertible_twist`: twists of invertible modules are invertible (FLT
  `IsInvertible.tensor_monoidalV2`).
- `isLocallyFreeRankOne_of_isInvertible`: FLT invertibility gives `IsLocallyFreeRankOne`
  (`restrictFunctorIsoPullback`).
- `fibreEulerCharacteristic_eq_of_vanishing`: if `Hᵖ(Y_t, F_t) = 0` for all `p > 0`, then
  `χ(F_t) = dim H⁰(Y_t, F_t)`.

## The fibre computation: `geomFibreH0Finrank_twist_eq`

Setting:

- `B` is noetherian, `f_B : X_B ⟶ Spec B` is proper and flat, and `L` is invertible on `X_B`.
- `I` is a relative effective Cartier ideal with closed immersion `i : E ⟶ X_B` and ideal module
  `K`.
- `L_E` is an invertible module on `E` with an isomorphism `i^* L ≅ L_E`.
- `sk : B →+* k` with `k` a field, and `t` is the image point.

Fix `n`. Assume that `Hᵖ(X_t, K(n)_t) = 0` and `Hᵖ(X_t, 𝒪(n)_t) = 0` for all `p > 0`. Then

`geomFibreH0Finrank (i ≫ f_B) (𝒪_E(n)) k sk = χ(𝒪(n)_t) − χ(K(n)_t)`.

Proof, as implemented:

1. Let `X_t` be the fibre of `f_B` over `t` (projection `b : X_t ⟶ X_B`) and `E_t` the fibre of
   `i ≫ f_B` (projection `p`). The lift `i_t : E_t ⟶ X_t` makes the square
   `IsPullback p i_t i b` cartesian (`IsPullback.of_bot`), and `i_t ≫ (X_t ⟶ Spec κ(t))` is the
   structure map of `E_t`.
2. `b^*(ι)` is a monomorphism (`mono_pullback_fst_kernelModuleι`, which needs the flatness of
   `E`). Hence the base-changed divisor sequence `b^*(K) → b^*𝒪 → b^*(i_*𝒪_E)` is short exact.
   Twisting it `n` times by `L_t = b^* L` (`twistSeq`) keeps it short exact.
3. Its terms are identified as follows.
   - The first term is `fibreModule f_B t (K(n))` (`twistSeq_X₁`, `twistIsoTwistObj`,
     `pullbackTwistIso`).
   - The second term is `fibreModule f_B t (𝒪(n))`.
   - The third term is `(i_t)_*` of a twist of `𝒪_{E_t}` (`structurePushforwardBaseChangeIso` and
     `twistPushforwardIso`). That twist is `fibreModule (i ≫ f_B) t (𝒪_E(n))` (pullback
     compositions along `i_t ≫ b = p ≫ i` and FLT `pullbackTensorUnitObjIso`).
4. `H¹` of the first term vanishes by hypothesis. `H⁰` of the second term is finite dimensional
   by `properFlatFibreCohomologySemicontinuity` (first clause). So
   `finrank_relativeGlobalSections_X₃` gives `h⁰(third) = h⁰(second) − h⁰(first)`.
5. By `fibreEulerCharacteristic_eq_of_vanishing`, `h⁰(first) = χ(K(n)_t)` and
   `h⁰(second) = χ(𝒪(n)_t)`.
6. The global sections of `(i_t)_* G` over `κ(t)` are those of `G` over `E_t`
   (`Scheme.Modules.pushforwardComp`). So `h⁰(third) = dim H⁰(E_t, 𝒪_E(n)_t)`. This equals
   `geomFibreH0Finrank` by `GeometricFibreSectionsDim.geomFibreH0Finrank_eq`, applied to the proper
   flat morphism `i ≫ f_B`.

## The reduction: `projectiveRelativeDivisorFibreHilbert_of_twistCohomology`

`ProjectiveFibreTwistCohomologyStatement → ProjectiveRelativeDivisorFibreHilbertStatement`. In the
setting of the statement, apply the first clause of the hypothesis at `t` over `T = Spec B` to
`F = K` and to `F = 𝟙`. This gives a bound `n₀ = max n₁ n₂` for the vanishing of all higher fibre
cohomology of `K(n)` and `𝒪(n)` at `t`. Then apply `geomFibreH0Finrank_twist_eq` with
`L = pB^* 𝓛X`, `L_E = (i ≫ pB)^* 𝓛X` and `pullbackComp` as the comparison.

Kleiman's argument (S. L. Kleiman, *The Picard scheme*, literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`, proof of Theorem 4.8, p.30) uses Euler
characteristics on the geometric fibre. The Lean proof works on the fibre over `t` and needs only
`H⁰` and `H¹`. Field extension enters only through `GeometricFibreSectionsDim`.

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
