# Integral models over `𝒪[F]` from parahoric models over the maximal unramified integers

This helper module builds the single model over `↥𝒪[F]` that the construction
of KP Axiom 4.1.20 attaches to one index. Here KP is Kaletha–Prasad, *Bruhat–Tits
theory: a new approach* (2023). Following KP §9.2.5, the construction uses
parahoric models over the integers of the maximal unramified extension
`K = inertiaFixedField F` and applies smooth model descent to `𝒪[F]` (KP
Fact 2.10.16). The main theorem takes three statements as hypotheses.

- `UnramifiedParahoricModelStatement` (KP Theorems 8.3.2 and 8.3.13 over `K`).
- `UnramifiedSmoothModelDescentStatement` (KP Fact 2.10.16).
- `UnramifiedZeroDescentStatement`. The proof uses its clause that Galois
  conjugation preserves `G(K)^1`.

Throughout, `fixedFieldIntegers F` are the integers of `K`. The module installs
the coefficient algebra `↥𝒪[F] → fixedFieldIntegers F` and its scalar tower from
Mathlib's `Valuation.HasExtension` instances, as local instances named
`unramifiedModelFamilyAlgebra` and `unramifiedModelFamilyScalarTower`. These
are the instances that define `IntegralModel.baseChangeUnramified`. A private
instance `unramifiedModelFamilyAffineHom` records that the base change of `G`
to `K` is affine; the base change is a pullback of the affine morphism
`G.X.hom`.

## Declarations

- `GroupScheme.IsSimplyConnectedDerivedCover.baseChange_field`. Let `d : D → G`
  and `π : C → D` form a simply connected derived cover over a field `k` (the
  cover used in KP Definition 2.6.20), and let `K / k` be a field extension.
  Then their base changes to `K` form one too. The proof combines three Library
  results:
  - `connectedReductiveFieldExtensionStatement`: `G_K` is connected reductive;
  - `derivedSubgroupFieldBaseChange`: `D_K` is the derived subgroup of `G_K`;
  - `isSimplyConnectedCover_fieldExtension`: `C_K → D_K` is a simply connected
    cover.
- `unramifiedZeroDatumOfParahoric P`. This is the zero datum over `K` from the
  derived cover stored in `P.zeroDatum`. It is the Library constructor
  `UnramifiedZeroDatum.ofDerivedCover` applied to the base change of that
  cover. Its `zeroPoints` subgroup is `G(K)^0` (KP Definition 2.6.23(1)). Both
  halves of the construction use this one datum.
- `rationalConjugate_mem_pointwiseFixer`. Let `Dσ` be a semilinear Galois
  action on the building data `C` over `K`, and let a set `Y` be fixed pointwise
  by `Dσ.action σ`. If `x ∈ G(K)` fixes `Y` pointwise, then so does its Galois
  conjugate `σ(x)`. The proof applies the semilinearity `Dσ.action_smul`:
  `σ(x) · σ(y) = σ(x · y)`. Then `x · y = y` and `σ(y) = y`.
- `exists_relativeComponentModelData_of_unramified`. Let `G` be connected
  reductive and let `Y = g · apartmentMap '' Ya` for a nonempty set `Ya` of the
  apartment of `C`. Assume every affine functional is bounded above on `Ya`,
  and that `Y` is fixed pointwise by every `Dσ.action σ`. Let `E` be a zero
  datum over `K`. Then there is a relative-component datum
  `D : RelativeComponentModelData ↥𝒪[F] F G` such that:
  - the base change of `D.full` to the integers of `K` has integral points
    `G(K)^1 ∩ Fix(Y)`, where `G(K)^1` is the kernel of the character
    valuations;
  - the base change of `D.neutral` has integral points `E.zeroPoints ∩ Fix(Y)`.

## Proof of the main lemma

1. `UnramifiedParahoricModelStatement` gives a relative-component datum `DK`
   over the integers of `K`. Its full model has points `G(K)^1 ∩ Fix(Y)` and
   its neutral model has points `E.zeroPoints ∩ Fix(Y)`.
2. The full integral points are stable under every `σ ∈ Aut(K/F)`:
   - `G(K)^1` is stable by the first clause of `UnramifiedZeroDescentStatement`;
   - `Fix(Y)` is stable by `rationalConjugate_mem_pointwiseFixer` and the
     hypothesis on `Y`.
3. `UnramifiedSmoothModelDescentStatement` applied to the smooth full model of
   `DK` gives a smooth model `M` over `𝒪[F]` and an isomorphism from its
   unramified base change to `DK.full` over the identity of `G_K`.
4. `G` has connected underlying space because it is connected reductive. The
   helper `RelativeComponentModelData.exists_full_eq` (module
   `RelativeComponentModelLemmas`) then gives a datum `D` with `D.full = M`.
5. The full points follow because isomorphic models over the identity have
   equal points (`IntegralModel.Iso.integralPoints_eq`).
6. The neutral points follow from the Library lemma
   `RelativeComponentModelData.baseChange_neutral_integralPoints_eq` (module
   `RelativeComponentFunctoriality`). The base
   change of `D.neutral` and `DK.neutral` have the same integral points because
   the full models are identified.

The lemma has `set_option maxHeartbeats 2000000`. Membership in the infimum
needs explicit `Subgroup.mem_inf` steps, because unification across the two
spellings `UnramifiedClosure F` and `inertiaFixedField F` is slow.

## Sources

- KP Definitions 2.6.20 and 2.6.23(1) and Lemma 2.6.24, printed pp. 104–105 /
  PDF pp. 135–136, give the image of the simply connected derived cover on
  rational points and its role in `G(k)^0`.
- KP Fact 2.10.16, printed pp. 126–127 / PDF pp. 157–158: unramified descent of
  smooth models.
- KP Theorem 8.3.2, printed p. 296 / PDF p. 327, and Theorem 8.3.13, printed
  p. 299 / PDF p. 330: the parahoric models over the maximal unramified integers.
- KP §9.2.5, printed pp. 327–328 / PDF pp. 358–359, descends the models.
  Section 9.5, printed pp. 363–364 / PDF pp. 394–395, verifies the axioms
  for the descended models.
- KP Proposition 9.3.24, printed p. 343 / PDF p. 374, gives the intersection
  identity `G(k)^0 = G(K)^0 ∩ G(k)` in the third clause of
  `UnramifiedZeroDescentStatement`. The Galois stability of `G(K)^1` used
  here is the first clause, derived by conjugating rational characters and
  using Galois invariance of the valuation in
  `UnramifiedCharacterValuationKernelGaloisStability`.

The Lean construction takes the relative identity component of the descended
full model over `𝒪[F]` and identifies its unramified points through uniqueness
of relative identity components.
