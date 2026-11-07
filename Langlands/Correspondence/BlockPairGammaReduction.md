# The block-pair gamma law from the pair-block Euler formula

Author: Worker 1695.

This module proves that the published block-pair gamma law
`LocalFactor.PairBlock.BlockPairGamma.{uF, uP} F` (Henniart 2002, §2.4)
follows from the published pair-block Euler statement
`LocalFactor.WDEulerPairBlockStatement` at carrier universe `max uF uP`. It
packages the implication as the proposition
`LocalFactor.CommonClosureGamma.BlockPairGammaReductionStatement.{uF, uP} F`
and proves it (`blockPairGammaReduction`). It then derives the target
`Correspondence.AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F` from
multisegment datum matching, the segment-head L- and gamma formulas and the
pair-block Euler statement alone. The block-pair gamma law is no longer a
premise of that result.

The module does not prove `WDEulerPairBlockStatement`, the segment-head
formulas or datum matching. Every result that uses them takes them as explicit
hypotheses.

Throughout, `F : PadicField.{uF} p` with `[Fact p.Prime]`. `E` is an
intermediate field of the common closure, `ν = (normCharacter F E).toMonoidHom`,
`I = inertia F E`, and `Φ` is a geometric Frobenius. `block ν ρ (n+1)` is the
published uncentered block `ρ ⊗ S_(n+1)`, and `twistedFactor F E C k` is the
published zero-monodromy pair `ν^k ⊗ C`. Write `T` for the block tensor
`block ν ρ (n+1) ⊗ block ν ρ' (m+1)` and `C = ρ ⊗ ρ'`. Let `R(g)` be the action of
`g` on the inertia invariants `C^I`, and `x = q_E^(-s)` the spectral parameter.

## Statement of the reduction

```
def BlockPairGammaReductionStatement : Prop :=
  WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP} → PairBlock.BlockPairGamma.{uF, uP} F
```

The universe arguments of `WDEulerPairBlockStatement` are those of the
coefficient field (`ℂ`), the group (`weilSubgroup F E`, in `uF`) and the two
carriers. `BlockPairGamma.{uF, uP}` quantifies over `ρ`, `ρ'` with carriers in
`max uF uP`, and the reduction uses the Euler statement only there.

## Part 1: general algebra (namespace `Langlands.LocalFactor`)

- `det_one_sub_smul_eq_det_neg_mul`: if `f * g = 1` and `z ≠ 0`, then
  `det(1 - z f) = det(-(z f)) · det(1 - z⁻¹ g)`. The proof factors
  `1 - z f = (-(z f)) (1 - z⁻¹ g)`.
- `det_one_sub_smul_eq_restrict_mul_mapQ`: for an `A`-stable subspace `W`,
  `det(1 - z A)` is the factor on `W` times the factor on `V / W`. This is
  Mathlib's `LinearMap.det_eq_det_mul_det` applied to `1 - z A`.
- Telescoping: `prod_range_shift_telescope`, `prod_shift_identity_range`,
  `prod_shift_identity` and `prod_fin_shift_identity` prove, in any commutative
  monoid and for every `f : ℤ → M`,

  `∏_{i ≤ n} ∏_{j ≤ m} f(i+j-1) · ∏_{j < min(n+1,m+1)} f(n+m-j) =
     ∏_{i ≤ n} ∏_{j ≤ m} f(i+j) · ∏_{j < min(n+1,m+1)} f(j-1)`.

  For `m ≤ n`, each column `j` telescopes:
  `∏_{i ≤ n} f(i+j-1) · f(n+j) = ∏_{i ≤ n} f(i+j) · f(j-1)`. Reindexing
  `j ↦ m - j` turns `∏_j f(n+m-j)` into `∏_j f(n+j)`. The case `n ≤ m` follows
  by swapping the roles of `n` and `m`.
- `det_one_sub_smul_invariants_tensor_dual`: when inertia acts on `A ⊗ B`
  through a finite image,
  `det(1 - z g | (A∨ ⊗ B∨)^I) = det(1 - z g⁻¹ | (A ⊗ B)^I)`. It transports along
  the published `tensorDualEquiv` and then applies the published
  `eulerPolynomial_invariants_dual_eval` (module `Langlands.LocalFactor.InvariantsDual`).

## Part 2: Weil–Deligne Euler factors (namespace `Langlands.LocalFactor.WeilDeligne`)

- `eulerPolynomial_of_monodromy_eq_zero`: with zero monodromy, the Euler
  polynomial is that of the action on all inertia invariants.
- `eulerPolynomial_zeroMonodromy_twist`: for a character `χ` trivial on `I`,
  the Euler polynomial of the zero-monodromy pair `χ ⊗ C` is that of
  `χ(g) · R_C(g)` on `C^I`.
- `dual_twist_representation`, `eulerPolynomial_dual_zeroMonodromy_twist`: the
  same for the dual, with `χ(g)⁻¹` acting on `(C∨)^I`.
- `eulerPolynomial_tensor_directSum`: the Euler polynomial of a tensor of two
  finite direct sums is the double product over the summands. It applies the
  published `tensorDirectSumLeft`, `tensorDirectSumRight` and
  `eulerPolynomial_directSum`.
- `det_inertiaOperator_eq_mul`: `det(1 - z g | V^I)` is the factor on the
  monodromy kernel `(ker N)^I` (`kernelOperator`) times the factor on the
  quotient `V^I / (ker N)^I` (`quotientOperator`).

## Part 3: scalar identities (section `Scalar`)

- `gamma_scalar`: let `φ : ℕ → K` and `ψ : ℤ → K` be arbitrary, and let
  `q, E1, u, w, Eψ ∈ K`. Assume
  `∏∏ φ(i+j) = E1 · u`, `∏∏ ψ(i+j) = Eψ · w`,
  `Eψ = ∏_{j<min} ψ(n+m-j)` and `u = q · w`. Assume also `Eψ ≠ 0`, every
  `ψ(i+j-1) ≠ 0` and `∏_{j<min} ψ(j-1) ≠ 0`. Then

  `q · (E1 / ∏_{j<min} ψ(j-1)) = ∏_{i ≤ n} ∏_{j ≤ m} φ(i+j) / ψ(i+j-1)`.

  The telescoping identity and the second and third hypotheses give
  `∏∏ ψ(i+j-1) = w · ∏_j ψ(j-1)`, and the remaining step is field arithmetic.
- `scalar_shift`: `a · y · a^(-k) = y · a^(-(k-1))` for a unit `a`.

## Part 4: the block-pair gamma law (namespace `Langlands.LocalFactor.CommonClosureGamma`)

- `normCharacter_inertia`: `ν` is trivial on inertia.
- `inertia_hasFiniteImage`: a continuous representation of `weilSubgroup F E`
  has finite image on inertia. Inertia is an open compact subgroup, and the
  published continuity bridge (`Weil.bundledRepresentationContinuity_iff`,
  `Weil.representationContinuity`) turns continuity into finite image on such a
  subgroup.
- `spectralParameter_one_sub_eq`: `q_E^(-(1-s)) = ν(Φ) · (q_E^(-s))⁻¹`. It uses
  `Φ.property : ν(Φ) = q_E⁻¹`.
- `eulerPolynomial_inertiaOperator_block`: the Euler polynomial of the action
  on all of `T^I` is `∏_{i ≤ n} ∏_{j ≤ m} eP(ν(g)^(i+j) · R(g))`. The Weil action
  of `T` is that of the tensor of the two zero-monodromy pairs. The published
  `blockZeroMonodromyEquiv` and `twistedPairEquiv` decompose that tensor into
  the twisted factors `ν^(i+j) C`.
- `eval_twistedFactor`, `eval_dual_twistedFactor`: at `g` and `z`, the factor of
  `twistedFactor C k` is `det(1 - z ν(g)^k R(g))`. For continuous `C`, the
  factor of its dual is `det(1 - z ν(g)^(-k) R(g⁻¹))`.
- `det_kernelOperator_block` (uses the hypothesis `hE`): on the monodromy
  kernel of `T`,
  `det(1 - z K_T(g)) = ∏_{j<min} det(1 - z ν(g)^(n+m-j) R(g))`.
- `eval_dual_block_tensor` (uses `hE`): the factor of `T∨` is
  `∏_{j<min} det(1 - z ν(g)^(-j) R(g⁻¹))`. It applies the published reduction
  `wdEulerDualPairBlock_of_pairBlock` (module
  `Langlands.LocalFactor.WeilDeligneEulerDualPairReduction`), the published
  `tensorDualEquiv` and `det_one_sub_smul_invariants_tensor_dual`.
- `quotientValue_mul_lRatioValue_block_of_wdEuler` (uses `hE`): let `ρ`, `ρ'`
  be continuous and `s` a regular point for `T` and `Φ`. Let `t i j` be regular
  points for `twistedFactor C (i+j)` with `(t i j).val = s.val`. Then

  `quotientValue(T)(s) · lRatioValue(T)(s) = ∏_{i ≤ n} ∏_{j ≤ m} lRatioValue(twistedFactor C (i+j))(t i j)`.

  This is the conclusion of `quotientValue_mul_lRatioValue_block` in
  `Langlands.Correspondence.BlockPairEpsilon`, which assumed `BlockPairGamma`.
  Here it is proved from `hE`. The proof applies `gamma_scalar` with
  - `φ(k) = det(1 - x ν(Φ)^k R(Φ))` and
    `ψ(k) = det(1 - x⁻¹ ν(Φ)^(-k) R(Φ⁻¹))`;
  - `E1 = det(1 - x K_T(Φ))` and `u = det(1 - x Q_T(Φ))`, where `K_T` and `Q_T`
    are the kernel and quotient operators. `eulerPolynomial_inertiaOperator_block`
    and `det_inertiaOperator_eq_mul` at `Φ` give `∏∏ φ(i+j) = E1 · u`;
  - `Eψ = det(1 - x⁻¹ K_T(Φ⁻¹))` and `w = det(1 - x⁻¹ Q_T(Φ⁻¹))`. The same
    lemmas at `Φ⁻¹` give `∏∏ ψ(i+j) = Eψ · w`, and `det_kernelOperator_block`
    at `Φ⁻¹` gives `Eψ = ∏_j ψ(n+m-j)`;
  - `q = det(x · (-Q_T(Φ)))`, the value of `quotientValue`
    (`quotientCorrectionValue_det`). Since `Q_T(Φ) Q_T(Φ⁻¹) = 1`,
    `det_one_sub_smul_eq_det_neg_mul` gives `u = q · w`.

  The published `lRatioValue_eq` writes each L-ratio as the Euler factor at `x`
  over the dual Euler factor at `q_E^(-(1-s)) = ν(Φ) x⁻¹`. With `scalar_shift`,
  the dual factor of `twistedFactor C k` is `ψ(k-1)` and that of `T` is
  `∏_j ψ(j-1)`. The numerator of `lRatioValue(T)` is `E1`. The nonvanishing
  hypotheses come from the regular points: `Eψ ≠ 0` from the regularity of `s`
  for `T`, using `K_T(Φ) K_T(Φ⁻¹) = 1`; `ψ(i+j-1) ≠ 0` from the dual parts of
  the `t i j`; and `∏_j ψ(j-1) ≠ 0` from the dual part of `s`. This declaration
  raises `maxHeartbeats` to 400000.
- `blockPairGamma_of_wdEulerPairBlock`: `hE` implies `BlockPairGamma.{uF, uP} F`.
  Rewrite the gamma value of the block pair with the published
  `conditionalPairGammaValue_eq` (gamma = epsilon · L-ratio) and
  `conditionalPairEpsilonValue_block` (module `BlockPairEpsilon`). It becomes
  `(∏∏ ε_(i+j)) · quotientValue(T) · lRatioValue(T)`. Rewrite each twisted gamma
  value with `conditionalGammaValue` and
  `conditionalPairEpsilonValue_twistedFactor`, then distribute the products. The
  previous item then closes the goal.
- `BlockPairGammaReductionStatement`, `blockPairGammaReduction`: the reduction
  above as a proposition and its proof.

## Part 5: the assembled target (namespace `Langlands.Correspondence`)

- `assemblyEpsilonInheritance_of_segmentHeads_of_wdEulerPairBlock`: the target
  `AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F` follows from
  `MultisegmentHeadDatumMatching.{uF, uA} F`,
  `RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}`,
  `RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA}`, and
  `WDEulerPairBlockStatement` at `.{0, uF, uP, uP}` and at
  `.{0, uF, max uF uP, max uF uP}`. It is the published
  `assemblyEpsilonInheritance_of_segmentHeads` (module
  `Langlands.Correspondence.SegmentEpsilonInheritance`) with its block-pair gamma
  premise supplied by `blockPairGamma_of_wdEulerPairBlock`. None of these
  premises is proved here.

## Provenance and scope

Derived. Henniart 2002 (henniart-2002-characterization) §2.4 states the gamma
law for pairs of special blocks, formalized as the published
`PairBlock.BlockPairGamma`, together with the L-factor formulas for such pairs,
formalized as the published `WDEulerPairBlockStatement`. The provenance section
of `Langlands.LocalFactor.PairBlockStatement` records the argument behind the
gamma law: by Tate (4.1.6), the quotient correction and the Weil–Deligne L-ratio
combine to the L-ratio of the underlying Weil representation, and `γ` is
multiplicative on exact sequences of Weil representations. The proof here
follows that idea, but not through exact sequences. The epsilon side was split
into twisted factors in `BlockPairEpsilon`, using additivity of the system on
virtual classes. The identity `quotientValue(T) · lRatioValue(T) = ∏∏ lRatioValue(ν^(i+j) C)`
is proved from the explicit pair-block Euler formula `hE`, by linear algebra on
`T^I` and the telescoping product. Parts 1–3 are general lemmas proved from
Mathlib and published definitions. They assert no literature claim.

The module imports `Langlands.LocalFactor.InvariantsDual`,
`Langlands.LocalFactor.WeilDeligneEulerDualPairReduction`,
`Langlands.LocalFactor.WeilDeligneEulerSum`, `Langlands.WeilDeligne.TensorDual`,
`Langlands.Representation.Twist.DualProof`, `Langlands.Weil.Local.ContinuityProof`,
`Langlands.Correspondence.BlockPairEpsilon` and
`Langlands.Correspondence.SegmentEpsilonInheritance`.
