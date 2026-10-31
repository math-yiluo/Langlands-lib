# Nondegenerate pairings through normalized `Φ⁻`

Author: Worker 805. This module is the `Φ⁻` step of the proof of Bernstein–Zelevinsky
(1977), Proposition 3.8, in task `a925b519-9bb9-4927-873e-ad322d41328e` (executors
Worker 1024 and Worker 805).

## Main theorem

`Langlands.Derivative.Mirabolic.phiMinus_nondegeneratePairing T ψ m`, with universe
parameters `uF uV uW` and axioms `propext`, `Classical.choice`, `Quot.sound`:

for smooth representations `A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F)` and
`B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F)` of `P_(m+2)`, and a form
`β ∈ InvariantBilinear.forms A B (g ↦ |det g|)` (that is,
`β (g v) (g w) = |det g| β v w`, with `|det g| = T.determinantNorm (m + 1 + 1) g`)
that is nondegenerate in `A` (`β v w = 0` for all `w` forces `v = 0`), there is a form
`γ ∈ InvariantBilinear.forms (Φ⁻ A) (Φ⁻ B) (h ↦ |det h|)` on the normalized
`Φ⁻ = Mirabolic.phiMinus T ψ m`, with `|det h| = T.determinantNorm (m + 1) h`, that is
nondegenerate in `Φ⁻ A`.

No highest-derivative hypothesis is needed here. The highest-derivative hypothesis of
Proposition 3.8 is used in the other modules of the task, which prove the `Ψ⁻` step and
the assembly.

## Source and route

BZ77 (printed p.453, PDF page 14) proves the case `k > 1` of Proposition 3.8 this way.
First, `B` restricts to a pairing of `τ₁ = Φ⁺Φ⁻τ` and `π₁ = Φ⁺Φ⁻π` that is nondegenerate
in `τ₁`; this uses 3.7(c) and 3.3(a). Then 3.7(b) (printed p.453), proved through the
adjunctions of 3.2 and the comparison 3.4(b), turns it into a nondegenerate pairing of
`Φ⁻τ` and `Φ⁻π`.

The Lean proof uses neither the plus functors nor minus exactness. It restricts `β` to
`A(V) × B`, where `A(V) = span {u a − a : u ∈ V}` is the radical-relations
subrepresentation (it is `Φ⁺Φ⁻A` in BZ77's language, but this is never used). It then
transfers the restriction with the explicit twisted radical integral of the published
module `MirabolicMinusPairingTransferProof`. Nondegeneracy of the transferred form is
proved directly, by character averaging and the published finite Fourier lemma.
Finally `Φ⁻ A(V) → Φ⁻ A` is shown to be bijective. This is internal, derived
content. Its role matches BZ77 3.7(b) together with the restriction step of the 3.8
proof.

Notation: `V = radical (m + 1) F ≅ F^(m+1)` with radical elements `u(c)`
(`radicalElement c`), `θ = T.mirabolicTheta ψ m` with `θ(u(c)) = ψ(c_last)`,
`e = Pi.single (Fin.last m) 1`, `levi g` for `g ∈ GL_(m+1)`, `successor h = levi h` for
`h ∈ P_(m+1)`, and `mk` for the quotient map to the `θ`-coinvariants
`Jacquet.Localization.Coinvariants ρ V θ`, which is the carrier of `Φ⁻`.

## Lemmas and proofs

### Radical relations

- `radicalRelations_stable ρ g`: `relations ρ V 1` is stable under every `ρ g`. The
  conjugate `g u g⁻¹` lies in `V` (the published instance `radical_normal`), and
  `ρ g (ρ u v − v) = ρ(g u g⁻¹)(ρ g v) − ρ g v`.
- `radicalPart ρ`: the restriction of `ρ` to `relations ρ V 1`, built with Mathlib's
  `Representation.subrepresentation`. `radicalPart_apply` holds by `rfl`.
- `isSmooth_subrepresentation`: a stable submodule of a smooth representation is
  smooth. A vector of the submodule is fixed by the open subgroup that fixes it in the
  ambient space.

### Support and Levi perturbations

- `exists_coefficient_support_of_mem`: if `β` has covariance `|det|^(-s)` and `ξ`, `ξ'`
  are smooth, then for `v ∈ relations ξ V 1` and any `w`, the radical coefficient
  `c ↦ β (ξ (u c) v) w` vanishes outside a lattice box. The proof is that of the
  published `exists_coefficient_support`, concluding for vectors of the relation span
  instead of assuming that the span is everything. The vectors with this property form
  a submodule. For a generator `ξ(u(d)) x − x`, the published
  `exists_open_subgroup_coefficient` and `exists_mulVec_eq_add` show that the
  coefficient of `x` at `c + d` equals its value at `c` for large `c`.
- `exists_lastRow_perturbation T H`: if `H ⊆ GL_(m+1)(F)` is open and contains `1`, there
  is a lattice box such that every `r` in it has some `h ∈ H` with
  `(h c)_last = c_last + r ⬝ c` for all `c`. Take `h = 1 + e rᵀ`. The map
  `r ↦ 1 + e rᵀ` is continuous, so the preimage of `H` is a neighbourhood of `0` and
  contains a lattice box (`exists_latticeBox_subset`).

### Twisted radical integrals

- `twistedIntegral μ ψ ξ β y v w = ∫ ψ(−(y ⬝ c)) β (ξ (u c) v) w dc`. When the radical
  coefficients are continuous with compact support, the integrand is integrable
  (`integrable_twistedIntegrand`). The integral is then linear in `v`
  (`twistedFunctional`, `twistedFunctional_apply`).
- `twistedIntegral_radical`: `J_y(ξ(u d) v, w) = ψ(y ⬝ d) J_y(v, w)`, by translation
  invariance of Haar measure (`integral_add_right_eq_self`).

### The left kernel of the transfer integral

`mem_relations_of_transferIntegral_eq_zero`: let `β` have covariance `|det|^(-s)`, be
nondegenerate in `v`, and have compactly supported radical coefficients, with `ξ`, `ξ'`
smooth, and let `μ` be an additive Haar measure. If the published `transferIntegral` of
`v` vanishes against every `w`, then `v ∈ relations ξ V θ`. Proof:

1. Smoothness gives an open subgroup `K₁` fixing `v`. `exists_lastRow_perturbation`,
   applied to `levi⁻¹ K₁`, gives a box level `n₀` and, for every `y` with
   `y − e ∈ box n₀`, some `h` with `levi h ∈ K₁` and `(h c)_last = y ⬝ c`. The published
   `transferIntegral_levi` gives
   `0 = I(v, ξ'(levi h) w) = I(ξ(levi h) v, ξ'(levi h) w) = |det h|^(-s)|det h| J_y(v, w)`,
   and the constant is nonzero. So `J_y(v, w) = 0` whenever `y − e ∈ box n₀`.
2. Put `M = n(ψ) − n₀` and let `x` be the `θ`-average `characterAverage` of `v` over
   the radical box of level `M`. Then `ξ(u d) x = ψ(d_last) x` on that box. This is
   the fixed-vector property of the twisted average
   (`Compact.averageMap_mem_fixedVectors`).
3. Fix `w`. The coefficient `f(c) = β (ξ (u c) x) w` is locally constant with compact
   support. Every `y` has `J_y(x, w) = 0`:
   - if `y − e` lies in the dual box of level `n(ψ) − M = n₀`, then `J_y` is
     `θ`-equivariant on the box (`character_dotProduct_eq_one`), so
     `J_y(x) = J_y(v) = 0` (`apply_characterAverage` and step 1);
   - otherwise some `d` in the box has `ψ(d ⬝ (y − e)) ≠ 1`
     (`mem_latticeBox_of_forall_character_eq_one`). Comparing
     `J_y(ξ(u d) x) = ψ(y ⬝ d) J_y(x)` with `J_y(ψ(d_last) x) = ψ(d_last) J_y(x)` forces
     `J_y(x) = 0`.
   The published `exists_integral_character_ne_zero` then gives `f(0) = β x w = 0`.
4. So `x = 0` by nondegeneracy, and `v = v − x ∈ relations ξ V θ`
   (`sub_characterAverage_mem`).

### The descended transfer pairing

`exists_transferPairing_nondegenerate`: under the hypotheses of the previous lemma
there is a bilinear form `B` on `Coinvariants ξ V θ × Coinvariants ξ' V θ` with
`B (mk (ξ (successor h) v)) (mk (ξ' (successor h) w)) = |det h|^(-(s − 1)) B (mk v) (mk w)`
that is nondegenerate in the first variable. The construction copies the published
proof of `phiMinusPairingTransfer`: `B v w = I(v, ξ'(ε) w)` with `ε = levi(−1)`,
descended twice through `Jacquet.Localization.lift`, with covariance from
`transferIntegral_levi`. For nondegeneracy, if `B (mk v) y = 0` for all `y`, then
`I(v, w) = B (mk v) (mk (ξ'(ε⁻¹) w)) = 0` for all `w`, so `mk v = 0` by the previous
lemma.

### Normalization bridges

- `determinantNorm_eq_determinantWeight`: `|det g|` (the `T.determinantNorm` character)
  equals `determinantWeight (normalizedAbsoluteValue T) g (−(−1))`, the transfer
  module's `|det g|^(-s)` at `s = −1`.
- `phiMinusCharacter_mul_mul_determinantWeight`:
  `|det h|^(-1/2) · |det h|^(-1/2) · |det h|^(−(−1 − 1)) = |det h|`. These are the two
  normalizing twists of `Mirabolic.phiMinus` (`realPowerCharacter … (−1/2)`) against
  the covariance `|det|^2` of the unnormalized transfer, computed with
  `Complex.ofReal_cpow` and `Real.rpow_add`.
- `smul_smul_eq_of_eq`: the scalar identity `c • (c • (d X)) = x X` when `c c d = x`.

### `Φ⁻ A(V) ≅ Φ⁻ A`

- `radicalPartMap T ψ ρ : Coinvariants (radicalPart ρ) V θ → Coinvariants ρ V θ`, induced
  by the inclusion; `radicalPartMap_mk` holds by `rfl`.
- `exists_mk_radicalRelations_eq`: every class `mk v` comes from `A(V)`. Since `ψ` is
  nontrivial, pick `t` with `ψ t ≠ 1` and put `u₀ = u(t e)`. Then `θ(u₀) ≠ 1`, and
  `mk v = (θ(u₀) − 1)⁻¹ mk(ρ u₀ v − v)` with `ρ u₀ v − v ∈ A(V)`.
  `radicalPartMap_surjective` follows.
- `radicalPartMap_injective`: if `x ∈ A(V)` is a `θ`-relation in `A`, every linear
  form `f` on `Coinvariants (radicalPart ρ) V θ` gives a `θ`-equivariant form `f ∘ mk`
  on `A(V)`. The published `apply_eq_zero_of_mem_relations`, applied along the radical
  boxes of levels `0, 1, 2, …`, makes it vanish at `x`. So `mk x = 0` by
  `Module.forall_dual_apply_eq_zero_iff`.
- `exists_transport_left`: a bilinear form transported along a linear bijection of the
  first variable keeps nondegeneracy in that variable.
- `radicalPartMap_covariance`: covariance under `successor` passes from `Φ⁻ A(V)` to
  `Φ⁻ A`. Write `mk v = radicalPartMap (mk x₀)`. Then
  `mk(ρ(successor h) v) = radicalPartMap (mk (successor h · x₀))`, because the
  `θ`-relations are stable under the successor range (`relations_stable` with the
  published `theta_isInvariant`).

### Assembly

`exists_coinvariantPairing_nondegenerate` takes `ρ`, `σ` and `β` with covariance
`|det|`, nondegenerate in the first variable. It applies
`exists_transferPairing_nondegenerate` to `radicalPart ρ`, `σ` and the restriction
`β₀ = β ∘ A(V).subtype` (with `s = −1`). Nondegeneracy of `β₀` and the support lemma
are inherited from `A`. It then transports the result along `radicalPartMap` and
checks the normalized covariance against the twists
`|det h|^(-1/2) mk(ρ(successor h) v)`. `phiMinus_nondegeneratePairing` applies this to
`A.representation`, `B.representation` and `β`. The `Φ⁻` action on a class is by
definition `|det h|^(-1/2) mk(ρ(successor h) v)` (`phiMinus_action`), and general
classes reduce to `phiMinusQuotient` images (`phiMinusQuotient_surjective`).

## Import and proof-dependency audit

Imports: `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`
(published proof of the `Φ⁻` pairing-transfer statement, task
`96a1c747-9282-43a2-b8b7-d9180675f432`), `Langlands.Representation.Derivative.MinusVanishing`
(published radical boxes, coordinate characters and the radical-box exhaustion),
`Langlands.Representation.Compact.ProjectionProof` (fixed vectors of compact
averages) and `Langlands.Group.GL.MirabolicProjection` (normality of the radical).
The transitive Library import closure of these four modules has 101 modules. None
of them is a plus functor, exactness, segment, socle, multisegment, classification,
square-integrability, tempered or exhaustion module. The proof uses none of the
Zelevinsky (1980) results or derivative results excluded by the task's Independence
section, and no unpublished statement. It uses only the lemmas named above, all
published in the Library at base `d8292e5e`.
