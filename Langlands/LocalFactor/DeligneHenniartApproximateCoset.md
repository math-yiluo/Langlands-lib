# The approximate Deligne–Henniart witness coset

Supporting lemmas for the approximate uniqueness clause of Deligne–Henniart
1981, Theorem 4.2 (printed pp. 108–109, PDF pp. 20–21). Part (i) of that
theorem says that the element `γ` satisfying 4.2.1 up to roots of unity of
`p`-power order is unique modulo `U(1)`. In the Library target
`VirtualStabilityStatement` this is the clause

`∀ γ₀', ApproximateWitness F e ε v a ψ γ₀' ↔ γ₀' * γ₀⁻¹ ∈ principalUnits 1`

for `a = minimumBreak F v hv`. The published helper
`approximateWitness_coset` (in `DeligneHenniartWitnessGroups`) reduces this
clause to zero input `v = 0`. This module identifies the zero-input
approximate witnesses with the principal units of level `1` of the bottom
field `(baseExtension F).field`. By DH81 0.1, `U(1) = {u : v(u - 1) ≥ 1}` is
the principal-unit group of level `1`.

The coset lemmas use unproved published propositions. Each one is an
explicit hypothesis, with the same names as in the published helper module
`DeligneHenniartExactCoset`:

- `hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F`. Only the
  inclusion `⊇` uses it.
- `hreal : AbsoluteReciprocityRealUnitImages.{uF}`,
  `hinert : AbsoluteUpperInertia F F.canonicalTopologicalData`,
  `hcmp : UnitFiltrationComparison.{uF}`, and
  `he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
  (Correspondence.baseReciprocityCandidate F eC)`. These are the inputs of
  `baseUpperGroup_map_reciprocityUnits` (module `DeligneHenniartUpperUnits`).
- In the last corollary, `he` is replaced by
  `hgeo : CommonClosureGeometricStatement.{uF, uF}`, through
  `geometric_baseReciprocityCandidate`.

## Unit-group facts for a p-adic field

These lemmas are stated for an arbitrary `T : F.TopologicalData` of a p-adic
field `F` and need no hypotheses. They live in the namespace
`Langlands.PadicField.TopologicalData`.

- `discreteValuation_prime_le`: the base prime `p` has discrete valuation at
  most `exp (-1)`. This follows from the published `ord_prime_pos`, since
  `ord x = -log (discreteValuation x)`.
- `pow_prime_mem_principalUnits_succ`: let `n ≥ 1` and let `u` be a principal
  unit of level `n`. Then `u ^ p` has level `n + 1`. Proof: put
  `x = u - 1`. Then `x` is integral, with valuation at most `exp (-n)`.
  Mathlib's `exists_add_pow_prime_eq`, applied in the integer ring, gives an
  integral `r` with `(x + 1) ^ p = x ^ p + 1 + p * x * r`. So
  `u ^ p - 1 = x ^ p + p * x * r`. The first term has valuation at most
  `exp (-p n) ≤ exp (-(n + 1))`, because `p ≥ 2` and `n ≥ 1`. The second has
  valuation at most `exp (-1) * exp (-n) * 1`. Also `u ^ p` has valuation `1`.
- `pow_prime_pow_mem_principalUnits`: a principal unit `u` of level `1`
  satisfies `u ^ (p ^ k) ∈ principalUnits (k + 1)` for every `k`. Proof:
  induction on `k`, using the previous lemma.
- `pow_residueCardinality_sub_one_mem_principalUnits`: let `u` have valuation
  `1`, and let `q = residueCardinality`. Then `u ^ (q - 1)` is a principal
  unit of level `1`. Proof: the residue of `u` in the finite residue field is
  nonzero, because `u` is a unit of the integer ring. By Mathlib's
  `FiniteField.pow_card_sub_one_eq_one`, its `(q - 1)`th power is `1`. So
  `u ^ (q - 1) - 1` lies in the maximal ideal and has valuation `< 1`, that
  is, at most `exp (-1)`.
- `coprime_residueCardinality_sub_one`: `q - 1` is coprime to `p ^ n` for
  every `n`. This uses the published `residueCardinality_eq_pow`
  (`q = p ^ f`) and `residueDegree_pos` (`f ≥ 1`). If `p` divided `p ^ f - 1`,
  it would divide `1`.
- `twoPowOrdCharacter` (definition): the unramified quasicharacter
  `x ↦ 2 ^ ord x` of `F.Carrierˣ`, for the topology of `T`. As a homomorphism
  it is the composite of the quotient map by `principalUnits 0` (the integral
  units), the published `orderHom` descended to that quotient, and
  `n ↦ 2 ^ n`. It is continuous because the quotient is discrete
  (`principalUnits_isOpen`).
  - `twoPowOrdCharacter_apply`: its value at `x` is `2 ^ ord x`, by `rfl`.
  - `multiplicativeConductor_twoPowOrdCharacter`: its conductor is `0`. It is
    unramified, because integral units have order `0`.
  - `discreteValuation_eq_one_of_twoPowOrd`: if `(2 ^ ord x) ^ (p ^ n) = 1`,
    then `x` has valuation `1`. Taking complex norms gives
    `(2 ^ ord x) ^ (p ^ n) = 1` in the reals. Hence `2 ^ ord x = 1`, so
    `ord x = 0`.

## The zero-input approximate witnesses

- `approximateWitness_zero_of_mem_principalUnits` (assumes `hthr`, `hreal`,
  `hinert`, `hcmp`, `he`, `AdditiveRelation F ε`, and `0 ≤ a`): every
  principal unit `δ` of level `1` satisfies `ApproximateWitness F eC ε 0 a ψ δ`.
  Proof: rewrite with the published `approximateWitness_iff`. For zero input
  the assignment value is `1` (`value_zero`). Given a degree-zero test `w`
  with `AllBreaksBelow F w a`, take the exponent `n = ⌈a⌉₊`. Then
  `δ ^ (p ^ n)` has level `n + 1 ≥ ⌈a⌉₊`. The published
  `fieldDeterminant_eq_one_of_mem_principalUnits` (with `t = a`) shows that
  the field determinant of `w` is trivial there. So the determinant value at
  `δ`, raised to `p ^ n`, equals `1 = 1 ^ (p ^ n)`. DH81 states this
  inclusion implicitly, in the phrase "défini de façon unique mod* U(1)" of
  4.2(i).
- `exists_pow_eq_one_of_approximateWitness_zero` (assumes `hreal`, `hinert`,
  `hcmp`, `he`, `AdditiveRelation F ε`, and `0 < a`; no `hthr`): let `δ` be a
  zero-input approximate witness, and let `η` be a bottom-field character of
  conductor at most `1`. Then `η δ ^ (p ^ n) = 1` for some `n`. Proof: put
  `r = min a 1 / 2`, so `0 < r < a` and `⌈r⌉₊ ≥ 1`. By
  `baseUpperGroup_map_reciprocityUnits` at `r`, the character
  `baseWeilCharacter F eC η` is trivial on `upperGroup F r`. So the test
  `lineDifference (baseWeilCharacter F eC η)` has degree `0` and all labels
  below `a` (`allBreaksBelow_lineDifference`). A Haar measure exists. The
  witness condition for this test, rewritten with
  `fieldDeterminant_reciprocityUnits`, `determinantCharacter_realizeAtBase`,
  `determinantCharacter_lineDifference` and `baseWeilCharacter_apply`, gives
  the claim.
- `mem_principalUnits_of_approximateWitness_zero` (same hypotheses): every
  zero-input approximate witness `δ` is a principal unit of level `1`. This
  is the argument of DH81 4.2(iii) (printed pp. 108–109). Proof:
  - Valuation: apply the previous lemma to the unramified character
    `twoPowOrdCharacter`, whose values `2 ^ k` with `k ≠ 0` are not roots of
    unity. This gives `ord δ = 0`, so `δ` has valuation `1`. DH81 makes the
    same choice of an unramified `η` with `η(γ γ₀⁻¹)` not a root of unity of
    `p`-power order.
  - Level one: by the published criterion
    `PadicAbelian.mem_principalUnits_iff_bounded_characters`, it suffices to
    show `η δ = 1` for every `η` of conductor at most `1`. The previous lemma
    gives `η δ ^ (p ^ n) = 1`. Also `δ ^ (q - 1)` has level `1`, so
    `η δ ^ (q - 1) = 1`. Since `q - 1` and `p ^ n` are coprime, `η δ = 1`.
    This is DH81's remark that `U(0)/U(1)` has order prime to `p`.
- `approximateWitness_zero_iff` (assumes `hthr`, `hreal`, `hinert`, `hcmp`,
  `he`, `AdditiveRelation F ε`, and `0 < a`): for every `δ`,
  `ApproximateWitness F eC ε 0 a ψ δ` holds if and only if `δ` is a principal
  unit of level `1`.
- `approximateWitness_iff_mem_coset` (same hypotheses): if `γ₀` is an
  approximate witness for `(v, a, ψ)`, then `γ₀'` is one if and only if
  `γ₀' * γ₀⁻¹` is a principal unit of level `1`. Proof: compose
  `approximateWitness_coset` with `approximateWitness_zero_iff`.
- `approximateWitness_iff_mem_coset_of_isSystem` (assumes `hthr`, `hreal`,
  `hinert`, `hcmp`, `hgeo`): the same statement for `IsSystem F eC ε`, a
  lattice element `v` with nonempty break support `hv` and
  `PositiveBreakSupport F v`, and `a = minimumBreak F v hv`. This is the
  approximate coset clause of `VirtualStabilityStatement`, relative to any
  approximate witness `γ₀`. The conjuncts of `IsSystem` give `he` and
  `AdditiveRelation`. Positivity of `a` comes from
  `positiveBreakSupport_iff_minimumBreak_pos`.

## Scope

The module does not prove the existence of an approximate or exact witness,
the valuation formula, or the compatibility `γ * γ₀⁻¹ ∈ principalUnits 1`
between the exact and approximate witnesses. It does not prove any of the
hypotheses listed above. The private lemma `haarMeasure_nonempty'` repeats
the private Haar-existence lemma of `DeligneHenniartExactCoset`.
