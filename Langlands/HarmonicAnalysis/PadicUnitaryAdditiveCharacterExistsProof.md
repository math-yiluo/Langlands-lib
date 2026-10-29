# Existence of a nontrivial unitary additive character of a p-adic field

The module `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof`
proves

```lean
theorem Langlands.HarmonicAnalysis.padicUnitaryAdditiveCharacterExists {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicUnitaryAdditiveCharacterExistsStatement F T
```

whose type is exactly the published proposition
`Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement.{u} F T`.
By definition, this proposition is
`Nonempty (@UnitaryAdditiveCharacter F.Carrier _ T.topology)`. So for every
prime `p`, every finite extension `F` of `ℚ_p` in universe `u` and every supplied
realization `T`, the theorem gives an additive character `F → Circle` that is
continuous for `T.topology` and not equal to `1`. The theorem has no
hypotheses beyond those of the statement. The statement module and the modules
it imports are used unchanged.

The proof has two steps. It first builds a character of `ℚ_p` from a character
of the discrete group `ℚ_p ⧸ ℤ_p`. It then pulls that character back along the
field trace `F → ℚ_p` with the published
`PadicField.TopologicalData.traceCharacter`.

## Private helpers

These declarations are private, in the namespace
`Langlands.HarmonicAnalysis.PadicAdditiveCharacter`.

- `ratCircleToRealCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ)` is the map
  `ℚ/ℤ → ℝ/ℤ` that `QuotientAddGroup.map` induces from the cast `ℚ → ℝ`.
  `ratCircleToRealCircle_injective` proves it is injective. Take the class of a
  rational `q`. If its real image is zero, then `(q : ℝ)` is an integer `n` by
  `AddCircle.coe_eq_zero_iff`. Injectivity of the cast then gives `q = n`, so
  the class of `q` in `ℚ/ℤ` is zero. This is the argument of the private
  `rationalCircleMap` in the published `UnboundedConductorProof` module, which
  cannot be imported.
- For an abelian group `A` and `c : A →+ AddCircle (1 : ℚ)`, `toCircleAddChar c`
  is the `AddChar A Circle` given by
  `a ↦ AddCircle.toCircle (ratCircleToRealCircle (c a))`. In Mathlib,
  `AddCircle.toCircle` with period `1` sends the class of a real `t` to
  `Circle.exp (2π t)`, that is `exp(2πit)`. It takes `0` to `1`
  (`AddCircle.toCircle_zero`) and sums to products (`AddCircle.toCircle_add`).
  `toCircleAddChar_apply_eq_one_iff` proves `toCircleAddChar c a = 1 ↔ c a = 0`.
  The forward direction uses `ratCircleToRealCircle_injective` and
  `AddCircle.injective_toCircle one_ne_zero`.
- `padicIntegers p : AddSubgroup ℚ_[p]` is the additive subgroup of Mathlib's
  `PadicInt.subring p`, whose carrier is `{x | ‖x‖ ≤ 1}`, i.e. `ℤ_p`.
  `isOpen_padicIntegers` proves it is open: it is the closed ball of radius `1`
  about `0`, and in an ultrametric space such a ball is open
  (`IsUltrametricDist.isOpen_closedBall`).
  `inv_p_not_mem_padicIntegers` proves `(p : ℚ_[p])⁻¹ ∉ padicIntegers p`. By
  `norm_inv` and `Padic.norm_p`, `‖p⁻¹‖ = p`, and `p > 1` because `p` is prime.

## The character of `ℚ_p`

The public theorem `Langlands.HarmonicAnalysis.exists_padic_unitaryAdditiveCharacter`
states, for every prime `p` and the usual topology of `ℚ_[p]`,

```lean
∃ ψ : UnitaryAdditiveCharacter ℚ_[p],
  (∀ z : ℤ_[p], ψ (z : ℚ_[p]) = 1) ∧ ψ ((p : ℚ_[p])⁻¹) ≠ 1
```

It asserts no more than this. In particular, it does not claim that `ψ` is
Tate's standard character `x ↦ exp(2πi λ(x))`.

Proof. Let `L = padicIntegers p`. The class of `p⁻¹` in `ℚ_[p] ⧸ L` is nonzero
because `p⁻¹ ∉ L` (`QuotientAddGroup.eq_zero_iff`). Mathlib's
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero` supplies an additive
homomorphism `c : ℚ_[p] ⧸ L →+ AddCircle (1 : ℚ)` that is nonzero on this class.
Let `χ = toCircleAddChar (c.comp (QuotientAddGroup.mk' L))`, so `χ(y)` is the
image of `c` at the class of `y`.

- Continuity. Since `L` is open, `ℚ_[p] ⧸ L` has the discrete topology
  (`QuotientAddGroup.discreteTopology`). So `χ` is a function on a discrete space
  (continuous by `continuous_of_discreteTopology`) composed with the continuous
  quotient map (`QuotientAddGroup.continuous_mk`).
- Nontriviality. `χ(p⁻¹) ≠ 1` by `toCircleAddChar_apply_eq_one_iff`, because `c`
  is nonzero at the class of `p⁻¹`. Hence `χ ≠ 1`, since `1` takes the value
  `1` everywhere (`AddChar.one_apply`).
- Triviality on `ℤ_p`. For `z : ℤ_[p]`, the element `(z : ℚ_[p])` lies in `L`, so
  its class is zero and `χ(z) = 1`.

Packaging `χ` with these two certificates gives the required `ψ`.

## Transport to an arbitrary p-adic field

In `padicUnitaryAdditiveCharacterExists`, take `ψ` from the previous theorem and
discard its two extra properties. The base field `PadicField.rational p` is
`PadicField.ofField (Padic p)`, so its carrier is definitionally `Padic p`.
Likewise the topology of `PadicField.rationalTopologicalData p` is definitionally
the usual topology of `Padic p`. Hence `ψ` already has the type
`@UnitaryAdditiveCharacter (PadicField.rational p).Carrier _
(PadicField.rationalTopologicalData p).topology` that `traceCharacter` expects.

The proof makes `F`'s own algebra structure `F.algebra` a local instance of
`Algebra (PadicField.rational p).Carrier F.Carrier`. It proves
`IsScalarTower (Padic p) (PadicField.rational p).Carrier F.Carrier` with
`IsScalarTower.of_algebraMap_eq`: both sides of the required equation of algebra
maps agree definitionally (`rfl`). The algebra map of `PadicField.rational p` is
the identity of `Padic p`.

Then
`(PadicField.rationalTopologicalData p).traceCharacter T ψ` is an element of
`@UnitaryAdditiveCharacter F.Carrier _ T.topology`. By its published definition
it is `ψ ∘ Tr_{F/ℚ_p}`. The published declaration proves both facts needed:
continuity for the supplied topology `T.topology`, by restricting scalars to
`Padic p` and using the module topology, and nontriviality, from surjectivity of
the trace. `traceCharacter` has independent universe parameters, so the
universe-`0` base `PadicField.rational p` and the universe-`u` field `F` need no
universe lifting.

## Checks

Development `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiles the module with no errors or warnings. Inspection of
`Langlands.HarmonicAnalysis.padicUnitaryAdditiveCharacterExists` reports level
parameter `u` and the axioms `propext`, `Classical.choice` and `Quot.sound`. The
module uses no `sorry`, `admit`, new axioms or `native_decide`.

## Dependency audit

Imports of the module:

- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement` (the
  target statement);
- `Langlands.HarmonicAnalysis.CharacterTransport`;
- `Mathlib.Algebra.Module.CharacterModule`,
  `Mathlib.Analysis.SpecialFunctions.Complex.Circle`,
  `Mathlib.Topology.Algebra.Group.Quotient`.

At the module level, these are all the `Langlands` modules it imports,
directly or transitively:

- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement`, which
  imports `Langlands.LocalField.Definitions` and `Langlands.HarmonicAnalysis.Basic`;
- `Langlands.HarmonicAnalysis.CharacterTransport`, which imports
  `Langlands.HarmonicAnalysis.Basic`, `Langlands.LocalField.Definitions` and Mathlib;
- `Langlands.HarmonicAnalysis.Basic`, which imports only Mathlib;
- `Langlands.LocalField.Definitions`, which imports only Mathlib.

None of these modules is representation-theoretic. None contains or imports
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, their proof successors or conclusions. None
contains or imports any derivative statement that takes
`PadicUnitaryAdditiveCharacterExistsStatement` or an instance of it as an input.
The only use of `PadicUnitaryAdditiveCharacterExistsStatement` is as the target
type. The modules `Langlands.Representation.Whittaker.PrerequisiteInterfaces` and
`Langlands.HarmonicAnalysis.FieldTransport` are not imported.

## Provenance and authorship

The target comes from J. T. Tate, *Fourier analysis in number fields and Hecke's
zeta-functions*, in Cassels–Fröhlich, *Algebraic Number Theory* (1967), §2.2,
printed p.309 (`tate-1967-thesis`). Tate's Case 2 and Lemma 2.2.2 give the
explicit character `x ↦ exp(2πi λ(x))` of `ℚ_p`. The paragraph before Theorem
2.2.1 transports it by the trace. The implemented proof keeps Tate's trace
transport and his key properties: the character is trivial on the open
subgroup `ℤ_p` and nontrivial at `p⁻¹`. However, it obtains the character of
`ℚ_p ⧸ ℤ_p` from Mathlib's character-module duality (divisibility of `ℚ/ℤ`)
instead of Tate's explicit fractional part `λ`.

Worker 1000 wrote the Lean proof and this Markdown.
