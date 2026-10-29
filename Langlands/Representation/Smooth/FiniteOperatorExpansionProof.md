# Proof of the finite operator expansion of a smooth representation of `Fˣ`

Worker 940 proves the exact published proposition
`Langlands.FiniteOperatorExpansionStatement.{uF,uV}` of module
`Langlands.Representation.Smooth.FiniteOperatorExpansionStatement` with the
closed theorem

```lean
theorem Langlands.finiteOperatorExpansion : FiniteOperatorExpansionStatement.{uF,uV}
```

in module `Langlands.Representation.Smooth.FiniteOperatorExpansionProof`. The
theorem is the complete, unapplied proposition. Its only universe parameters are
the target's independent, unrestricted universes `uF` (the field) and `uV` (the
representation space). The statement pair and every file it imports are
unchanged.

## What is proved

The theorem keeps every quantifier of the target: every natural number `p` with
`Fact p.Prime`, every `F : PadicField.{uF} p`, every `T : F.TopologicalData`, every
complex module `V : Type uV` and every actual `σ : Representation ℂ F.Carrierˣ V`.
It uses exactly the target's two hypotheses:

1. `IsSmooth σ`: every vector is fixed by some open subgroup of `F.Carrierˣ`;
2. `FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ))`: the operators `σ(a)`
   span a finite-dimensional subspace `S` of `Module.End ℂ V`.

No topology on `V`, finite-dimensionality of `V`, admissibility, finite
generation, irreducibility, character decomposition, common open kernel or
expansion certificate is assumed. The proof does not use
`JPSDecompositionStatement` or any Whittaker asymptotic statement.

**Topology.** As in the target, `F.Carrier` carries `T.topology`, and
`F.Carrierˣ` carries Mathlib's `Units` topology, induced by `u ↦ (u, u⁻¹)`.
Smoothness and the continuity of the expansion functions both refer to this
topology. The local-constancy step needs `F.Carrierˣ` to be a topological group.
The proof obtains this by installing the instances `T.valuativeRel` and
`T.localField`, which are fields of `T` stated for `T.topology`. They make
multiplication on `F.Carrier` continuous, and Mathlib's instance for units of a
monoid with continuous multiplication then applies. This adds no hypothesis and
does not change the topology.

**Normalized absolute value.** `|x|` is `T.normalizedAbs x`. For `x ≠ 0` it is
`q ^ (-T.ord x)`, where `q = T.residueCardinality > 1`. The proof uses only the
published facts that it is nonnegative and multiplicative, this formula on
nonzero elements, `q > 1`, and `|ϖ ^ n| = q ^ (-n)` for the uniformizer unit `ϖ`.

The conclusion is proved in two parts.

- **Bounded span.** `S⁺ = S`, where `S⁺` is the span of `σ(b)` over units with
  `|b| ≤ 1`.
- **Expansion.** There are one finite set `Y` and one total family `A`, chosen
  before any unit and any vector, such that the required properties hold. Every
  `η ∈ Y` is continuous and has a finite-dimensional left-translate span. Every
  `A η` with `η ∈ Y` lies in `S⁺`. For every unit `b`, including units with
  `|b| > 1`, the endomorphism identity `σ b = ∑ η ∈ Y, η b • A η` holds in
  `Module.End ℂ V`.

## Implemented proof

The module proves three reusable helper theorems in namespace `Langlands`, then
the closing theorem.

### Finitely many vectors separate a finite-dimensional operator space

`exists_finset_eq_zero_of_apply_eq_zero` takes any complex module `V` and a
finite-dimensional submodule `S` of `Module.End ℂ V`. It produces a finite set
`t` of vectors such that every `f ∈ S` vanishing at all `v ∈ t` is zero.

For each finite set `t`, let `K t` be the submodule of `S` of operators
vanishing on `t`, the infimum of the kernels of evaluation at its points. A
finite-dimensional space is an Artinian module, so Mathlib's
`IsArtinian.set_has_minimal` gives a finite set `t` for which `K t` is minimal
among these submodules. Take `f ∈ K t` and any vector `w`. Then
`K (insert w t) ≤ K t`, and minimality forces equality. Hence `f` vanishes at
`w`; since `w` is arbitrary, `f = 0`.

### Local constancy of `b ↦ σ b`

`isLocallyConstant_of_finiteDimensional_span` holds for any topological group
`G` in a separate universe `uG`. If a representation `σ` of `G` is smooth and
its operator span is finite dimensional, then `fun g => σ g` is locally constant
as a map into `Module.End ℂ V`. No topology is placed on the endomorphisms.

Apply the separation theorem to `S` to get a finite set `t`, and pick an open
subgroup `K v` fixing each vector `v`. Suppose `k` lies in `K v` for every
`v ∈ t`. Then `σ k - 1` belongs to `S`, because `1 = σ 1`, and it vanishes on
`t`. Hence `σ k = 1`. For any `a`, the set of `b` with `a⁻¹ * b ∈ K v` for all
`v ∈ t` is a finite intersection of preimages of open sets under continuous maps,
so it is open. It contains `a`, and on it
`σ b = σ a * σ (a⁻¹ * b) = σ a`.

### The bounded operators span the operator space

`boundedSpan_eq_span T σ` proves the first conjunct from the hypothesis that the
operator span is finite dimensional alone. It uses neither smoothness nor the
topology.

The inclusion `S⁺ ≤ S` is monotonicity of spans, so `S⁺` is also finite
dimensional. Let `c` be a unit with `|c| ≤ 1`. Left multiplication by `σ c`
maps `S⁺` into itself: a spanning element `σ b` with `|b| ≤ 1` goes to
`σ (c * b)`, and `|c * b| = |c| |b| ≤ 1`. Span induction extends this to all
of `S⁺`.

Fix a unit `b` and a natural number `n` with `-T.ord b ≤ n`, and put
`c = ϖ ^ n`. Here `ϖ` is
`LocalFactor.PadicAbelian.uniformizerUnit T`. Then `|c| = q ^ (-n) ≤ 1` and
`|c * b| = q ^ (-(n + T.ord b)) ≤ 1`. Left multiplication by `σ c` is
injective on `S⁺`, since `σ c⁻¹` is a left inverse. It is therefore a
surjective linear endomorphism of the finite-dimensional space `S⁺`
(`LinearMap.injective_iff_surjective`). Take `y ∈ S⁺` with
`σ c * y = σ (c * b) = σ c * σ b`. Multiplying by `σ c⁻¹` on the left gives
`y = σ b`, so `σ b ∈ S⁺`. Hence `S ≤ S⁺`.

The source derives this conjunct from a polynomial equation satisfied by every
element of the algebra. The implemented route uses the injective-implies-surjective
property of finite-dimensional linear endomorphisms instead.

### The uniform expansion

`finiteOperatorExpansion` first proves the bounded-span conjunct with
`boundedSpan_eq_span` and then rewrites the remaining goal along it. Membership
of each `A η` in `S⁺` becomes membership in `S`.

Write `s a` for `σ a` viewed as an element of `S`. Choose the finite basis
`B = Module.finBasis ℂ S` and set `χᵢ(a) = B.coord i (s a)`.

- **Continuity.** By the local-constancy theorem, `s` is locally constant.
  Hence so is each coordinate `χᵢ`, which is therefore continuous in the units
  topology.
- **Finite translate span.** Left multiplication by `σ b` maps `S` into
  itself: a spanning element `σ a` goes to `σ (b * a)`, and span induction
  extends this. Call this linear map `L_b`. The linear map
  `E : (S →ₗ[ℂ] ℂ) → (F.Carrierˣ → ℂ)`, `f ↦ (a ↦ f (s a))`, has a
  finite-dimensional source, so its range is finite dimensional. The translate
  `a ↦ χᵢ (b * a)` equals `E (B.coord i ∘ L_b)`, so the whole span of
  translates lies in the range of `E` and is finite dimensional. This is the
  target's exact `b * a` convention.
- **Distinct coordinates.** If `χᵢ = χⱼ`, then the coordinate functionals
  `B.coord i` and `B.coord j` agree on every `s a`. These elements span `S`, so
  the functionals are equal, and the linear independence of basis coordinates
  gives `i = j`.

Take `Y` to be the image of the coordinate family, as a `Finset`, and define
`A` by `Function.extend`: `A χᵢ = B i`, and `A` is zero outside `Y`. Every `A η`
with `η ∈ Y` is a basis vector, hence lies in `S = S⁺`. Since `χ` is injective,
the sum over `Y` reindexes to the sum over basis indices. The basis expansion
`s b = ∑ i, B.coord i (s b) • B i` then gives `σ b = ∑ η ∈ Y, η b • A η`
in `Module.End ℂ V` for every unit `b`.

**Operator-level uniformity.** `Y` and `A` depend only on `σ`, through the
basis `B`, and not on `b` or on any vector. The identity is an equality of
endomorphisms, so it holds for all vectors at once.

When `S = 0`, for example when `V = 0`, the basis is indexed by `Fin 0`, `Y` is
empty and both sides of the identity are zero. No nontriviality hypothesis or
separate case is needed.

## Dependencies

Library modules imported by Lean name:

- `Langlands.Representation.Smooth.FiniteOperatorExpansionStatement`: the
  target proposition. It also supplies `IsSmooth` and
  `PadicField.TopologicalData.normalizedAbs` through its own imports.
- `Langlands.LocalField.Normalization.Proof`:
  `PadicField.TopologicalData.normalizedAbs_mul`, `normalizedAbs_of_ne_zero`,
  `normalizedAbs_nonneg` and `residueCardinality_gt_one`.
- `Langlands.LocalField.Uniformizer`:
  `LocalFactor.PadicAbelian.uniformizerUnit` and `uniformizerUnit_zpow_abs`.

Mathlib modules: `Mathlib.LinearAlgebra.FiniteDimensional.Basic`,
`Mathlib.RingTheory.Artinian.Module`, `Mathlib.Topology.Algebra.Group.Units` and
`Mathlib.Topology.LocallyConstant.Basic`. The main Mathlib results used are
`IsArtinian.set_has_minimal`, `LinearMap.injective_iff_surjective`,
`Module.finBasis`, `Module.Basis.sum_repr`, `Module.Basis.linearIndependent_coord`,
`LinearMap.ext_on_range`, `IsLocallyConstant.iff_exists_open` and
`Function.extend`.

The new helper theorems `exists_finset_eq_zero_of_apply_eq_zero`,
`isLocallyConstant_of_finiteDimensional_span` and `boundedSpan_eq_span` are
proved in this module. No other Library file is added or changed. The proof
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source provenance

This proof is internal and derived. The target formalizes the opening remarks
of the proof of Proposition (2.2) in H. Jacquet, I. I. Piatetski-Shapiro and
J. Shalika, *Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979),
169–212, printed p.181 (one-based PDF page 14). Registered source
`jps-1979-gl3-i`, retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Worker 940 re-read the extracted text of that page when preparing this proof:
the definition of finite functions in (2.2), and the remarks asserting the finite
expansion `σ(a) = ∑_{χ ∈ X} χ(a) A_χ` and the spanning of the algebra by the
operators `σ(a)` with `|a| ≤ 1`. The source states these remarks without a
detailed argument. Their bounded-span justification is that every element of the
algebra satisfies a polynomial equation.

The separation-by-finitely-many-vectors argument, the local-constancy argument
and the injective-implies-surjective route to the bounded span are this
formalization's own. The basis-coordinate construction follows the published
proof `Langlands.centralOperatorExpansion` in
`Langlands.Representation.Smooth.CentralOperatorExpansionProof`; its lemmas are
not imported, because they assume admissibility and finite generation. The
source's further remark, that `X` depends only on the isomorphism class of the
algebra, is not part of the target and is not proved. No source-specific errata
for `jps-1979-gl3-i` were found in the project notes, the Library notes or the
literature collection when this proof was prepared.
