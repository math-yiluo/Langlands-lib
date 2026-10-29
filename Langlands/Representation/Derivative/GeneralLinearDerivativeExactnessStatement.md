# Exactness of the general-linear derivatives

Author: Worker 749.

This module states that every published Bernstein–Zelevinsky derivative
`generalLinearDerivative T ψ N k hk` of
`Langlands.Representation.Derivative.Iteration` preserves short exact
sequences. It has one Prop-valued definition, the principal proposition
`Langlands.Derivative.GeneralLinearDerivativeExactnessStatement.{uF, uV} F T`.
It proves nothing and constructs no functor. Exactness of the derivatives
remains a proof obligation.

## The principal proposition

The parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with level parameters in the order `uF, uV`. The
carrier universe `uV` is independent of `uF`. The body installs
`letI := T.topology`, so all groups carry the topology supplied by `T`. No
canonical topology is substituted and `F` is not made canonical. The Lean body
is

```
∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N),
  Mirabolic.MapsShortExactIntertwiners (generalLinearDerivative.{uF, uV} T ψ N k hk)
```

Here `ψ` has the type `@UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The functor
`generalLinearDerivative T ψ N k hk` goes from
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)` to
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N - k) F.Carrier)`. Carriers stay in
`Type uV`; `uV` is not replaced by `max uF uV`.

The helper `Mirabolic.MapsShortExactIntertwiners` is the published one from
`Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`, used
unchanged. With the helper unfolded, the proposition says: for every `ψ`,
`N`, `k`, `hk : k ≤ N`, all objects `A B C` of
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)` and all morphisms
`i : A ⟶ B` and `q : B ⟶ C`, if

```
Function.Injective (SmoothRep.hom i)
Function.Surjective (SmoothRep.hom q)
LinearMap.range (SmoothRep.hom i).toLinearMap =
  LinearMap.ker (SmoothRep.hom q).toLinearMap
```

then, writing `D = generalLinearDerivative T ψ N k hk`,

```
Function.Injective (SmoothRep.hom (D.map i)) ∧
LinearMap.range (SmoothRep.hom (D.map i)).toLinearMap =
  LinearMap.ker (SmoothRep.hom (D.map q)).toLinearMap ∧
Function.Surjective (SmoothRep.hom (D.map q))
```

`SmoothRep.hom` returns the actual intertwiner underlying a morphism. The
hypotheses say that `0 → A → B → C → 0` is exact on the underlying complex
vector spaces, and the conclusion says the same of `0 → D A → D B → D C → 0`.
During development the proposition was checked to be definitionally equal
(`Iff.rfl`) to this unfolded form.

The proposition concerns the actual morphisms `D.map i` and `D.map q` of the
named published functor. It is not a statement about isomorphism classes,
Grothendieck groups, homology or a replacement functor. It adds no
finite-length, admissibility, irreducibility or other hypothesis on `A`, `B`,
`C`, and no exactness or classification result is a premise. In particular,
the proposition `Mirabolic.MinusExactnessStatement` of the imported module is
not assumed. Only its helper is used.

## The functors covered

The published construction fixes what `D` is:

- `k = 0`: `generalLinearDerivative T ψ N 0 hk` is the identity functor of
  `SmoothRep ℂ (GeneralLinear N F.Carrier)` (`generalLinearDerivative_zero`).
  This is the source's `π^(0) = π`.
- `k + 1 ≤ N`: `generalLinearDerivative T ψ N (k + 1) hk` is
  `generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙ generalLinearDerivativePositive T ψ (N - (k + 1)) k`
  (`generalLinearDerivative_succ`). The positive derivative is
  `generalLinearRestriction T (n + k) ⋙ phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`
  with `n = N - (k + 1)` (`generalLinearDerivativePositive_eq_comp`). This is
  restriction to the mirabolic subgroup `P_N`, then `k` steps of the
  determinant-normalized `Φ⁻`, then the determinant-normalized `Ψ⁻`. The
  rank cast transports along `N = N - (k + 1) + k + 1`.

All ranks and orders with `k ≤ N` are included:

- `N = 0`: only `k = 0`, the identity functor of `SmoothRep ℂ (GeneralLinear 0 F.Carrier)`.
- `k = 0`, any `N`: the identity functor.
- `N = 1`: `k = 0` gives the identity. `k = 1` gives
  `generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0`, the functor
  `GL_1 → P_1 → GL_0` (`generalLinearDerivative_one_one`).
- `k = N`: the functor has target `GL_(N - N)` as published. The statement is
  about this functor itself. It does not compose with the extra cast
  `Nat.sub_self N` used by the published top equations.

Orders `k > N` are not covered, since the published wrapper requires
`hk : k ≤ N`. The character `ψ` enters the functor only through `Φ⁻`. For
`k ≤ 1` there is no `Φ⁻` step.

`UnitaryAdditiveCharacter` bundles continuity for `T.topology` and
nontriviality. The statement therefore says nothing about the trivial additive
character.

## Source and provenance

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Page
numbers below are printed numbers, with one-based PDF pages in parentheses.

- §3.2, printed pp.450–451 (PDF pages 11–12): `Ψ⁻ = r_{V,1}` and
  `Φ⁻ = r_{V,θ}`, normalized as in §1.8. Proposition 3.2(a), p.451: "All the
  functors `Ψ⁻, Ψ⁺, Φ⁻, Φ⁺, Φ̂⁺` are exact."
- §3.5, printed p.452 (PDF page 13): for `τ ∈ Alg P_n`,
  `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ) ∈ Alg G_(n-k)` for `k = 1, …, n`. Footnote (2):
  `(Φ⁻)^m` is the composite `Alg P_n → Alg P_(n-1) → … → Alg P_(n-m)`.
- §4.3, printed p.454 (PDF page 15): for `π ∈ Alg G_n`, `π^(0) = π` and
  `π^(k) = (π|_(P_n))^(k)` for `k = 1, …, n`, where `π|_(P_n)` is the
  restriction to `P_n`.

No applicable errata entry was found in the central library, the literature
index or the public notes. The published `MirabolicMinus`, `Iteration` and
`MirabolicMinusExactnessStatement` pairs record the same.

### What the source asserts

The source asserts exactness of `Ψ⁻` and `Φ⁻` (Proposition 3.2(a)). It defines
the derivatives as the composites above. The pages cited do not state
exactness of `π ↦ π^(k)` as a separate numbered assertion.

### Derived provenance

The statement is an internally derived consequence of these source facts, not
a quotation. A proof is expected to combine the following facts:

- the identity functor is exact, which covers `k = 0`;
- restriction is exact: it keeps carriers and underlying linear maps
  (`generalLinearRestriction_map_toLinearMap`);
- `Ψ⁻` and `Φ⁻` are exact (Proposition 3.2(a)). For the Library's
  determinant-normalized functors this is clauses 3 and 4 of the published
  statement `Mirabolic.MinusExactnessStatement`, which is not yet proved;
- the composite of functors preserving short exact sequences preserves them,
  which covers the iterate `phiMinusIterate` and the composite with `Ψ⁻`;
- the rank cast `generalLinearRankCast` is `Eq.rec` of the identity functor
  along an equality of ranks. It is internal packaging, not a source
  construction, and it changes no map (`generalLinearRankCast_map_heq`).

The Library normalizes `Ψ⁻` and `Φ⁻` by the fixed determinant twists
`|det|^(-1/2)`, where the source uses `mod_V^(-1/2)`. A fixed character twist
keeps carriers and underlying linear maps. Exactness of underlying linear maps
therefore does not depend on the normalizing character, and no Haar-modulus
comparison is needed for this statement.

### Internal packaging

The formulation by underlying linear maps via `SmoothRep.hom` and the literal
injectivity, `range = ker` and surjectivity conditions follows the task
contract. Reusing the helper `MapsShortExactIntertwiners` and quantifying `ψ`,
`N`, `k` and `hk` in one proposition are internal choices.

## Remaining proof obligation

A proof of `GeneralLinearDerivativeExactnessStatement F T` must show
`MapsShortExactIntertwiners (generalLinearDerivative T ψ N k hk)` for every
`ψ`, `N` and `k ≤ N`, with no added hypothesis. It needs an actual proof of
exactness for the normalized minus functors `Mirabolic.psiMinus` and
`Mirabolic.phiMinus`. The published Prop-valued definition
`Mirabolic.MinusExactnessStatement` is only a statement and is not such a
proof. The remaining steps are elementary: identity, composition, restriction
and the rank cast.

## Imports and independence

The module imports `Langlands.Representation.Derivative.Iteration`, for the
derivative functors, and
`Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`, for the
helper `MapsShortExactIntertwiners`. Not counting this module, its `Langlands`
import closure has 52 modules: these two, `MirabolicMinus`,
`MirabolicCharacter`, and modules on groups, local fields, smooth
representations, twists, coinvariants and localization, matrix coefficients
and Whittaker characters. `Representation/Dual/Definitions` in the closure
only builds algebraic dual maps of intertwiners; it is not a duality theorem.
The closure contains no classification, segment, multisegment,
square-integrable, tempered, socle, irreducibility, plus-functor or filtration
module, and it does not contain `Representation/CompactCoefficient/GroupTransport`.

Neither the module nor its closure uses `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
`UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, or any result of the excluded exhaustion,
existence, coverage, conversion, uniqueness, socle-commutation, gluing or
segment-classification tasks. No plus functor, adjunction, duality, derivative
filtration, pairing, segment or classification result is used or stated.
