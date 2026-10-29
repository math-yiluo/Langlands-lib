# Reducibility of an adjacent two-supercuspidal product

Author: Worker 480. The exact proposition body was supplied in Worker 892's
task specification and is retained unchanged.

`Langlands.Classification.TwoSupercuspidalAdjacentProductReducible.{uF,uV} F T`
states the reducibility step of Zelevinsky 1980, Proposition 1.11(b), for
actual upper normalized induced representations over p-adic fields.
It is a Prop-valued definition, not a proof. Compiling this module does not
establish reducibility.

## Original source and scope

Ze80 Proposition 1.11(b), printed p.175 / PDF p.12, considers irreducible
cuspidal representations of equal rank with either factor isomorphic to the
other twisted by `ν = |det|`. It states length two and a unique nonzero proper
submodule, with prescribed Jacquet modules. The proof isolates the remaining
step that `ρ × νρ` is reducible, after using BZ77 §2.16(1) for the algebraic
structure. Ze80 Theorem 1.9 supplies the passage between the two orders in
the sketch. The present proposition isolates only nonirreducibility under
the two adjacent alternatives. It does not assert the length, uniqueness, or
Jacquet descriptions.

BZ77 Remark 4.2(2), printed p.454 / PDF p.15, announces reducibility when one
cuspidal factor is the `ν` twist of another. That announcement is not a proof.
Ze80 §1.11 explicitly supplies only a sketch of the analytic step.

The originals allow a general nonarchimedean local field. This proposition
specializes to the existing `PadicField` objects, finite extensions of
`ℚ_p`, and makes no claim about positive-characteristic local fields.

## Binders and hypotheses

| Lean binder or expression | Mathematical meaning and source correspondence |
| --- | --- |
| `{p : ℕ}` and `[Fact p.Prime]` | A prime residue characteristic and its primality witness, needed for the p-adic field model. These specialize the local field in Ze80 §1.1, printed p.170 / PDF p.7. |
| `(F : PadicField.{uF} p)` | An actual finite extension of `ℚ_p`; the group is `GL_k(F.Carrier)`. The field is explicit, rather than an abstract group or an assumed induction datum. |
| `(T : F.TopologicalData)` | A compatible topology and local-field realization of that field, used by the published determinant norm, twists, and normalized induction. It is not a theorem-valued assumption about reducibility. |
| `letI := T.topology` | The topology used for smoothness of the input objects and for all subsequent constructions. |
| `(k : ℕ)` and `(hk : 0 < k)` | A positive common rank. This builds in Ze80's equality of the two ranks, `k = l`, and the positive ranks of the cuspidal classes in §1.10, printed p.174 / PDF p.11. `hk` also supplies the positivity of both blocks. |
| `(ρ ρ' : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := k))` | Actual irreducible smooth complex representations of `GL_k(F)` that are admissible and have vanishing Jacquet quotients for proper parabolics. These are the irreducible cuspidal factors of Ze80 §§1.10–1.11. |
| `ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass` | The first alternative, `ρ' ≅ νρ`. |
| `ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass` | The second alternative, `ρ ≅ νρ'`. |
| The disjunction `∨` followed by `→` | Either adjacent alternative suffices; both refer to the product in the same factor order `ρ × ρ'`. No unitary hypothesis or auxiliary theorem is imposed. |

`SupercuspidalRep` and `SupercuspidalClass` are the published objects in
`Langlands.Representation.Classification.Supercuspidal`. The vanishing
condition in `GeneralLinear.IsSupercuspidal` is imposed on actual
coinvariants for every proper standard block unipotent radical and every
conjugate. Conjugation transports these quotients, so including the conjugates
does not strengthen the usual condition in Ze80 §1.10. Irreducibility is part
of the bundled object's property, separately from admissibility and Jacquet
vanishing. BZ77 §2.4, printed p.446 / PDF p.7, uses the same cuspidality
convention.

The twist in
`Langlands.Representation.Classification.SupercuspidalTwist` is by
`T.determinantPowerCharacter k 1`, namely `g ↦ |det g|` as a complex-valued
character. Its norm is residue normalized, with `|ϖ| = q⁻¹`, as for the
standard norm defining `ν` in Ze80 §1.11 and BZ77 §4.2.
`SupercuspidalRep.isoClass_eq_iff` identifies equality of these quotient
classes with existence of an actual isomorphism. Thus the hypotheses are
isomorphism conditions, not equality of chosen carriers or actions.

## The actual product, its order, and normalization

The only import is the published
`Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement`.
Its helper `twoBlockFactors hk hk ρ.obj ρ'.obj` places `ρ.obj` in block `0`
and `ρ'.obj` in block `1`. The shape `Shahidi.twoBlocks k k hk hk` has ordered
sizes `![k,k]`, total rank `k + k`, and the first block occupies the first
`k` coordinates. Its actual Levi is the product of those two block groups.
These are the ordered partitions and block embeddings of Ze80 §1.1 and
BZ77 §2.2. This helper is internal packaging of the source's ordered pair;
it introduces no mathematical hypothesis.

The product in the conclusion is precisely

```lean
(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
  (twoBlockFactors hk hk ρ.obj ρ'.obj)
```

It is the published external tensor product of the ordered block factors,
followed by induction from the standard upper block parabolic. This is
Ze80 §1.8, printed p.174 / PDF p.11, applied to the normalized functor of
§1.1. `normalizedProductInductionFunctor_obj` identifies its representation
with the actual `T.normalizedProductInduced` in
`Langlands.Representation.Induction.BlockFactors`.

For a parabolic element `q` with Levi part `m = (m₀,m₁)`, the implemented
covariance and action are

```text
f(qg) = δ_P(m)^(1/2) · (ρ(m₀) ⊗ ρ'(m₁)) f(g),
(h · f)(g) = f(gh).
```

The square root is positive. The published normalizing character is
`T.leviHalfCharacter`; `normalizedProductInduced_covariant` records this
formula. For this shape `T.leviModulus_twoBlocks` gives
`δ_P(m) = |det m₀|^k / |det m₁|^k`. BZ77 §1.8(a), printed p.444 / PDF p.5,
uses this positive half-module covariance and right translation; §§2.2–2.3,
printed p.446 / PDF p.7, fix the upper parabolic convention. The Library
construction uses the explicit block determinant formula for the modulus.
Any needed comparison with the Haar module in an analytic proof remains a
proof obligation; it is not assumed as new structure here.

`SmoothRep.IsIrreducible` is the published abbreviation for
`Representation.IsIrreducible`, simplicity of the lattice of actual invariant
subspaces, including nonzeroness. The conclusion is exactly the negation of
this predicate on the induced object. No existential choice of a proper
subspace, composition series, or Jacquet isomorphism is included in this
statement. Its hypotheses and product are exactly those of the published
`TwoSupercuspidalAdjacentProductComposition` and
`TwoSupercuspidalAdjacentProductJacquet`.

## Independent universes

`uF` is the universe of the field carrier and the groups `GL_n(F)`.
`uV` is the independent universe of the complex carriers of `ρ` and `ρ'`,
and of their external tensor product. No equality or inequality between these
universes is imposed. The induced function-space carrier lies in
`Type (max uF uV)`, as in `normalizedProductInductionFunctor`.
The source has no universe parameters; these are the Library's explicit size
parameters. The entry declaration retains both in the order `.{uF,uV}`.

## Boundary for the proof successor

A proof must establish this proposition for the actual Library objects without
additional theorem-valued assumptions. Ze80's sketch uses a common compact
realization of `π_s = ν^(-s)ρ₀ × ν^sρ₀`. Its reduction to unitary `ρ₀`
(reference [9], Proposition 5.1), the invariant Hermitian forms and their
uniqueness and analytic dependence (reference [13], §4), their nondegeneracy
and positivity, unitarity at `s = 0`, and the unbounded matrix coefficient for
large `|s|` all require proofs if this route is used. Replacing `s` by `-s`
gives the equally parametrized family with the two exponents reversed.

The nonadjacent irreducibility used away from `s = ±1/2` and the needed
consequence of Ze80 Theorem 1.9 also require independent accepted proofs.
Statements, pending drafts, and citations cannot supply these inputs.
The proof successor must preserve the full task's independence exclusions:
in particular it cannot use segment or multisegment classification,
exhaustion, segment Jacquet or derivative formulas, segment product
irreducibility criteria, or the downstream analytic or square-integrability
results. Its Markdown must audit both imports and mathematical proof
dependencies. The imported structure module here supplies definitions only;
none of its asserted propositions is being used as a proved premise.

## Exact citations and reading

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  165–210. Literature ID `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Read §1.1, printed p.170 / PDF p.7; §§1.8–1.10, printed p.174 /
  PDF p.11; and Proposition 1.11 and its proof sketch, printed p.175 /
  PDF p.12. The statement and signs of the analytic family on PDF p.12
  were also checked in the rendered original.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Read §1.8, printed p.444 / PDF p.5; §§2.1–2.4, printed p.446 /
  PDF p.7; and §4.2 including Remark 4.2(2), printed p.454 / PDF p.15.
  The positive half-module sign on PDF p.5 was checked in the rendered
  original.

No source-specific errata note for either ID was present in the current
Library or project notes, and no applicable errata entry was found in the
retained literature index when checked on 2026-10-29. This records the bounded
local check, not an assertion that no errata exist elsewhere.
