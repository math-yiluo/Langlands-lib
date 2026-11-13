# Nonvanishing, regularity and nonnegativity of `μ` on the unitary orbit (target)

Worker 5. `Langlands.Plancherel.RationalPlancherelDensity.ConditionalPlancherelDensityUnitaryStatement`
is a Prop-valued target for the first two claims of Waldspurger's Lemma
V.2.1 about the Plancherel density `μ`. It also asks that `μ` be a nonzero
rational function when the product of the `γ(M_α|M)` is finite. The module
does not prove the target. It proves that the target follows from the
target `ConditionalDynamicOppositeUnitaryScalarStatement` about `j_P`
(IV.3(6) with positivity), which is not proved either. It also proves one
elementary fact about the Library predicate `RationalFunctionNonnegAt`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- V.2, printed p.292 / PDF p.58: for `ω` in the unitary orbit `O`,
  `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`, where `α` runs over the reduced roots of
  `A_M` up to sign.
- Lemma V.2.1, printed p.292 / PDF p.58: "La fonction `µ` est une fonction
  rationnelle régulière sur `O`. Pour tout `ω ∈ O`, on a `µ(ω) ⩾ 0`; …"
  The lemma continues with three more claims: the product formula
  `µ^G(ω) = ∏_α µ_α(ω)`, invariance under `W^G`, and invariance under
  `ω ↦ ω̌`.
- Proof, printed p.293 / PDF p.59: "Cela résulte des propriétés (2), (3),
  (5) et (6) de IV.3."
- IV.3(6), printed p.287 / PDF p.53: if `π` is square-integrable, then
  `j(π) ≠ 0`.

## Provenance of the target

The target is derived from V.2 and Lemma V.2.1. It is not a verbatim
statement. It states, for the Library density `plancherelDensity`:

1. if `rankOneGammaProduct i ζ K hK ≠ ⊤`, then `μ ≠ 0` in the field of
   rational functions;
2. for every unitary unramified character `z`, `μ` is regular at `z` with
   a nonnegative real value (`RationalFunctionNonnegAt`).

Item 2 is the first two claims of Lemma V.2.1. Item 1 is not a separate
claim in the source. Waldspurger's definition of `μ` as `j⁻¹` times a
product of positive real numbers presupposes `j ≠ 0` (IV.3(6)) and the
finiteness of each `γ(M_α|M)`, so his `μ` is a nonzero rational function.
In Lean, `0⁻¹ = 0` and `ENNReal.toReal ⊤ = 0`. If `j_P = 0` or the
product is `⊤`, the Library density `μ` is `0`, and item 2 holds trivially.
Item 1 rules out the first case whenever the product is finite. The
finiteness of the product is a separate matter: the module
`RationalPlancherelConstantFinite` proves it for a split torus `T` and a
smooth connected `G`. Item 1 keeps it as a hypothesis, so the target does
not depend on that module.

Item 2 at `z` does not say that `μ` has no zero at `z`. At a pole of `j_P`
on `O`, the value of `μ` is `0`; this is consistent with V.2.1.

The target omits the last three claims of Lemma V.2.1 and all of
IV.3(1)–(6).

## The Library objects

- `plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
  hDForwardΩ hneReverse hDReverseΩ hne hi` (module
  `RationalPlancherelDensity`) is
  `fieldConstant (plancherelDensityConstant i ζ K hK) * j_P⁻¹`. Here
  `plancherelDensityConstant i ζ K hK = (rankOneGammaProduct i ζ K hK).toReal ^ 2`
  is `∏_α γ(M_α|M)²`, and `j_P` is the Library's
  `conditionalCanonicalRationalScalar` with the same arguments. The
  Haar measures on the radicals are normalized by the same compact open
  subgroup `K` as the `γ` factors.
- `RationalFunctionNonnegAt G hp hG f z` (module
  `DynamicOppositeUnitaryScalarStatement`): there are regular functions
  `m n` with `n(z) ≠ 0`, `f = m / n`, and a real number `r ≥ 0` with
  `m(z) / n(z) = r`. The value does not depend on the presentation
  (`rationalFunction_value_eq` in that module).
- `unitaryUnramifiedCharacters` is the Library's `Im X(M)`: unramified
  characters of absolute value one.

## The target

`ConditionalPlancherelDensityUnitaryStatement` has the inputs of the
target `ConditionalDynamicOppositeUnitaryScalarStatement`, in the same
order, except that the cocharacter `χ` there is replaced by `T`, `i` and
`ζ` with `χ = ζ ≫ i`. `F : Type u` is a nonarchimedean local field, `G` is a group scheme
over `Spec F` with `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`,
`T` is a commutative group scheme with `i : T → G`, `ζ` is a cocharacter
of `T`, and `χ = ζ ≫ i` (local notation). `P = parabolic χ`,
`P̄ = oppositeParabolic χ` and `M = levi χ`. The other inputs are:

- `hRefl : RelativeRootReflectionExistenceStatement`,
  `hCST : CentralSplitTorusCharacterStatement` and
  `hG : IsConnectedReductive G`;
- a compact open subgroup `K` (`hK`) with `G(F) = P K` (`hPK`) and
  `G(F) = P̄ K` (`hOppK`);
- `A : SmoothRep ℂ (levi χ)`, continuations `p : ForwardContinuation …`
  and `q : ReverseContinuation …`;
- open nonempty sets `DForward`, `DReverse` in the two full convergence
  domains, and an open nonempty set `D` of unramified characters at which
  the normalized induction of the twist of `A` is irreducible (`hi`);
- a normal central subgroup `C` of `M(F)` (`hC`), a Borel structure and a
  Haar measure `μM` on `M(F)/C`, the finiteness
  `[Finite (levi χ ⧸ (commonNormKernel (leviNormCharacters χ) ⊔ C))]`, and
  `hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM`.

The data `T`, `i` and `ζ` are needed because `plancherelDensity` forms
the `γ(M_α|M)` from the submodules of the cocharacter lattice of `T`. The
module re-enables, with `attribute [local instance]`,
the local instances of `DynamicOppositeCanonicalScalar` (point topologies
and their Hausdorff, locally compact, topological-group, nonarchimedean
and second-countable structures, and the closed-immersion, affine and
finite-type instances of the centralizer scheme), as in the modules
`RationalPlancherelDensity` and `DynamicOppositeUnitaryScalarStatement`.
Underscored binder names (`_hDForward`, `_hDReverse`, `_hD`, `_hsq`) are
premises that the conclusion does not mention. The conclusion is

```
(rankOneGammaProduct i ζ K hK ≠ ⊤ → μ ≠ 0) ∧
  ∀ z : unramifiedCharacters (normCharacters χ),
    z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
    RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG) μ z
```

with `μ = plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
hDForwardΩ hneReverse hDReverseΩ hne hi`.

## Proved results

- `RationalFunctionNonnegAt.const_mul` (section `Regular`, a general group
  scheme `G` with the inputs of `rationalUnramifiedFunctionField`): if `f`
  is regular at `z` with a nonnegative real value and `c ≥ 0` is real, then
  the constant `c` times `f` is regular at `z` with a nonnegative real
  value. Proof: from `f = m / n` with `n(z) ≠ 0` and `m(z)/n(z) = r ≥ 0`,
  take the presentation `(c m) / n`; its value at `z` is `c r ≥ 0`.
- `plancherelDensity_nonnegAt_of_unitaryScalar`: under
  `ConditionalDynamicOppositeUnitaryScalarStatement`, `μ` is regular with a
  nonnegative real value at every unitary `z`. Proof: the hypothesis gives
  this for `j_P⁻¹`. Then `μ` is the constant `plancherelDensityConstant`
  times `j_P⁻¹`, and the constant is `≥ 0`
  (`plancherelDensityConstant_nonneg`); apply `const_mul`.
- `plancherelDensity_ne_zero_of_unitaryScalar`: under the same hypothesis,
  if `rankOneGammaProduct i ζ K hK ≠ ⊤`, then `μ ≠ 0`. Proof: by
  `plancherelDensity_eq_zero_iff`, `μ = 0` would give `j_P = 0`,
  contradicting the first item of the hypothesis.
- `conditionalPlancherelDensityUnitaryStatement_of_unitaryScalar`:
  `ConditionalDynamicOppositeUnitaryScalarStatement` implies
  `ConditionalPlancherelDensityUnitaryStatement`. The proof introduces all
  binders and combines the two previous theorems.

The last three results follow Waldspurger's proof of the first two claims
of V.2.1, which reduces them to IV.3. Here the content of IV.3 is
packaged in the hypothesis.

## Not proved here

Neither target is proved. This module proves none of IV.3(1)–(6), Lemma
V.2.1, or the finiteness of the `γ(M_α|M)`.

## Axioms

The four proved results use only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).
