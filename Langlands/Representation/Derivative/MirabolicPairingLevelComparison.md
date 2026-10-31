# Derivative levels under a nondegenerate mirabolic pairing

Author: Worker 357.

This internal derived module packages a chosen pairing and two corollaries of the published theorem
`Langlands.Derivative.mirabolicHighestDerivativePairing`, imported from
`Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`.
It uses the actual derivative order wrapper and finite-maximum level from
`Langlands.Representation.Derivative.Homogeneity`. These corollaries are derived
from those Lean declarations; no additional assertion from the literature is
assumed.

All declarations are in `Langlands.Derivative.Mirabolic`. Their parameters are
arbitrary `{p : ℕ} [Fact p.Prime]`, `{F : PadicField.{uF} p}`, the supplied
`T : F.TopologicalData`, and
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The field universe `uF` and the two carrier universes `uV`, `uW` are independent.
The supplied topology is installed throughout.

## Bundled derivative pairing

`chooseHighestDerivativePairing T ψ N k hk A B hA hhigh β hβ`
returns an actual invariant form on the order-`k` derivatives of `A` and `B`,
bundled in a subtype with its left nondegeneracy proof. Its hypotheses are
exactly those listed in the next section. The construction applies
`Classical.choose` and `Classical.choose_spec` to
`mirabolicHighestDerivativePairing`. This is a noncomputable choice from the
proved existence statement, with no claim of canonicity, naturality or a
formula relating the chosen form to `β`. It gives consumers one object
containing both the form and the property needed for the level argument.

## Nonzero derivative on the second side

`nontrivial_derivative_of_highestPairing T ψ N k hk A B hA hhigh β hβ`
has the same hypotheses as the published pairing theorem:

- `A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)` and
  `B : SmoothRep.{0,uF,uW} ℂ (GeneralLinear.mirabolic N F.Carrier)`;
- `hk : 0 < k ∧ k ≤ N+1`;
- the actual order-`k` derivative of `A` has a nontrivial carrier, and every
  valid higher-order derivative of `A` has a subsingleton carrier;
- an actual bilinear form `β` with simultaneous covariance
  `β (A g v) (B g w) = |det g| * β v w`, where the character is exactly the
  coercion of `T.determinantNorm (N+1)` used by the imported theorem;
- left nondegeneracy, namely
  `∀ v : A, (∀ w : B, β.val v w = 0) → v = 0`.

It concludes
`Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj B)`.
The proof unpacks the invariant form `γ` and its left nondegeneracy from
`chooseHighestDerivativePairing`. If the second derivative were
subsingleton, every vector in it would equal zero. Linearity would make
`γ v w` zero for every pair of vectors. Left nondegeneracy would then make
every vector of the first derivative zero, contradicting its nontriviality.

## Level comparison

`level_le_of_nondegeneratePairing T ψ A B β hβ` assumes only the
representations, determinant-covariant form and its left nondegeneracy above.
For every `N : ℕ` it proves

```lean
Langlands.Derivative.level T ψ A ≤ Langlands.Derivative.level T ψ B
```

Here `mirabolic N` is `P_(N+1)`, and `level` is the maximum of the actual
nonzero derivative orders in `1,…,N+1`, with default zero. If `level A = 0`,
the inequality is `Nat.zero_le`. Otherwise `level_eq_iff` identifies
`k = level A` as a valid nonzero derivative order for `A`, with all higher
valid derivatives zero. `hasNonzeroDerivative_iff` and
`not_nontrivial_iff_subsingleton` translate this characterization into the
hypotheses of the first lemma. That lemma gives a nontrivial order-`k`
derivative of `B`. Finally `le_level_of_hasNonzeroDerivative` bounds `k` by
`level B`.

The zero case requires no detection theorem. No nontriviality of `A`,
finite length, admissibility, irreducibility or finite dimensionality is
assumed. The two carrier universes need not agree. The comparison is one-sided:
it gives no equality of levels and no highestness assertion for the second
derivative. It covers `N=0` and the top derivative landing in `GL₀` through
the existing order wrapper.

## Normalization and independence

The derivatives and pairing character are exactly the published
determinant-normalized ones. This module introduces no normalization change
and requires no additional Haar-modulus comparison.

The only direct import is `MirabolicHighestDerivativePairingProof`.
The module uses its proved pairing theorem, the finite-maximum laws of
`Homogeneity`, elementary facts about bilinear maps and subsingletons, and
natural-number inequalities. No classification, segment-product,
exhaustion, ordered-head, quotient-coverage or tempered-uniqueness conclusion
is assumed. This helper does not prove the special-head product irreducibility
criterion.

The audited project import closure contains 111 modules including this module:
110 unchanged published dependencies and this new pair. Every imported
Lean/Markdown pair is byte-identical to the workspace Library base
`2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`. No classification module occurs
in this closure. A scan of its Lean code found none of the excluded
classification or exhaustion declaration names. The inherited lower proof
infrastructure includes harmonic analysis, character localization, compact
averaging and the pairing transfer used by the published theorem; no pending
statement is treated as a proved premise. Declaration inspection reports only
`propext`, `Classical.choice` and `Quot.sound` for the construction and the two
corollaries.
