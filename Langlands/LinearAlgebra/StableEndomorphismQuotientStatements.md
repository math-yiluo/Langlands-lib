# Exactness assertions for successive kernel and range quotients

Worker 709 prepared these statements for the Renard whole-book program.
Worker 969 independently rechecked them against the source and submitted
them unchanged. This module defines four propositions. It proves none of them.
It imports the public construction
`Langlands.LinearAlgebra.StableEndomorphismQuotients`, without changing
its objects or laws. All four declarations belong to
`Langlands.LinearAlgebra.StableEndomorphism`.

## Sources and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix C.II,
proof of Lemma (iv), printed page 278 / PDF page 284. The notation and
surrounding lemma are on printed page 277 / PDF page 283. Registered
source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The readable original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 read PDF pages 283–284 and inspected a rendered image of
PDF page 284 when auditing the formulas, then reread those pages while
preparing this pair. Worker 969 confirmed the SHA256 of that file,
reread the text of PDF pages 283–284 and checked every formula
below against a rendered image of PDF page 284.

The supplementary author errata for the older edition are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Workers 709 and 969 each read PDF page 19. Its correction to old printed
page 321, line 4, replaces `k + 1` by `k + 2` in `t(N_(k+2))`. The
governing 2026 PDF page 284 already has this corrected index; clause 5
below retains it. The errata supplement the 2026 text and do not replace it.
When this pair was checked, the workspace, the project notes and the
Library had no errata note for either source.

The source states these identities inside the proof of an eventual
stabilization result for complex vector spaces. The identities themselves
use only powers, kernels, images and quotient-module operations.
Stating them for arbitrary rings, with no eventual stability premise,
is an internal strengthening and has derived provenance. The explicit
complex specialization preserves the source setting. This statement
module supplies no proof of that strengthening.

## Objects and hypotheses

`PowerQuotientExactnessAt` takes

```lean
{R : Type uR} [Ring R] {V : Type uV} [AddCommGroup V] [Module R V]
(t : Module.End R V) (k : ℕ)
```

The coefficient and carrier universes are independent. The ring may be
noncommutative. There are no dimension, finite generation, stabilization,
Noetherianity, Artinianity, nontriviality or positivity premises.
In particular `k = 0`, zero modules and zero rings are allowed. The
public construction proves `kerPow t 0 = ⊥` and `rangePow t 0 = ⊤`.

Use the following notation only in this Markdown:

- `N_j = kerPow t j = LinearMap.ker (t ^ j)`.
- `I_j = rangePow t j = LinearMap.range (t ^ j)`.
- `E_j = KerQuotient t j = N_(j+1) / N_j`.
- `F_j = RangeQuotient t j = I_j / I_(j+1)`.
- `alpha = kerQuotientShift t k : E_(k+1) →ₗ[R] E_k`,
  induced by `t`.
- `beta = kerToRangeQuotient t k : E_k →ₗ[R] F_k`,
  induced by `t ^ k`.
- `gamma = rangeQuotientShift t k : F_k →ₗ[R] F_(k+1)`,
  induced by `t`.

The quotient denominators are pulled back along the actual numerator
subtype inclusions. Thus `E_k` is the quotient of the submodule
`N_(k+1)`, and `F_k` is the quotient of the submodule `I_k`.
For an ambient submodule `S : Submodule R V`, write

```lean
Q_E(S) =
  (S.comap (kerPow t (k + 1)).subtype).map (kerQuotientMk t k)
Q_F(S) =
  (S.comap (rangePow t k).subtype).map (rangeQuotientMk t k)
```

These are prose abbreviations for the full expressions written in Lean;
the module introduces no auxiliary construction. The `comap` takes the
vectors of `S` that lie in the numerator, and the `map` takes their
classes under the public canonical projection. So `Q_E(S)` is the image
of `S ⊓ N_(k+1)` in `E_k`, and `Q_F(S)` is the image of `S ⊓ I_k` in
`F_k`. In each formula below, the displayed `S` contains the quotient
denominator and lies inside the numerator. These are elementary
inclusions that this module neither states nor proves. Hence `Q_E(S)`
and `Q_F(S)` are exactly the source's `S/N_k` and `S/I_(k+1)`. Supremum
`⊔` is submodule sum and infimum `⊓` is intersection. In Lean, `⊓`
binds more tightly than `⊔`, so `N_k ⊔ LinearMap.range t ⊓ N_(k+1)`
means `N_k ⊔ (LinearMap.range t ⊓ N_(k+1))`.

## The ten clauses

`PowerQuotientExactnessAt t k` is a conjunction, in this order:

| Clause | Lean assertion, in the prose notation above | Source correspondence |
| --- | --- | --- |
| 1 | `LinearMap.ker (kerShiftMk t k) = kerPowInSucc t (k + 1)` | The composite `N_(k+2) → N_(k+1) → E_k` has kernel exactly `N_(k+1)`, viewed inside `N_(k+2)` |
| 2 | `LinearMap.ker beta = Q_E(N_k ⊔ (LinearMap.range t ⊓ N_(k+1)))` | Kernel of the middle arrow |
| 3 | `LinearMap.range beta = Q_F(I_(k+1) ⊔ (N_(k+1)).map (t ^ k))` | Image of the middle arrow |
| 4 | `Function.Injective alpha` | The first induced quotient arrow is injective |
| 5 | `LinearMap.range alpha = Q_E(N_k ⊔ (N_(k+2)).map t)` | First image formula, retaining the corrected `k + 2` |
| 6 | `LinearMap.range alpha = Q_E(N_k ⊔ (LinearMap.range t ⊓ N_(k+1)))` | Second image formula for the first arrow |
| 7 | `Function.Surjective gamma` | The last induced arrow is surjective |
| 8 | `LinearMap.ker gamma = Q_F(I_(k+1) ⊔ (N_(k+1)).map (t ^ k))` | Kernel of the last arrow |
| 9 | `LinearMap.range alpha = LinearMap.ker beta` | Exactness at `E_k` |
| 10 | `LinearMap.range beta = LinearMap.ker gamma` | Exactness at `F_k` |

Clauses 4, 7, 9 and 10 express the full five-term sequence
`0 → E_(k+1) → E_k → F_k → F_(k+1) → 0` as endpoint
injectivity/surjectivity and equalities of actual range and kernel
submodules. All arrows are the public constructed linear maps. No
chosen image or kernel and no exactness hypothesis is an input.

Clause 1 concerns the composite before passing to the quotient in its
domain. Its kernel can be nonzero. Clause 4 concerns the distinct
induced map on `E_(k+1)`; these assertions are compatible and use
different domains.

The source's other construction remarks on PDF page 284 are not repeated
here, because the public construction module already proves them:

- `t ^ k` sends `N_(k+1)` into `I_k`: `kerToRange`.
- That map vanishes on `N_k`: `kerPowInSucc_le_ker_kerToRange`.
- The composite `I_k → I_(k+1) → F_(k+1)` vanishes on `I_(k+1)`:
  `rangePowSuccIn_le_ker_rangeShiftMk`.

The conclusion of Lemma (iv), stabilization from the first common index,
belongs to the separate existing statement module
`Langlands/LinearAlgebra/StableEndomorphismStatements.lean`.

## Closed targets

| Declaration | Content |
| --- | --- |
| `PowerQuotientExactnessAt.{uR, uV}` | All ten assertions for fixed ring/module/operator/index data |
| `PowerQuotientExactSequenceStatement.{uR, uV}` | Universally quantifies every ring in `Type uR`, every module carrier in `Type uV`, every endomorphism and every natural index, then requires `PowerQuotientExactnessAt` |
| `ComplexPowerQuotientExactSequenceStatement.{uV}` | Explicitly quantifies every complex vector space with carrier in `Type uV`, every complex-linear endomorphism and every natural index, then requires the same predicate |
| `PowerQuotientExactSequenceStatements.{uR, uV}` | Conjunction of the ring-general and explicit complex targets |

The complex target uses `R := ℂ` in `PowerQuotientExactnessAt` and
retains arbitrary carrier universe and dimension. The aggregate is the
intended exact target for a later proof unit.

## Verification and remaining obligations

The paired Lean file is a statement unit, with no theorem proving these
four propositions. Development checks in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` completed with no errors or
warnings:

- Aggregate inspection `b3fc41c5-4255-48c6-85f1-2f2edf568622`:
  `PowerQuotientExactSequenceStatements` returns `Prop`, with level
  parameters `uR`, `uV`.
- Ring-target inspection `6a053a76-bd5b-4da8-833a-d869d3648f4c`:
  `PowerQuotientExactSequenceStatement` returns `Prop`, with level
  parameters `uR`, `uV`.
- Complex-target inspection `82b13171-c876-4232-a3ca-875d04be2f28`:
  `ComplexPowerQuotientExactSequenceStatement` returns `Prop`, with
  level parameter `uV`.

These three inspections report only `propext`, `Classical.choice` and
`Quot.sound` in their axiom closures. The private complete-body diagnostic
`09798f6c-43cc-41c3-8ce0-d5ebcea6f916` also completed cleanly. Worker
709 read all four complete printed bodies and all eight check outputs.
The predicate body contains exactly the ten clauses above, including
`N_(k+2)` in clause 5 and the two final range/kernel equalities. Its
printed type has independent coefficient/carrier universes and exactly
the stated ring/module parameters. The closed bodies quantify all
operators and natural indices without further premises; the complex
body explicitly instantiates the coefficient universe to zero and the
ring to `ℂ`. The checks include independent and swapped universe
parameters, and the parameterized predicate for arbitrary rings and
complex spaces at general and zero indices. These checks inspect the
statements and do not prove them.

Worker 969 then checked the unchanged Lean file independently in the
same environment:

- Aggregate inspection `f2c4b5d4-76c9-4b2e-a964-a33c3ad178ca`: no
  errors or warnings, `statement_returns_prop: true`, level parameters
  `uR`, `uV`, axioms `propext`, `Classical.choice`, `Quot.sound`.
- Complete-body diagnostic `2aad8f04-ac3c-4bca-b22d-1096c9e9989e`:
  printed all four bodies with explicit universes, confirming the ten
  clauses above in order. It also elaborated the aggregate at
  independent, swapped and concrete universe levels, and the
  specialization of the ring statement at `R := ℂ` to the complex
  statement. Finally it extracted the endpoint, clause-1, clause-5 and
  exactness conjuncts by position, including at index `0` over an
  arbitrary ring.

The diagnostic modules are private and excluded from the shared pair and
any submission. Development evidence supplies neither independent
semantic acceptance nor publication. Both are required before a proof
successor targets the aggregate.

The existing common-first-stabilization theorem remains separate.
These statements do not close general categorical exactness,
power-kernel-union localization, the general algebra-action extension
or the final C.II finite-localization proposition. Those remain
independent obligations of the whole-book program.
