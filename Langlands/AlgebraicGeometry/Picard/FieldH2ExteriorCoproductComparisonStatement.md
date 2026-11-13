# Degree-two exterior and Künneth comparison

`Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonStatement.{u}`
is a `Prop`-valued target. For every field `K : Type u` and abelian scheme `A`
over `Spec K`, it asks for linear equivalences

```text
e : H²(A, O_A) ≃ ∧² H¹(A, O_A)
κ : H²(A ×_K A, O_(A ×_K A))
      ≃ H²(A, O_A) × (H¹(A, O_A) ⊗ H¹(A, O_A)) × H²(A, O_A).
```

The middle factor in Lean is the twofold indexed tensor power
`⨂[K]^2 H1`, with indices `Fin 2`. Its role is the usual tensor square.
For every `x : H²(A, O_A)`, the requested formulas are

```text
κ(p₁* x) = (x, 0, 0)
κ(p₂* x) = (0, 0, x)
κ(μ*  x) = (x, antisym(e x), x).
```

Here `antisym` is Mathlib's `exteriorPower.toTensorPower K H1 2`.
On an exterior monomial with ordered entries `v,w`, its tensor terms are
`v ⊗ w − w ⊗ v`. The statement has no characteristic, algebraic closure,
dimension, finiteness, chosen basis or polarization hypothesis. It includes
zero-dimensional abelian varieties.

## Exact cohomology and maps

`H1`, `H2` and `HP2` are the objects obtained by applying the Library's actual
`relativeCohomology` functor to the corresponding structure module. The product
is `A.X ⨯ A.X` in schemes over `Spec K`. Its projections are `Limits.prod.fst`
and `Limits.prod.snd`; `m := p1 * p2` is the group multiplication.
For each of these three morphisms `f`, the pullback is exactly
`relativeCohomologyPullback f O 2` followed by the degree-two cohomology map
of `Langlands.Scheme.Modules.pullbackUnitIso f.left`. These are the maps in
`FieldH2PrimitiveInjectivityStatement`.

The equivalences `e` and `κ` are existential witnesses satisfying all three
formulas simultaneously. This interface does not construct a cup product,
specify a unique comparison, or assert naturality beyond these formulas.
It is a degree-two consequence to be proved from the exterior cohomology
and Künneth descriptions, with all transport to the actual Library functors
still required. An abstract Künneth isomorphism without the displayed
compatibilities does not supply this statement.

## Provenance and independence

This is a derived interface isolating the geometric input in the proof of
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd edition (1994),
Proposition 6.7, printed pp.117–118 (PDF pp.130–131). The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
The source invokes the cohomology exterior-algebra description of abelian
varieties and Künneth for precisely the reduced degree-two pullback.
The three formulas are the degree-two expression of that description;
the exact Lean functors and existential interface are internal choices.

For the algebra dictionary, Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, (6.14)–(6.17), printed pp.94–95 (PDF pp.98–99), describes
multiplication pullback as the bialgebra coproduct under Künneth and gives
the mixed exterior coproduct formula. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These passages provide the dictionary and algebra calculation, not a Lean
proof of this geometric comparison. In particular, the draft's later use of
dual Picard geometry to identify the full exterior algebra does not waive
the independent proof obligation here. No source-specific errata note was
found for either registered source.

A proof for the intended primitive-class application must avoid the
Artinian primitive lifting, Picard-zero lifting, finite-type or relative
dual geometry, and finite-type or unrestricted smooth-family abelian
representability results excluded by Task 5774, including results proved
through them. This statement assumes none of those results.

## Implemented conditional reduction

`fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison` proves that the
comparison target implies `FieldH2PrimitiveInjectivityStatement` exactly.
Applying `κ` to the difference of the three pullbacks and projecting to its
middle component gives `antisym ∘ e`. The accompanying algebra lemma
`Langlands.LinearAlgebra.exteriorPowerToTensorPower_injective` proves
injectivity of antisymmetrization over any commutative ring on a free
module, using exterior-basis coordinate pairings. Every vector space is
free, so it applies here without an extra geometric finiteness hypothesis.
The injectivity of `e` then proves the desired injectivity.

The module proves this conditional reduction and the supporting algebra
lemma, but leaves the geometric comparison target unproved. It does not
complete Task 5774 or establish the unconditional field result.

## Authorship

Worker 223 designed the comparison interface and implemented the algebra
lemma and conditional reduction.
