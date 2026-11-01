# Renard C.I: the complement bound for a maximizing tuple

The theorem `Langlands.Renard.nilpotentMaximizingComplement.{u}` proves
exactly the unchanged closed proposition
`Langlands.Renard.NilpotentMaximizingComplementStatement.{u}`.
Worker 846 supplied the proof adapter in the task context. Worker 1200
checked its dependencies and source correspondence, prepared this explanation
and submitted the pair.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Appendix C.I, printed p.275 / one-based
PDF281. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF281–282 were read and PDF281 was visually checked for this contribution.
The relevant step passes from the restriction estimate
`dim R ≤ s k` to `φ_l(k) ≤ s k`. The formal statement makes explicit that
the chosen algebra attains the maximum before its complement is used.
This existential packaging is a derived clarification of the source.

The supplementary 2010-edition corrections, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19. Their C.I entries concern numerical inequalities
and exponents in the older edition. The 2026 original governs the
maximum/complement inference proved here.

## Actual objects and conclusions

For every `V : Type u` with `AddCommGroup V`, `Module ℂ V` and
`FiniteDimensional ℂ V`, and every `l : ℕ`, the theorem supplies one tuple
`a : Fin l → Module.End ℂ V`. Its entries commute pairwise and are
individually nilpotent. Write

```text
R = NilpotentFiltration.generatedAlgebra a,
V₁ = NilpotentFiltration.idealPowerSubspace a 1,
k = Module.finrank ℂ V.
```

The imported definitions make `R` the actual unital algebra
`Algebra.adjoin ℂ (Set.range a)` and `V₁` the subspace `I V` for the
tuple-generated ideal `I` in this algebra acting by the original
endomorphisms. The scalars and identity are already in the unital adjoin;
they do not add a counted nilpotent generator.

The same tuple satisfies `Module.finrank ℂ R = nilpotentGeneratedPhi l k`.
The theorem also supplies a complex complement of its own `V₁`, and for
every complex submodule `W` with `IsCompl V₁ W` it proves

```text
nilpotentGeneratedPhi l k ≤ Module.finrank ℂ W * k.
```

Thus with `s = Module.finrank ℂ W` the conclusion is the source bound
`φ_l(k) ≤ s k`. The complement has no invariance requirement. Its
existence is a conclusion, as are attainment and the dimension estimate.

## Implemented proof and dependencies

`nilpotentGeneratedMaxDimension_attained`, imported through the target
from `Langlands.Algebra.RenardNilpotentDimensionMaximum`, chooses an
actual tuple `a` with commutation, nilpotence and

```text
dim R = nilpotentGeneratedMaxDimension l V.
```

The second conjunct of the published theorem
`nilpotentDimensionTransport.{u, u}` from
`Langlands.Algebra.RenardNilpotentDimensionTransportProof` identifies the
right side with `nilpotentGeneratedPhi l k`. Composing these two
equalities gives `hdim'`, the required maximum equality for this tuple.
The generated algebra in the target is definitionally the adjoin used
by the attainment theorem, so no algebra replacement occurs.

`Submodule.exists_isCompl` supplies a complement of this tuple's `V₁`.
For an arbitrary complement `W`, the proof rewrites the desired bound
using `hdim'` and applies the second conjunct of the independently
published theorem `nilpotentComplementRestriction` from
`Langlands.Algebra.RenardNilpotentComplementRestrictionProof`, with
the same `V`, `l`, `a`, commutation, nilpotence and complement.
That conjunct is exactly `dim R ≤ (dim W)(dim V)`.

The restriction theorem is imported and applied as a proved theorem.
Its statement is not added as a premise. Its proof, by Worker 308,
uses the published complement-generation theorem and the restriction
dimension helpers. The maximum construction is by Worker 1200; the
carrier-transport proof is by Worker 16. This pair reuses their
published results by Lean name.

## Boundaries

The proof keeps the arbitrary carrier universe and every natural tuple
length. It requires no positive dimension, nontrivial carrier, nonempty
tuple, nonzero entries, distinctness or minimality. In particular the
zero space, empty tuples and repeated or redundant generators are covered
by the same imported theorems without a case split. These boundary
extensions and the explicit maximizing choice are derived from the
published actual definitions, as explained by the target's companion.

This pair proves only the maximizing-tuple complement statement.
The per-tuple restriction theorem is reused; head/tail splitting,
monotonicity, the floor recurrence, numerical contradiction and the
other whole-book obligations retain their separate tasks and owners.
