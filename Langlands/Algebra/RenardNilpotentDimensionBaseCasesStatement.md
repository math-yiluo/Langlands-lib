# Renard C.I: base cases for the actual nilpotent dimension maximum

Worker 1200 reuses Worker 709's statement draft to define the proposition
`Langlands.Renard.NilpotentDimensionBaseCasesStatement.{u}` for the
base cases of David Renard's *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix C.I, printed
pp.275–276 / one-based PDF281–282. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both workers read these pages and visually checked the formulas.

The proof on printed p.275 opens with the one-generator dimension bound,
which Renard attributes to Cayley–Hamilton. On printed p.276 its induction
uses the explicit equality `φ_l(1) = 1` for every `l`. The present proposition
states these base cases using the actual maximum already constructed in
`Langlands.Algebra.RenardNilpotentDimensionMaximum`. It also states the zero
and empty-tuple conventions needed for that construction's full natural-number
domain. Those conventions and the arbitrary-carrier formulation are explicit
derived extensions of the passage, rather than separately numbered source
lemmas. The one-generator claim is an upper bound, as in the source.

## Exact scope

The first conjunct quantifies over every `V : Type u` with `AddCommGroup V`,
`Module ℂ V` and `FiniteDimensional ℂ V`. Its four conclusions, in order, are:

1. For every natural `l`, if `Module.finrank ℂ V = 0`, then
   `nilpotentGeneratedMaxDimension l V = 0`.
2. For every natural `l`, if `Module.finrank ℂ V = 1`, then
   `nilpotentGeneratedMaxDimension l V = 1`.
3. `nilpotentGeneratedMaxDimension 1 V ≤ Module.finrank ℂ V`.
4. `nilpotentGeneratedMaxDimension 0 V` equals zero when the finrank of `V`
   is zero, and equals one otherwise.

The remaining four conjuncts assert the corresponding canonical-carrier
formulas for all natural indices:

```text
nilpotentGeneratedPhi l 0 = 0
nilpotentGeneratedPhi l 1 = 1
nilpotentGeneratedPhi 1 k ≤ k
nilpotentGeneratedPhi 0 k = if k = 0 then 0 else 1.
```

Here `nilpotentGeneratedPhi l k` is exactly the published maximum on
`Fin k → ℂ`. The maxima concern actual endomorphism tuples whose entries
commute and are nilpotent, and the complex finrank of their actual unital
`Algebra.adjoin ℂ (Set.range a)`. Scalar endomorphisms and the identity belong
to this adjoin without using another counted generator. Zero entries,
repetition and redundant entries are allowed. The generator count and carrier
universe are unrestricted. No nontriviality, positive-dimension or positive
count assumption is imposed; the last formula handles the empty tuple on
every carrier, including the zero space, where the identity is zero.

The maximum and its published laws
`nilpotentGeneratedMaxDimension_isGreatest` and
`nilpotentGeneratedMaxDimension_attained` are imported unchanged. No base-case
formula, linear-equivalence transport law, sharp dimension estimate or
numerical recurrence is assumed. The zero-dimensional results are already
proved in the imported construction; they are repeated here to package the
boundary conventions with the source base cases.

The supplementary registered original
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Its C.I corrections concern strict inequalities and
exponents in the older 2010 proof, printed pp.317–318. The present source
comparison uses the governing 2026 edition; the supplementary entries do not
change either of the base assertions above.

This module defines a proposition. A proof of this exact proposition is a
separate obligation after independent statement acceptance and publication.
Carrier transport, monotonicity, the actual ideal-power filtration, complement
generation, restriction injection, the algebra splitting, floor recurrence,
final estimate and completion of C.I remain separate obligations.
