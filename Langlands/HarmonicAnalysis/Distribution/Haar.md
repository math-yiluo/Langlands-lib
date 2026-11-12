# Haar integration as an algebraic distribution

This definition unit provides concrete integration and density maps into the
published `Langlands.HarmonicAnalysis.Distribution` space, and exact modular
convention bridges. Its source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The locators are II.3.6 Proposition and following density embeddings, printed
pp.46–47 / PDF pp.52–53; II.3.7 modular function and automorphism module,
printed pp.47–48 / PDF pp.53–54, including (II.3.7.1).

`Distribution.ofMeasure μ` is the complex linear map on the actual
`SchwartzBruhat X` given by the Bochner integral against `μ`. It requires a
Borel measurable space and finiteness on compact sets, with no countability
assumption. Every test is integrable by continuity and compact support; those
facts justify the linearity fields. In particular a Mathlib Haar measure
supplies a distribution by this formula.

`multiplyTest f` transports the existing
`PointwiseTestAlgebra.multiplier f` through its published scalar equivalence.
Its pointwise formula is `f(x) φ(x)`. The linear map `density μ` sends a
locally constant function `f` to the distribution
`φ ↦ ∫ x, f(x) φ(x) ∂μ`; complex multiplication is commutative, so this is
the source's formula with the factors in reverse order. `density_one`
identifies the constant-one density with `ofMeasure`. `testDensity μ`
is its restriction to the existing test space. Injectivity and the compact
support assertions are separate statement obligations, not properties
assumed in these definitions.

`IsNonnegativeTest` means a test is real valued with nonnegative real part.
`IsPositive` requires evaluation on every nonzero such test to be a positive
real number, explicitly including zero imaginary part. This is the strict
positivity convention specified in II.3.6. `IsLeftInvariant` and
`IsRightInvariant` are fixed-point conditions for the existing distribution
actions. In particular, source right invariance uses the point action
`x ↦ xg⁻¹`, with no convention changed.

`renardModular` is a homomorphism into the nonnegative reals whose value is
exactly Mathlib's `Measure.modularCharacter g⁻¹`. The theorem
`renardModular_eq_inv` identifies it with the reciprocal of
`Measure.modularCharacter g`. The source's values are strictly positive;
positivity is a separate assertion, not lost by use of `ℝ≥0` as the codomain.
The reciprocal arises because Mathlib scales pushforward by `x ↦ xg`, while
Renard's right point action is `x ↦ xg⁻¹`.

`renardAutomorphismModule σ` is the reciprocal of
`MeasureTheory.mulEquivHaarChar σ`. Mathlib's
`mulEquivHaarChar_smul_map` states that its character times `μ.map σ` equals
`μ`, whereas Renard's (II.3.7.1) scales the integral of `f ∘ σ`, equivalently
`μ.map σ`. Thus the reciprocal is required here too. These adapters reuse
Mathlib's actual characters; they do not define alternative Haar measures.
This unit constructs the maps and proves their elementary formulas, but
does not prove Haar existence, uniqueness, invariance, positivity, density
injectivity or Renard's index formula.
