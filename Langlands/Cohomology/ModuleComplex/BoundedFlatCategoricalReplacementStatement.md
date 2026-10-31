# One categorical perfect replacement for a bounded flat complex

`Langlands.Cohomology.ModuleComplex.BoundedFlatCategoricalReplacementStatement.{u}`
is an internal algebraic assembly statement over an arbitrary commutative
noetherian ring `R` in universe `u`. Its input is an actual
natural-number-indexed cochain complex `C` of flat modules whose terms
vanish above some natural number `n`. It assumes finite generation of the
kernel of the degree-zero differential and of each positive cycle module
modulo the image of the preceding differential. The latter image is
written as the comap to the cycle submodule, so that the quotient uses the
actual bundled differentials of `C`.

The conclusion chooses one integer-indexed complex `K` satisfying the
existing `IsStrictlyPerfect` predicate: it is bounded in both directions
and has finite projective terms. It asserts an isomorphism, by `Nonempty`,
from `DerivedCategory.Q.obj K` to the image of `C` extended by zero to
integer degrees. After **every** ring homomorphism `f : R →+* A`, that same
`K` gives an isomorphism from its ordinary degreewise scalar extension to
the extension by zero of the ordinary scalar extension of `C`. The scalar
ring `A` is arbitrary and need not be flat or noetherian. All module
carriers stay in universe `u`; the derived categories use Mathlib's
standard localization, with morphisms in universe `u + 1`.

Worker 137 designed this interface by combining the existing
`BoundedFlatComplexProjectiveStatement` and
`BoundedFlatQuasiIsoBaseChangeStatement` with the internal
`NatModuleQuasiIsoCriterionStatement`,
`BoundedNatComplexExtensionStatement`, extension of quasi-isomorphisms,
and the Library's `DerivedPlus.mapExtendIso`. It repackages their raw
cycle and boundary tests as actual derived-category comparisons. It
introduces no new notion of perfection or scalar extension and contains
no scheme-theoretic input or comparison with derived sections. This file
defines the proposition; its proof is separate.
