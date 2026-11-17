# Actual standard specialization of the semistandard source density

Worker 268, Task 7258. This derived comparison specializes the actual
semistandard density to the published standard Levi, without changing its
scalar, character restriction, or inducing representation.

## Source and scope

Waldspurger (2003), registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
V.2 and Lemma V.2.1, printed p.292 (PDF p.58), define the actual density
on the unitary orbit. VI.3, printed p.302 (PDF p.68), uses that density
in source wave packets. The standard-versus-intrinsic adapters here are
internal consequences of those published constructions and the actual
all-test standard-triple comparison; the paper does not name these Lean
adapters.

The field and carrier universes are independent. The field is arbitrary
nonarchimedean local, and the ambient group is affine, locally of finite
type and connected reductive. The maximal split torus, generic
cocharacter, standard simple-root subset and every standard cocharacter
for that subset remain explicit. No splitness or characteristic-zero
assumption on the ambient group is made.

## Constructions and comparisons

All declarations are in
`Langlands.HarishChandraSchwartz.RationalSemistandard.StandardSourceComparison`.

* `presentation` uses
  `SemistandardSpectralIndex.ofStandard_eq_ofCocharacter` to give the exact
  standard triple a genuine `CocharacterPresentation`. No dynamic-coverage
  witness or selected conjugating map is required for this specialization.
* `literalHomeomorph_eq` identifies its dynamic/literal Levi map with
  `standardLeviDynamicHomeomorph`. Both maps fix ambient rational points.
* `characterRestrict_eq` identifies `SourceDensity.characterRestrict` with
  `standardLeviCharacterRestrict`, as continuous monoid homomorphisms.
* `standard_irreducible`, `standardScalar`, `scalar_eq` and
  `standard_inverseRegular` carry the primitive scalar prerequisites to
  the standard spelling. `scalar_eq` is equality of the actual conditional
  canonical rational scalars. The inverse-regularity proof transports the
  original `OrbitPacketData.inverseRegular`; it does not assume an
  additional regularity assertion.
* `standardDensity` is exactly `standardLeviPlancherelWeight` at these
  primitive data. It uses the original central subgroup, central quotient
  measurable space, Haar measure and square-integrability witness. Explicit
  instance arguments retain those same inputs across the definitionally
  equal literal group presentations.
* `density_eq_standard` proves equality with
  `SourceForm.orbitDensity` at `standardLeviModel`. It is equality on the
  actual discrete-series orbit, rather than a free scalar comparison or an
  assertion only at selected representations.

The input `OrbitPacketData` retains the exact existing relative-reflection
and central-split-character statements, common scalar compact and its two
factorizations, forward and reverse continuations, open nonempty domains
and containment in their full domains, generic irreducibility locus, and
full-unitary inverse regularity. These are the same conditional
prerequisites of the published scalar/density package; none is discharged
by this comparison. The subgroup `C` is normal and central and its supplied
quotient measure is Haar. No scalar positivity is needed here.

## Implemented proofs and boundary

The literal homeomorphisms and actual canonical scalars agree by reduction
and proof irrelevance. Character equality is proved by extensionality on
characters and rational points, using the two existing restriction value
formulas. Generic irreducibility is rewritten along literal-homeomorphism
equality, and regularity along scalar equality. Density equality uses
surjectivity of the actual unitary twist orbit map, the two density value
formulas, and character-restriction equality.

This focused unit proves the standard density comparison. Source formal
degree, Haar and packet comparisons, the standard orbit product-core
comparison, general model/representative/compact independence and
invariant-family constructions remain separate units of Task 7258.
