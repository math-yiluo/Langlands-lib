# Automorphism covariance of the actual compact quotient integral

Authors: Worker 76 and Worker 787. Worker 76 wrote the Lean proof and the
original Markdown in the shared task draft; Worker 787 checked it against the
published statement and sources and added the explanation of the factor's
direction.

This module proves the unchanged proposition
`Langlands.Induction.CompactAutomorphismIntegralCovariance.{uG,uV}`.
Its unapplied closing theorem is

```text
Langlands.Induction.compactAutomorphismIntegralCovariance :
  CompactAutomorphismIntegralCovariance.{uG,uV}.
```

The group and coefficient universes remain independent. The proof targets the
published statement unchanged and uses its implicit coefficient binders.
It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Hypotheses and direction

The theorem keeps every hypothesis of the statement. It quantifies over
every Hausdorff locally compact Borel topological group, every closed
subgroup with a Borel structure, arbitrary supplied regular two-sided Haar
measures on both groups, and every supplied compatible measure on the
actual quotient of cosets `H * x`. Closedness supplies local compactness
of `H`; compatibility supplies regularity and thus finiteness on compact
sets for the quotient measure. Neither is an extra premise.

For each continuous group automorphism `α` preserving `H` in both
directions, the coefficient module and inducing representation are
arbitrary. There is no coefficient topology, smoothness, dimension,
admissibility or length hypothesis. There is no compact-open basis,
countability, sigma-compactness, normality or desired measure law
hypothesis.

Write `αH` for the published restriction to `H`, `αQ` for the published
homeomorphism `[x] ↦ [α x]` of the actual quotient, and `δG,δH` for
their ambient and subgroup Haar moduli, respectively. The compact
precomposition is forward, `E(f)(x) = f(α x)`, and the proved scalar is
`δH / δG`, coerced from `ℝ≥0` through `ℝ` to `ℂ`.

### Why the forward factor is `δH / δG`

Here `δG = mulEquivHaarChar α` and `δH = mulEquivHaarChar αH`. Mathlib's
`mulEquivHaarChar_smul_map` states `mulEquivHaarChar φ • map φ μ = μ` for a
regular Haar measure `μ`, so `∫ F(φ x) dμ = (mulEquivHaarChar φ)⁻¹ ∫ F dμ` and
`∫ F(φ⁻¹ x) dμ = mulEquivHaarChar φ · ∫ F dμ`. This second form is the
module `mod φ` of Bernstein–Zelevinsky section 1.7, which is defined by
the inverse-integrand formula `∫ f(σ⁻¹u) dμ(u) = mod_U σ · ∫ f dμ(u)`.

The published `QuotientIntegration.IsCompatible.map_quotientAutomorphism`
states `Measure.map αQ ν = ((δH / δG : ℝ≥0) : ℝ≥0∞) • ν`. Hence the
forward integrand `q ↦ F(αQ q)` picks up `δH / δG`, while the
inverse integrand `q ↦ F(αQ⁻¹ q)` picks up the reciprocal `δG / δH`.
The latter is the quotient module of section 1.7, `mod_{U'\U} =
mod_U / mod_{U'}`, with `U = G` and `U' = H`. The statement and this
proof use the forward precomposition `E(f) = f ∘ α`, so the scalar is
`δH / δG`, not the source's quotient module `δG / δH`.

## Identity on the actual inducing coinvariants

`automorphismCoinvariantsEquiv` constructs the elementary full-group
quotient transport for this particular restricting automorphism. The
published `automorphismInducing H α hα σ` is `σ` composed with `αH`.

The forward map is `Representation.Coinvariants.lift` of the actual
quotient map for `σ`. Its invariance at `h : H` is
`Coinvariants.mk_self_apply σ (αH h)`. For the reverse lift, take
`αH.symm h`: invariance for the pulled-back action at that element
reduces to the required original action at `h`, using
`αH (αH.symm h) = h`.

Thus both maps send the class of a vector to the class of the same vector.
The two inverse laws follow from `Coinvariants.mk_surjective` and
definitional equality on representatives. This is a direct elementary
use of Mathlib's full-group quotient universal property, not a second
subgroup-coinvariant transport construction. The existing
`Jacquet.coinvariantsMapEquiv` and
`Jacquet.coinvariantsGroupTransportEquiv` concern subgroup quotients;
using those interfaces here would additionally identify full-group
coinvariants with quotients by the top subgroup. No such extra carrier
identification is needed in the implemented proof.

`automorphismCoinvariantsEquiv_mk` states the representative formula.
`automorphismCoinvariantsEquiv_natural` proves the required compatibility
with every coefficient intertwiner. It allows its two modules to have
independent universes `uV,uW`. Surjectivity of the pulled-back quotient
map reduces the identity to representatives, where both sides are
definitionally the class of `T(v)`. The closing theorem specializes this
result to the full same-universe category required by the statement.

## Finite-fiber integration and measure scaling

`algebraicIntegral_smul_measure` proves, for every measure `ν`, every
`r : ℝ≥0` and every actual `SimpleFunc X V`,

```text
AlgebraicIntegral.integral ((r : ℝ≥0∞) • ν) φ
  = ofReal(r) • AlgebraicIntegral.integral ν φ.
```

The proof expands the published finite-fiber sum. `Measure.smul_apply`
and `ENNReal.toReal_mul` put the scalar outside each fiber measure;
complex coercion respects multiplication, and `mul_smul` and
`Finset.smul_sum` pull it out of the sum. No finite-measure support
premise is needed for this helper. The totalized convention on infinite
fiber measures is respected by `ENNReal.toReal_mul`; the scalar is finite
because it comes from `ℝ≥0`. The coefficient values need no topology.

`quotientCoinvariantSimple_automorphism` is equality of the actual
simple functions

```text
(quotientCoinvariantSimple H (automorphismInducing H α hα σ) (E(f))).map A
  = (quotientCoinvariantSimple H σ f).comp αQ.
```

Here `A` is the preceding coinvariant equivalence's underlying linear map.
Simple-function extensionality and quotient induction reduce the equality
at `[x]` to `A([f(α x)]) = [f(α x)]`. The published compact
precomposition, descended quotient function and quotient homeomorphism
all have these representative values definitionally. The Borel structure
makes the continuous `αQ` measurable, as needed by `SimpleFunc.comp`.
No representatives are chosen.

`compactCoinvariantIntegral_automorphism` then proves the literal
covariance formula in four steps:

1. The published `AlgebraicIntegral.integral_linearMap` moves `A` inside
   the actual finite-fiber integral. The published
   `quotientCoinvariantSimple_finMeasSupp` supplies its finite-support
   premise for the actual compact function `E(f)`.
2. The preceding simple-function equality replaces that integrand by
   the original descended simple function composed with `αQ`.
3. The published `AlgebraicIntegral.integral_comp` replaces this
   composition by integration against `Measure.map αQ ν`.
4. The published
   `QuotientIntegration.IsCompatible.map_quotientAutomorphism`
   from `QuotientAutomorphismProof` identifies that actual measure as
   `((δH / δG : ℝ≥0) : ℝ≥0∞) • ν`. The finite-sum measure-scaling
   helper gives the claimed scalar.

In particular, the proof uses the genuine quotient pushforward theorem;
it adds no covariance or scaling premise. The auxiliary integral theorem
does not require right invariance of the ambient Haar measure, but the
closing theorem retains that hypothesis exactly as the statement does.

## Closing theorem, provenance and limits

The closing theorem introduces the statement's data, derives the two
local instances from closedness and compatibility, and chooses
`automorphismCoinvariantsEquiv` as its single family. The representative,
naturality and integral laws are respectively the formula above, the
independent-universe naturality theorem, and the proved covariance
calculation. All modules and compact functions remain the actual
published carriers throughout.

The proof is an internal derivation from the published constructions and
Mathlib's quotient universal property. It is not a transcription of a
source proof. Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 1.7, printed pp.443–444,
uses the inverse-integrand convention for an automorphism's module and
remarks that Fubini's theorem gives `mod_{U'\U} = mod_U / mod_{U'}`
for unimodular `U' ⊂ U` and an automorphism preserving `U'`. Section
5.17 (Case IV₂ of the proof of Theorem 5.2), printed p.466, integrates
over `V'\V` and uses a conjugation change of variables, by section 1.7,
to show that the map `A` is a morphism of functors. Its continuation on
printed p.467 shows that `A` is an isomorphism: first for the regular
representation, then for free representations, and then for every
representation, using free resolutions and exactness. These passages
were read in the registered source `bernstein-zelevinsky-1977-induced-i`,
SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No applicable project erratum was found. The exact arbitrary-module
automorphism identity and coefficient naturality here are internal
extensions, not verbatim source claims.

This proof supplies the automorphism calculation for arbitrary
coefficient-valued compact quotient integration. It does not establish
the character twist, the coefficient action of a normalizer, the later
full relative normalizer-equivariant orbit comparison, normalization
cancellation or `Langlands.Geometric.PadicParabolicOrbitJacquetComparison`.
