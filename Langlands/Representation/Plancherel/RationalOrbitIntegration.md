# Convergent integration on actual discrete-series twist orbits

Author: Worker 200.

This derived construction gives actual Bochner integration of continuous
complex-valued functions on the existing unitary unramified twist orbit,
with the measure fixed by `rationalNormalizedDiscreteSeriesOrbitMeasure`.
The source measure conventions are Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)* (2003), I.1, printed
p.239 (PDF p.5), and VI.3, printed p.302 (PDF p.68). The finite-measure,
integrability and bounded-linear-functional results here are internal
consequences of the existing constructions and Mathlib integration theory;
they are not assertions that the article explicitly states in this form.

## Actual objects and hypotheses

The field `F : Type u` is an arbitrary `IsNonarchimedeanLocalField`.
The group scheme `G` is affine and locally of finite type; its rational
points carry the actual `rationalPointTopology F G.X` and its proved
nonarchimedean-group structure. The representation-carrier universe `uV`
is independent of `u`. No characteristic, splitness or quasisplitness
restriction is added.

Let `T` be an affine commutative group scheme and `s : T.toGrp ⟶ G`
an actual central morphism, with `hs : GroupScheme.IsCentral s`. Put
`A = s(T(F))`. Each declaration derives normality of `A` from
`hs.range_le_center` before binding the Haar measure on `G(F) / A`
and the canonical discrete-series class `omega`. The quotient's measurable
space and Haar measure `mu` remain displayed data. There is no supplied
measure on the character group or orbit.

The explicit premise
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`
concerns the actual central valuation image. The imported kernel and
stabilizer results derive finiteness of the restriction kernel `K` and
twist stabilizer `S` from this premise. Both groups contain the identity,
so their finite cardinalities are positive. Proving actual-image finite
index remains an in-book deduction from Renard V.2.6, rather than a
permitted permanent external structural assumption for the full program.

Write `C` for the existing compact unitary unramified character group,
`h_G` for `rationalUnitaryUnramifiedProbabilityHaar G`, and
`lambda_s` for `rationalUnitaryUnramifiedCharacterHaar s hs hindex`.
Write `O_omega` for the actual orbit in the canonical discrete-series
classes, `p : C → O_omega` for `discreteSeriesOrbitMap`, and
`eta_omega` for its fixed measure. The existing constructions give

\[
  \lambda_s=|K|h_G,\qquad
  \eta_\omega=|S|^{-1}p_*\lambda_s,\qquad
  \eta_\omega(O_\omega)=|K|/|S|.
\]

The character and orbit measurable spaces are the Borel spaces of the
existing compact-open and stabilizer-quotient topologies. Compactness of
the actual orbit is imported, rather than assumed.

For the source I.1 comparison with restriction to split-component
characters, the imported character Haar module additionally uses
connected reductivity of `G`, an actual `GroupScheme.IsSplitComponent s`,
and local finite type of `T`. This pair does not remove those hypotheses.

## Finite positive measure and convergent integrals

`isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure` is the
finite-measure instance. It rewrites total mass by the existing ratio
formula, derives finiteness of `S`, and applies the extended-nonnegative
real division bound with nonzero denominator.
`rationalNormalizedDiscreteSeriesOrbitMeasure_univ_pos` derives
finiteness of `K` and uses its nonzero cardinality to prove positive total
mass. The denominator, being a natural-number cast, is not infinite.

`rationalNormalizedDiscreteSeriesOrbitMeasure_real_univ` converts the
mass formula to real numbers:

\[
  \eta_\omega.\operatorname{real}(O_\omega)
     =\frac{|K|}{|S|}.
\]

Its proof uses the existing extended-nonnegative mass formula and the
compatibility of `ENNReal.toReal` with division and natural-number casts.

`integrable_rationalNormalizedDiscreteSeriesOrbitMeasure` proves that
every continuous function `f : O_omega → ℂ` is integrable against
`eta_omega`. The proof equips the existing orbit with its proved compact
space instance, converts `f` into a bounded continuous function using
`BoundedContinuousFunction.mkOfCompact`, and applies finite-measure
integrability.

`integrable_rationalDiscreteSeriesOrbit_characterParameters` proves that
the pullback `f ∘ p` of any bounded continuous orbit function is integrable
for both `lambda_s` and `h_G`. It forms the bounded continuous pullback
using continuity of the actual orbit map. Compactness of `C` and its
Haar measure give finite measure for `lambda_s`; `h_G` is a probability
measure. Thus both character-parameter integrals below converge.

## The bounded complex linear integral

`rationalDiscreteSeriesOrbitIntegral s hs mu hindex omega` has type
`(O_omega →ᵇ ℂ) →L[ℂ] ℂ`. Its value is the actual Bochner integral

\[
  I_\omega(f)=\int_{O_\omega}f(\eta)\,d\eta_\omega.
\]

The definition constructs a complex linear map using integrability for
addition and the Bochner scalar-multiplication identity. It then applies
`LinearMap.mkContinuous` with the bound
`eta_omega.real Set.univ`, using
`BoundedContinuousFunction.norm_integral_le_mul_norm`.
`rationalDiscreteSeriesOrbitIntegral_apply` is the defining equality.
Every continuous function on the orbit can be supplied through
`BoundedContinuousFunction.mkOfCompact`.

`norm_rationalDiscreteSeriesOrbitIntegral_le` proves the operator bound

\[
  \|I_\omega\|\leq\frac{|K|}{|S|}.
\]

It applies the operator-norm criterion to the same integral estimate and
rewrites real total mass. No claim of operator-norm equality is made.
`rationalDiscreteSeriesOrbitIntegral_const` uses the Bochner constant
integral and the mass formula to prove

\[
  I_\omega(\operatorname{const}(c))
     =\left(\frac{|K|}{|S|}\right)\mathbin{\bullet}c.
\]

## Character parameters and change of base class

For every bounded continuous `f`,
`rationalDiscreteSeriesOrbitIntegral_eq_characterIntegral` proves

\[
  I_\omega(f)
    = |S|^{-1}\mathbin{\bullet}
       \int_C f(p(\chi))\,d\lambda_s(\chi).
\]

It unfolds the fixed orbit measure as a scaled pushforward, applies
Bochner integration against a scaled measure, and uses continuity of
`p` and `f` for the measurable pushforward integration theorem. Conversion
of the finite stabilizer scalar to real numbers gives the displayed
inverse cardinality.
`rationalDiscreteSeriesOrbitIntegral_eq_probabilityIntegral` substitutes
`lambda_s = |K| h_G` and combines real scalars to give

\[
  I_\omega(f)
    =\left(\frac{|K|}{|S|}\right)\mathbin{\bullet}
       \int_C f(p(\chi))\,dh_G(\chi).
\]

For a unitary unramified character `chi`, the existing
`discreteSeriesOrbitBaseChange` homeomorphism `b` sends the orbit based at
`chi • omega` to the orbit based at `omega` and is the identity on the
represented classes. `rationalDiscreteSeriesOrbitIntegral_baseChange`
proves

\[
  I_{\chi\cdot\omega}(f\circ b)=I_\omega(f).
\]

The function on the left is formed by bounded continuous precomposition.
The proof rewrites the existing base-change pushforward equality and
applies Bochner pushforward integration. This establishes independence
within the actual twist orbit using the same fixed character measure.

## Scope

These results construct convergent integration and its elementary laws
on the actual compact orbit, conditional on the displayed actual-image
finite-index premise. They introduce no representation-theoretic or
analytic conclusion as structural input. They do not establish that the
source wave-packet integrands are continuous, construct their density
or coefficient tensors, prove VI.3.1's Schwartz estimates or continuity,
or prove spectral finiteness, inversion or Plancherel. Those remain
separate obligations.
