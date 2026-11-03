# Scalar smooth functions on actual discrete-series twist orbits

Author: Worker 200.

This internal construction defines scalar smooth functions on the existing
actual unitary-unramified twist orbit by their real-angle lifts. It builds the
complex subalgebra of these functions, proves that they are continuous and
unchanged in smoothness by a base twist, includes them faithfully into bounded
continuous functions, and proves their integrability for the existing fixed
orbit measure.

The source motivation is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), VI.1, printed pp.295–296
(PDF pp.61–62). There smooth families are tested after pulling back to the
unitary character torus, and the scalar factor is
`C-infinity(Im X(M))`. The present scalar construction is an internal
prerequisite. It does not construct the source's coefficient-valued
`C-infinity(O,P)` or its tensor-product description. VI.1 explicitly gives a
GL(2) example with nontrivial stabilizer action on coefficient tensors.

## Actual objects and hypotheses

The field `F : Type u` is an arbitrary `IsNonarchimedeanLocalField`. The
group scheme `G` is affine and locally of finite type, with a displayed proof
`hG : GroupScheme.IsConnectedReductive G`. Its rational points carry the
existing actual rational-point topology and proved nonarchimedean-group
structure. The representation-carrier universe `uV` is independent of `u`.
There is no restriction on characteristic, splitness or quasisplitness.

Let `T` be a commutative group scheme and `s : T.toGrp ⟶ G` an actual
central morphism, witnessed by `hs`. Put `A = s(T(F))`. Normality of `A` is
derived from centrality before each dependent quotient-Haar and
representation-class binder. The measurable space on `G(F)/A` and its Haar
measure `mu` remain displayed data. Discrete-series classes, their twist
action and their orbit are the existing canonical `SmoothRep` constructions;
no alternative representation category or orbit is introduced.

Write `C` for the actual unitary unramified character group, `O_omega` for
its actual orbit through `omega`, `r = rationalImageRank G`, and

\[
 e:C\simeq (S^1)^r,\qquad
 p_\omega(z)=e^{-1}(z)\mathbin{\cdot}\omega.
\]

Here `e` is exactly
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG`, using the
existing chosen basis of the actual valuation image. The map `p_omega` is
`rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega`, with codomain
restricted to the actual orbit. Its already constructed quotient topology
is used throughout. Its open-quotient property and compactness are imported
proved results, rather than additional hypotheses.

The smoothness, algebra, inclusion and base-change results do not require
actual-image finite index or affineness of `T`. Integrability additionally
requires `IsAffine T.X.left` and the explicit premise
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`. The latter
remains an in-book proof obligation from Renard V.2.6, not a permitted
permanent structural assumption for completion of the full program.

## Exponential lifts and translation

For any index type `J`, `finiteTorusExp` is the map

\[
 q:\mathbb R^J\longrightarrow (S^1)^J,
 \qquad q(x)_i=\exp(i x_i).
\]

The circle exponential is Mathlib's `Circle.exp`.
`isOpenQuotientMap_finiteTorusExp` uses its surjectivity, continuity and
local-homeomorphism open-map property, then the product open-quotient
construction. `finiteTorusExp_add` proves `q(x+y)=q(x)q(y)` pointwise.

For finite `J`, `IsSmoothFiniteTorusFunction f` is the proposition
`ContDiff ℝ ∞ (f ∘ finiteTorusExp)`. Thus smoothness means that the
real-angle lift is infinitely differentiable as a map from the finite real
product to `ℂ`, viewed as a real normed space. Continuity of `f` follows
from continuity of its lift and the quotient-map continuity criterion; it
is not included as an extra conjunct in the definition.

`isSmoothFiniteTorusFunction_mul_const_iff` proves that
`z ↦ f(z*c)` is smooth exactly when `f` is smooth. Choose a real-angle
preimage `a` of `c`. The forward direction composes the lifted function
with `x ↦ x-a`; the reverse direction composes with `x ↦ x+a`. The
exponential addition law identifies the resulting lifts. The required
smoothness of those affine maps follows from addition and subtraction of
the identity and constant maps.

## Smoothness on the actual orbit

`IsSmoothRationalOrbitFunction s hs mu hG omega f` is the proposition

\[
  \operatorname{ContDiff}_{\mathbb R}^{\infty}
       (f\circ p_\omega\circ q).
\]

Its `continuous` theorem first applies the torus continuity theorem to
`f ∘ p_omega`, then applies the continuity criterion for the already proved
open quotient `p_omega`. This is continuity for the actual orbit topology.

`isSmoothRationalOrbitFunction_baseChange_iff` uses the existing
`discreteSeriesOrbitBaseChange`, which sends the orbit based at
`chi • omega` to the orbit based at `omega` and is the identity on
underlying representation classes. Write this homeomorphism as `b`. The
implemented pointwise identity is

\[
 b\bigl(p_{\chi\cdot\omega}(z)\bigr)
       =p_\omega\bigl(z\,e(\chi)\bigr).
\]

The proof uses multiplicativity of `e.symm` and the action law. Translation
invariance on the torus then proves

\[
 f\circ b\text{ is smooth on }O_{\chi\cdot\omega}
 \quad\Longleftrightarrow\quad
 f\text{ is smooth on }O_\omega.
\]

This proves independence of the chosen base class within the actual orbit.
It makes no additional comparison between different valuation-image bases.

## Algebra, bounded inclusion and integration

`rationalSmoothOrbitFunctions s hs mu hG omega` is a `Subalgebra ℂ` of
all functions `O_omega → ℂ`, with membership exactly the stated smoothness
predicate. Constants have constant real-angle lifts; addition and
multiplication have the pointwise sums and products of smooth lifts. The
implementation applies `contDiff_const`, `ContDiff.add` and
`ContDiff.mul` to prove every subalgebra closure field.

`rationalSmoothOrbitToBoundedContinuous` is an actual complex algebra
homomorphism from this subalgebra into `O_omega →ᵇ ℂ`. It takes the same
underlying function, supplies the derived continuity proof and uses the
proved compactness of the actual orbit with
`BoundedContinuousFunction.mkOfCompact`. Its `apply` theorem is
definitional equality at every orbit point. Its `injective` theorem
recovers equality of the original functions by pointwise evaluation. No
topology or completeness theorem is asserted for the smooth subalgebra.

Finally `IsSmoothRationalOrbitFunction.integrable` applies the derived
continuity theorem and the existing continuous-orbit integrability theorem
to obtain genuine complex Bochner integrability against
`rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega`.
The fixed measure is the existing I.1/VI.3 measure, rather than a newly
chosen normalization. The imported source I.1 split-component comparison
retains connected reductivity, an actual split-component inclusion, and
local finite type of `T` where that comparison is used.

This pair defines smoothness through exponential lifts and proves the laws
above. It does not install a manifold structure on the quotient, compare
this predicate with Mathlib's `ContMDiff`, or prove invariance under a
change of the image basis. It also does not construct coefficient tensors,
their stabilizer action, normalized intertwining families, wave packets,
Schwartz membership, spectral finiteness, inversion or Plancherel.
