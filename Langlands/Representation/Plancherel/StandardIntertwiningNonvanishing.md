# Nonvanishing of the actual standard intertwining integral

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1(10), printed p.283 / PDF p.49, states `J_{P'|P}(π) ≠ 0`. The argument
given there uses functions `f ∈ F₁` from the proof of Theorem IV.1.1: their
standard integral at `1` is the integral of `f` over `(U ∩ U') \ U'`, and it is
"easy to construct" such an `f` for which this integral is nonzero. The source
then extends the identity algebraically to all parameters.

This module carries out the construction for the actual standard integral at
one fixed inducing representation, in the general semidirect setting of
`StandardIntertwiningIntegral`. The test function is the published compact
double-coset section of `Induction.CompactLocalSection`. Its integral is
computed exactly. The algebraic extension to other parameters is not treated.
The provenance is internal, and no new translation of a numbered literature
result is claimed.

## Weak integral of an indicator

`hasIntegral_indicator_const` is a general lemma. For a representation `ρ`, a
measure `μ`, a measurable set `S` with `μ S ≠ ⊤` and a vector `w`, the function
equal to `w` on `S` and to `0` elsewhere has weak integral `(μ S).toReal • w`
in the sense of the published `SmoothWeakIntegral.HasIntegral`. Every smooth
functional is integrated by Mathlib's `integral_indicator_const`.

## Local product and the test vector

`G` is a locally compact nonarchimedean group. Let `P = M U` be a semidirect
decomposition with `U` closed, `U'` the radical of the target, and `Q` a
compact open subgroup of `G`.

* `HasSourceLocalProduct P U U' Q` states: every `x ∈ U'` of the form `p k`
  with `p ∈ P` and `k ∈ Q` can be written `x = a q` with `a ∈ U`, `q ∈ Q` and
  `q ∈ U'`.
* `targetCompactOpen U' Q` is the open subgroup `Q ∩ U'` of `U'`.
  `targetCompactOpen_isCompact` proves it compact when `U'` is closed.
* `sourceTestOrbit U U' Q` is the image of `Q ∩ U'` in the quotient
  `(U ∩ U') \ U'` (published `compactOpenQuotientOrbit`).

Let `A` be a canonical `SmoothRep.{0,uG,uV} ℂ M` and `σ` the published
`leviInflatedInducingRepresentation h hU A`: the action of `P` on `A` through
the Levi projection and the half modulus of `U`. Let `v ∈ A` be fixed by
`σ(p)` for every `p ∈ P ∩ Q`.

`sourceTestVector h hU A Q hQ v hv` is the published
`compactDoubleCosetSection P σ Q hQ 1 v hv`, viewed in the Levi-normalized
induced representation that is the source of the standard integral. By the
published lemmas on that section:

* `sourceTestVector_eval_mul`: its value at `p k` is `σ(p) v` for `p ∈ P`,
  `k ∈ Q`;
* `sourceTestVector_eval_eq_zero`: it vanishes off `P Q`.

`integrand_sourceTestVector` assumes `HasSourceLocalProduct P U U' Q`. It
proves that the integrand of the standard integral at `1`, the function
`x ↦ f(x)` on `(U ∩ U') \ U'`, is `v` on `sourceTestOrbit U U' Q` and `0`
elsewhere. On the orbit, `x = a k` with `a ∈ U ∩ U'` and `k ∈ Q ∩ U'`, so
`f(x) = σ(a) v = v`, because the Levi projection is trivial on `U`
(published `projection_unipotent`). Off the orbit, `x ∉ P Q`: otherwise the
local product writes `x = a q` with `q ∈ Q ∩ U'`, and then `x` lies in the
orbit. So `f(x) = 0` there.

## The value at `1`

Let `ν` be a measure on the Borel quotient `(U ∩ U') \ U'`.

* `hasIntegral_sourceTestVector_one`: if `ν S ≠ ⊤` for
  `S = sourceTestOrbit U U' Q`, the integrand at `1` has weak integral
  `(ν S).toReal • v`. This is the previous two results, since `S` is open.
* `HasIntegral.eval_one_sourceTestVector`: if `M` is closed, any representing
  function `Jf` of the standard integral of the test vector (published
  `StandardIntertwining.HasIntegral`) satisfies `Jf 1 = (ν S).toReal • v`. The
  proof is uniqueness of representing vectors, `SmoothWeakIntegral.HasIntegral.unique`
  with the published `compactCofinal`.
* `HasIntegral.eval_one_sourceTestVector_ne_zero`: assume also that `U'` is
  closed, that `ν` is compatible with Haar measures `μU'` on `U'` and `μI` on
  `U ∩ U'` (published `QuotientIntegration.IsCompatible`), and that `v ≠ 0`.
  Then `Jf 1 ≠ 0`. The published `IsCompatible.compactOpenQuotientOrbit_mass`
  gives `0 < ν S < ⊤` for the image of the compact open subgroup `Q ∩ U'`.

## Nonvanishing of the intertwiners

`fullSourceIntertwiner_ne_zero` takes in addition a semidirect decomposition
`P' = M U'`, a Hausdorff `G`, regular right-invariant Haar measures on `U'` and
`U ∩ U'`, the compatibility of `ν`, closedness of `M` and `U'`,
`SquaredModulusCompatibility h hU h' hU'`, and full convergence
`domain h hU U' A ν = ⊤`. Under `HasSourceLocalProduct P U U' Q` and `v ≠ 0`,
the published `fullSourceIntertwiner` is not the zero intertwining map. Its
value on the test vector has, by the published `fullSourceIntertwiner_spec`,
a representing function whose value at `1` is nonzero.

`standardInductionIntertwinerFamily_ne_zero` specializes this to the published
`standardInductionIntertwinerFamily`, in the setting of
`StandardInductionSelfComparison` (a chart `e : H ≃ₜ* M` and positive
characters `ν` of `H`). At a parameter `χ` of its full-domain region, the
family is nonzero, given `Q` with the local product property and a nonzero
vector `v` of the twisted inducing representation fixed by `P ∩ Q` under the
corresponding `leviInflatedInducingRepresentation`.

## Scope

* The subgroup `Q`, the local product property and the fixed vector are
  explicit inputs. They are not constructed here for parabolic subgroups of a
  reductive group, and no relation of `Q` to the source's compact subgroup is
  claimed.
* Full convergence at the given parameter is an input. The source's algebraic
  extension of the nonvanishing to all parameters, through rational
  continuation, is not proved.
* No statement is made about the scalar `j`, its nonvanishing, `μ` or the
  Plancherel formula.
