# Local hypotheses for actual fixed-model adelic openness

Author: Worker 208.

`AdelicModelOpenReductionStatement` is the conjunction of the actual
function-field and full number-field local-to-adelic openness reductions.
It records the topological passage in Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Theorem 4.5, printed p.12,
first two proof paragraphs. This formulation is derived: the geometric
inputs that Conrad proves later are retained as explicit hypotheses here.

For the function-field branch, k and F are fields in an arbitrary common
universe, with the compatible scalar tower from k through RatFunc k to the
function field F. The initial finite set S of actual curve places may be
empty. For the number-field branch, K is a number field in that same
arbitrary universe and S is a finite set of its finite places. The actual
full number-field adele construction retains every infinite factor.

In either branch, X and Y are actual schemes over the original ring of
S-integers, locally of finite type, quasi-compact and separated over that
base. The morphism f is an arbitrary morphism over that same base.
Nonaffine models are allowed. The point sets are the existing relative
scheme morphisms `RingPoint`; no auxiliary presentation replaces them.

At every finite superlevel T containing S, the hypotheses require that
postcomposition by f is open on points over each actual arithmetic factor,
using the existing `schemePointTopology`. They further require that these
factor maps are surjective for cofinitely many indices at that level.
The finite exceptional set may depend on T. Function-field factors are
the original completed local fields and integral valuation rings;
number-field factors additionally contain all original infinite places.
There is no requirement that the finitely many exceptional factor maps
be surjective.

The conclusion is openness of the original postcomposition map on actual
full fixed-model adelic points, with the independently defined final
topologies `curvePlaceFixedModelAdelePointTopology` and
`numberFieldFixedModelAdelePointTopology`. The proposition does not assume
the desired openness in an interface or define the topology by that
property.

Conrad proves this passage using the product-space description of each
arithmetic stage and the open stage maps. The anticipated proof uses the
published actual stage homeomorphisms, the product theorem for open maps
with cofinitely many potentially nonsurjective factors, finite-type
point covering and open target stage inclusions. This file only states
the reduction. Smooth local openness, compatible spreading, Lang-Weil
and eventual integral surjectivity remain separate parent obligations;
this statement is not the full Theorem 4.5.
