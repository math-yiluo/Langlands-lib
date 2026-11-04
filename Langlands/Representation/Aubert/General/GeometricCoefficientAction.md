# The target section and actual source coefficient action

This internal adapter compares the original inducing projection
on the target Levi section with the supplied target intersection
projection followed by inverse conjugation. It makes the
existing coefficient quotient comparison equivariant for the actual
unnormalized source Jacquet action, inflated through the target projection.

Write the original ambient decompositions as `P_I = M_I U_I` and
`P_J = M_J U_J`. Let
`H = (P_I ∩ n P_J n⁻¹).subgroupOf P_I`,
`K = (M_I ∩ n P_J n⁻¹).subgroupOf M_I`,
`L_t = (M_I ∩ n M_J n⁻¹).subgroupOf M_I`,
`U_t = (M_I ∩ n U_J n⁻¹).subgroupOf M_I`, and
`L_s = (M_J ∩ n⁻¹ M_I n).subgroupOf M_J`.
The given target decomposition is `K = L_t U_t`, with actual projection
`r_t : K → L_t`.

`geometricIntersectionSubgroupEquiv` is the actual equivalence
`e : L_t → L_s`, with `e(t) = n⁻¹ t n` and
`e.symm(a) = n a n⁻¹`. It composes the published
`Geometric.General.intersectionEquiv` with the two proved subgroup
equalities; it chooses no replacement subgroup or abstract isomorphism.
Both ambient value formulas are explicit theorems.

`geometricCoefficientSection` maps `l ∈ K` into `H` by the original
inclusion of `M_I` in `P_I`, retaining the same ambient point.
`geometricCoefficientLeviMap` is `p = e.comp r_t`.
The actual orbit coefficient map from the imported quotient module is
`f(h) = dJ.projection(n⁻¹ h n)`.
`geometricCoefficientProjection_section` proves precisely
`f(section(l)) = p(l)` as equality in the original `M_J`.

The implemented proof uses
`hTarget.projection_inv_mul_mem l`: `r_t(l)⁻¹ l` belongs to `U_t`.
Thus its inverse conjugate belongs to `U_J`. After rewriting the ambient
formula for `e(r_t(l))`, the defining membership condition becomes
`e(r_t(l))⁻¹ (n⁻¹ l n) ∈ U_J`.
`dJ.projection_eq_iff` identifies this with the desired equality of
original Levi components. No additional preservation of a conjugated Levi
or projection-comparison premise is needed.

For any ambient topological group, the equivalence is bundled as
`geometricIntersectionSubgroupContinuousEquiv`. Both maps are continuous
by inner multiplication and subtype inclusions.
The original section is continuous for any topology, with no continuity
premise on the ambient Levi projection. The coefficient map is continuous
whenever the original inducing projection `dJ.projection` is continuous.
`continuous_geometricTargetProjection` derives continuity of `r_t` from
that same premise and the target decomposition: the displayed projection
identity gives continuity of `p` first into `M_J`, then into `L_s` with its
induced topology, and finally continuity of `r_t = e.symm.comp p`.
There is no new independent continuity hypothesis on the intersection
projection.

The representation equivalence uses the original coefficient
quotient comparison as its linear equivalence. Quotient representatives
reduce its intertwining equation to the proved projection comparison.
More precisely, set
`N = ker(dI.projection).comap H.subtype` and
`S = (M_J ∩ n⁻¹ U_I n).subgroupOf M_J`.
The subgroup `N` is normal in `H`, as the inverse image of a kernel.
The source representation is
`((sigma.comp f).toCoinvariants N).comp section`.
The supplied source decomposition gives
`L_s ≤ normalizer S`, so the target is exactly
`(Jacquet.action sigma S L_s hSource.levi_le_normalizer).comp p`.
Its carrier is the actual source-radical quotient, and its action on a
class is `[v] ↦ [sigma(p(l))v]`.
`geometricCoefficientActionEquiv` intertwines these two representations;
its representative formula sends the class of each vector to the class of
that same vector. The linear map is the existing
`geometricCoefficientQuotientEquiv`, not a newly chosen equivalence.

The algebraic constructions hold for arbitrary groups, subgroups and
the displayed decompositions. The topological results require only the
topological group hypotheses just specified. The representation comparison
specializes to the actual rational standard families at the
standard-cocharacter, connected reductive, maximal split torus, generic
cocharacter and point-normalizer scope of the imported quotient comparison.
It retains the two actual source and target intersection decompositions
and arbitrary ambient decompositions, for every normalizer point over an
arbitrary field with an affine structural morphism on `G`. It does not
require minimality, root or Coxeter comparisons, finite length, or topology.
The commutative coefficient ring and representation carrier have
independent universes.

These are internal derived constructions. The direct mathematical inputs
are the intersection subgroup equalities and
`Geometric.General.intersectionEquiv`, the two original semidirect
projection criteria just named, original Levi inclusion, the actual
coefficient projection and quotient comparison, Mathlib normal
coinvariant action, `Jacquet.action_mk`, quotient-map extensionality, and
continuity of multiplication and subgroup inclusions.
The rational quotient comparison transitively uses the original
source-radical image, proved through closed stable dynamic limits and
common-torus conjugation, and elementary pullback coinvariant transport,
as documented in `RationalGeometricCoefficientQuotient.md`.
This proof chain uses no geometric expansion, adjointness, cuspidal
support, character independence or Langlands classification, including
Aubert Proposition 3.2 or its defective original application to Theorem 3.6.
The broader imported representation definitions are separate from these
proof-body dependencies and do not discharge their target statements.

The comparison concerns ordinary algebraic quotient actions. Passing to
the actual trivial-character localization and smooth source functor,
composing the nested split-stage coefficient quotient, both Haar
corrections and distinct-radical normalization, the integral application,
compact/full induction, actual orbit comparison and the ordered filtration
remain separate obligations. The full rational geometric K0 expansion is
open.
