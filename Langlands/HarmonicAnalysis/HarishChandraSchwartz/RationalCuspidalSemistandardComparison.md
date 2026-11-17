# Actual semistandard constant terms and the cuspidal kernel

Worker 279, Task 7252. Source: Waldspurger (2003), I.1, printed p.238,
III.6, printed p.272, and VIII.2.1, printed pp.321–322, registered source
`waldspurger-2003-plancherel`, DOI 10.1017/S1474748003000082.
The normalization and source condition below follow those passages.
The comparison with the convergence-strengthened standard kernel is a
derived formulation. Its analytic proof remains open.

## Actual normalization

This module imports the published `SemistandardSpectralIndex i` from the
group-scheme construction. It creates no index. Each index supplies the
actual parabolic, Levi and geometric radical subgroup functors, with an
all-test Levi decomposition and containment of the fixed torus in the
Levi. Their literal rational-point subgroups carry the canonical
rational-point topology and its Borel measurable space.

`isClosed_semistandardRadicalPoints` proves that the indexed radical
points form a closed subgroup: its represented radical immersion
composed with its represented parabolic immersion is closed, and the
published rational-point closedness theorem applies. This helper requires
affineness of G but no finite-type assumption. The algebraic helper
`semistandardLeviPoints_le_normalizer_radicalPoints` evaluates the
all-test Levi decomposition at `Spec F`. Its normality assertion and
Levi inclusion show that the actual Levi points normalize the actual
radical points; topology and affineness are unnecessary for this helper.

For `F : Type u` a nonarchimedean local field and G affine and locally
finite type, `semistandardUnipotentModulus p` is
`HaarModulus.closedRestrictCharacter` of that radical and Levi. It is the
actual Haar modulus of conjugation, not a supplied character.
`semistandardUnipotentModulus_ofStandard` is a definitional equality
with `standardUnipotentModulus` for the imported `ofStandard` triple.
Thus the standard specialization uses the existing actual normalization.

`RationalSemistandardConstantTermsVanish f` quantifies every p with
`p.parabolic ≠ ⊤`, every Haar measure on its radical points, and every
pair of group arguments. It requires
`constantTermInd muU (semistandardUnipotentModulus p) f g = 0`.
This is equality of functions on the actual Levi, so it also quantifies
every Levi argument m. Unfolding gives the source formula
`δ_P(m)^(1/2) ∫ f(g₂⁻¹ m u g₁) du = 0`.
This predicate asserts vanishing alone; it does not assert convergence.

The proved helper
`isIntegrableUnipotentCuspidal_iff_semistandardConstantTermInd`
specializes the published generic integral equivalence to each indexed
triple and its actual modulus. It equates the integrable unipotent
cuspidality condition with two-sided translated integrability together
with the normalized vanishing condition. It requires no Schwartz
estimate and makes no source-coverage assertion.

## Closed targets and scope

Both targets are Prop-valued definitions, not proved theorems. They
quantify every nonarchimedean local field F, affine locally finite type
connected reductive G, maximal split torus `i : S → G`, generic
cocharacter ν, compact open subgroup K with the displayed minimal
Iwasawa factorization, and a closed matrix representation ρ on a
nonempty finite matrix index defining the height. Functions belong to
the existing `RationalSchwartzSpace hKc hPK ρ`, with its actual Xi and
height. There is no characteristic-zero, split, quasi-split or
positive-rank restriction, nor a representation-carrier universe in
these statements.

`RationalSchwartzSemistandardConstantTermConvergenceStatement` asserts
Bochner integrability of `u ↦ f(x u y)` for every such Schwartz
function, every proper indexed parabolic, every Haar measure on its
actual radical, and all x,y. It is the full-index counterpart of the
published standard convergence target.

`RationalCuspidalSemistandardComparisonStatement` asserts, for every
such Schwartz function, equivalence between membership in
`rationalCuspidalSubmodule hKc hPK ρ` and
`RationalSemistandardConstantTermsVanish f`. The constructed submodule
requires integrability and vanishing for all proper standard root
subsets and all translates. This target compares it with normalized
vanishing alone on the full intrinsic index. Convergence, estimates,
conjugacy, coverage, finiteness and Plancherel are not premises.
When there are no proper index members the vanishing predicate is
vacuous; the standard kernel's empty-root specialization is already
proved in its construction. No geometric rank-zero comparison is
claimed as proved here.

In I.1 the source indexes semistandard parabolics by actual parabolics
containing the fixed maximal split torus. The imported
`SemistandardSpectralCoverageStatement` and
`SemistandardSpectralUniquenessStatement` separately assert that
forgetting the Levi and radical identifies the intrinsic triple carrier
with that source carrier. Their proofs belong to the group-scheme
index work. The present closed comparison contains neither as a
premise and does not prove them. A literal identification with the
source's parabolic indexing still uses those geometric comparisons.

## Recursive source projection

On printed p.321 the source defines `°f = f - κ(ψ)`, with ψ the Fourier
family of f on proper parabolics and zero on G. The construction uses
induction on strictly smaller semisimple rank and the preceding Fourier
and isometry results. VIII.2.1 identifies its image with the
semistandard vanishing condition: vanishing implies `°f = f` by VII.1.2;
the converse uses VII.2.5, constant-term transitivity and lower-rank
inversion, as detailed on pp.321–322.

Neither direction comparing that recursive projection with the
constructed kernel is proved here. The new comparison target concerns
the intrinsic integral conditions only. It neither supplies a projector
nor assumes finite support of the proper Fourier family in the same
rank. The recursive projection, its comparison, VIII.2.2 symmetries,
VIII.2.3 convolution identities, VIII.3 bounds, positive translation
representation and analytic VIII.4 proofs remain separate obligations.
