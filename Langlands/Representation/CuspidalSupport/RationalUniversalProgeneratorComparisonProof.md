# Renard VI.4.1: the actual compact-induction tensor comparison

Worker 1595.

## Source and exact result

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VI.4.1, alternative-progenerator Remark, printed pp.149–150 /
PDF pp.155–156. Registered original:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both source pages were read. The remark uses compact induction of the entire
restriction of π to the common norm kernel, applies Mackey's second isomorphism,
and identifies the compact induction of the trivial representation with the
unramified group algebra and its regular-function interpretation.

`Langlands.CuspidalSupport.rationalUniversalProgeneratorComparison` proves the
unchanged Library proposition
`RationalUniversalProgeneratorComparisonStatement.{uF, uV}`. Its conclusion is
`HasRationalUniversalProgeneratorComparison G π`, witnessed by an isomorphism
from `rationalNormKernelCompactInduction G π` to
`rationalUniversalTensorSmoothRep G π` in the actual category of smooth complex
representations. It therefore supplies an invertible complex-linear map
intertwining every group element.

The exact theorem retains all the published binders: the nonarchimedean local
field F, connected reductive G, maximal split torus inclusion, generic
cocharacter, standard-cocharacter statement, relative root system, closed
standard unipotent subgroups, the stated topological properties of G(F), and
irreducibility and cuspidality of π for the actual standard parabolic family.
The universes `uF` and `uV` are independent. Both compared carriers have universe
`max uF uV`; there is no added premise on π's dimension or admissibility.

## Explicit comparison through finite coefficients

The internal namespace `UniversalComparison` implements the tensor identity
directly rather than invoking a general Mackey theorem. These helper definitions
and proofs are derived constructions for this argument. Let R be a commutative
ring, H a topological group, L a discrete commutative group, and p : H →* L a
continuous surjection with open kernel N. Let ρ be a smooth R-linear
representation on V. The abbreviation `C p ρ` is literally
`Induction.CompactFunctions p.ker (ρ.comp p.ker.subtype)`, with covariance
f(kx) = ρ(k)f(x), compact nonzero support modulo N, and right-translation action.

For a ∈ L and v ∈ V, `sectionValue` is

    s(a,v)(x) = ρ(x)v if p(x) = a⁻¹, and 0 otherwise.

`sectionValue_covariant` proves the required covariance. Its quotient support
lies in the single left coset of any preimage of a⁻¹, so
`sectionValue_compactSupport` proves compactness. To obtain `compactSection`,
choose an open subgroup fixing v using smoothness of ρ and intersect it with
N. This open subgroup fixes s(a,v) under right translation, which supplies the
smooth-function condition in the actual induction definition.

The sections are R-linear in v (`sectionLinear`). Their finite sums define
`fromFinsupp : (L →₀ V) →ₗ[R] C p ρ`. The lemma `fromFinsupp_apply` proves

    fromFinsupp(c)(x) = ρ(x)(c(p(x)⁻¹)).

For the inverse, `representative p hp a` chooses a preimage x of a⁻¹, and
`coefficient` assigns ρ(x⁻¹)f(x). Covariance proves that this normalized value
is independent of the representative (`normalizedEval_eq`). The inverse-index
map N\H → L, [x] ↦ p(x)⁻¹, is well defined and continuous
(`quotientIndex`, `continuous_quotientIndex`). A nonzero coefficient lies in the
image of f's actual compact quotient support under this map. That image is
compact in the discrete space L and hence finite
(`coefficient_support_finite`), giving `toFinsupp`.

Evaluation at representatives, followed by the inverse action, proves
`fromFinsupp_injective`. The normalized-evaluation identity proves
`fromFinsupp_toFinsupp`. Thus `finsuppEquiv` is an R-linear equivalence between
finitely supported coefficient functions and the actual compact induction.
`groupAlgebraEquiv` composes it with Mathlib's coefficient, tensor, and
finite-support reindexing equivalences to obtain

    (AddMonoidAlgebra R (Additive L) ⊗[R] V) ≃ₗ[R] C p ρ.

`groupAlgebraEquiv_single` sends the unit monomial at a tensored with v to
s(a,v). The action identity `compactSection_action` is

    g · s(a,v) = s(p(g)a, ρ(g)v).

The inverse in the support condition p(x) = a⁻¹ is what gives this positive
p(g) factor under right translation.

## Actual rational specialization and equivariance

Take H = G(F) with its canonical rational-point topology, and
p = `Plancherel.rationalValuationImageProjection G` with target the actual
discrete valuation image of the complete rational-character norm family. The
published projection is surjective and continuous; its kernel is exactly
`rationalCommonNormKernel G`. The helper
`isOpen_rationalImageProjectionKernel` transports the published openness of
that full common kernel.

The published `rationalCanonicalUnramifiedCoordinateAlgebraEquiv G` identifies
the actual evaluation-generated algebra B = `rationalUnramifiedRegularAlgebra G`
with this valuation-image group algebra. Composing its inverse on the tensor's
first factor with `groupAlgebraEquiv` gives
`rationalUniversalTensorToImageCompactLinearEquiv`. The generator formula is
`rationalUniversalTensorToImageCompactLinearEquiv_single`.

`rationalCoordinateAlgebraEquiv_projection` identifies the unit monomial at
p(g) with the actual regular function b_g(χ) = χ(g), and
`rationalCoordinateAlgebraEquiv_mul_single` computes its product with any unit
monomial. On those generators the action identity above agrees with the
published universal tensor action

    g · (b ⊗ v) = (b_g b) ⊗ π(g)v.

`rationalUniversalTensorToImageCompactLinearEquiv_intertwines` extends this
calculation by tensor induction and additive-monoid-algebra induction. The
latter induction generalizes v, so its scalar case moves the scalar across the
tensor and applies the induction hypothesis. Additive cases use linearity.

`rationalUniversalTensorImageCompactEquiv` packages the resulting linear
equivalence and equivariance as a `Representation.Equiv`. Transport along the
published kernel equality and inversion give
`rationalUniversalProgeneratorComparisonIso` in the direction from compact
induction to the universal tensor, using `SmoothRep.mkIso`.
`hasRationalUniversalProgeneratorComparison` supplies the resulting nonempty
isomorphism type for every smooth π under the affine, locally finite type
hypotheses used by these actual constructions. The final exact theorem derives
those instances from its original structural inputs and applies this stronger
comparison. Irreducibility and cuspidality are retained in the exact target but
are unnecessary for the comparison itself.

This proof establishes the stated comparison. Inertia-block membership and the
small-progenerator property are separate assertions and are not claimed here.

The local canonical topology instances have explicit module-specific names so this module can be imported with the actual small-progenerator statement and its consumers. This naming choice changes no topology, representation, predicate or proof.
