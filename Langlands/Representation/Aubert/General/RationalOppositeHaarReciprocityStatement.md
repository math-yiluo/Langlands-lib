# Reciprocal actual Haar characters on opposite rational-point radicals

Author: Worker 127.

`Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`
is a proposition definition awaiting proof. On the literal common standard
Levi, it asserts that the actual positive Haar scaling characters of the
standard radical and the opposite radical multiply to one. It supplies no
proof or additional axiom.

## Scope and actual objects

The quantifiers and premises are the structural part of
`RationalNaturalJacquetDualityStatement`. The field `k : Type u` is every
nonarchimedean local field, including positive characteristic, and `G` is
every connected reductive group scheme over `Spec k`, including nonsplit and
non-quasisplit groups. The map `i` is the actual maximal split torus map,
`ν` is an actual generic cocharacter, and `I` is every finite subset of
`SimpleRoot i ν`. The label type and subset may be empty. There are no
representation carriers or representation-universe restrictions in this
statement.

The ambient rational-point group carries the canonical `pointTopology`.
Local compactness, the nonarchimedean group property and Hausdorffness are
displayed hypotheses for that topology. The two local instance binders
extract affineness of `G` and the monomorphism property of `i` from connected
reductivity and the maximal split torus hypothesis. The displayed
`hStandard : StandardCocharacterStatement` remains a premise. The statement
does not prove this universal standard-cocharacter assertion.

The standard radical is the published subgroup `unipotent i ν I`. Its
closedness is the displayed premise `hU`. For every actual witness `ζ`
satisfying `IsStandardCocharacter i ν (rootSet i ν I) ζ`, the opposite
radical is exactly `oppositeUnipotent i ζ`: the dynamic contraction subgroup
at the inverse of the inducing cocharacter, evaluated on the identity test
scheme. Its closedness is provided by
`isClosed_oppositeUnipotent_localField`.

Both characters have domain the literal subgroup `levi i ν I`.
`isSemidirectDecomposition_of_standardCocharacterStatement` supplies its
normalization of the standard radical, and
`opposite_isSemidirectDecomposition` supplies its normalization of the
opposite radical. Each use is the corresponding `.levi_le_normalizer`.
There is no replacement Levi, conjugation representative or comparison
between different choices of `ζ`.

## Meaning and conventions

For `U = unipotent i ν I`, `O = oppositeUnipotent i ζ` and
`M = levi i ν I`, write `c_U` and `c_O` for the two displayed
`HaarModulus.closedRestrictCharacter` homomorphisms `M →* ℝ≥0ˣ`.
The conclusion is

`∀ m : M, c_U(m) * c_O(m) = 1`.

These are the actual Haar characters of conjugation on the two closed
subgroups. If `μ_U` is a Haar measure on `U`, the Library's
`normalizerCharacter_smul_map` states
`c_U(m) • map (u ↦ m u m⁻¹) μ_U = μ_U`. Thus `c_U(m)` is the forward
volume scaling factor: `μ_U(m S m⁻¹) = c_U(m) μ_U(S)`.
The same convention applies to `O`. Closedness supplies local compactness
inside each character definition; no chosen Haar measure occurs in the
statement.

Renard instead writes `δ_N(m)` for the factor in
`∫ f(m n m⁻¹) dμ_N(n) = δ_N(m) ∫ f(n) dμ_N(n)`.
Consequently `δ_N(m) = c_U(m)⁻¹`, with the same conversion on the
opposite radical. Renard's identity
`δ_N(m) = δ_Nbar(m)⁻¹` therefore gives exactly
`c_U(m) * c_O(m) = 1`. Inverting both source characters preserves
reciprocity. This translation is derived here from the integral convention;
it is not a verbatim statement about the Library's definitions.

## Original sources and provenance

The registered governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Section V.5.4, printed pp. 126–127, PDF pp. 132–133, was read as extracted
text and original page images, including the overbars on the opposite
radical.

The Lemme on printed p. 126 asserts, for every `m ∈ M`,
`δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)⁻¹ = δ_N(m)⁻¹ = δ_Nbar(m)`.
The proof on p. 127 first computes root products for the split component
and explicitly obtains
`δ_P(a) = δ_N(a) = δ_Nbar(a)⁻¹`. It extends these equalities to the
full Levi by its Cartan decomposition. The preceding proof of ambient
unimodularity uses Iwahori index factorizations, root multiplicities and
the ambient Cartan decomposition. None of these structural ingredients is
assumed or proved by this proposition definition.

The supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is the author's errata for the 2010 edition, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
PDF p. 9 was read and visually checked. The correction to the 2010
Lemme V.5.4 specifies that its equalities hold on `M`, except for the final
root-product equality, which requires the split component `A`. The 2026
edition already makes that distinction. This statement asserts reciprocity
on the full Levi and includes no root-product formula.

The source abbreviates the minimal standard parabolic before V.5.4, but the
Lemme and its proof use `Σ(P)` and the split component of its Levi. Here the
same reciprocal identity is required for every standard `I`, as in the
intended general opposite-Jacquet application. Its proof must establish that
scope and identify the standard and inverse-cocharacter dynamic radicals;
the source quotation alone does not discharge those formal obligations.
The rational-point and canonical-topology formulation is internal.

## Consumer boundary

The normalized Jacquet functor uses
`HaarModulus.closedInverseHalfCharacter` of its own radical. Applying the
canonical positive-half and complex character maps to the asserted product
identity gives the reciprocal normalization scalars needed for an
equivariant opposite-Jacquet pairing. This implication still needs its Lean
proof; it is not a conclusion declared by this statement.

This unit isolates that structural normalization obligation. It does not
construct a stable pairing or contraction basis, prove naturality or
Jacquet duality, identify a parabolic modular character, or prove ambient
or Levi unimodularity. No classification, character-independence, geometric
lemma, adjointness or cuspidal-support theorem is invoked by this proposition
definition. Any such use in a future proof must be identified by its actual
declarations.
