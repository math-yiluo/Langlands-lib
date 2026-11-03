# Actual normalized induction on a product

The main construction is
`Langlands.Plancherel.normalizedProductInductionTensorEquiv`.
For actual semidirect subgroup decompositions
`P = M ⋉ U` in `G` and `Q = N ⋉ V` in `H`, it identifies the external tensor
of the two canonical normalized inductions with canonical normalized induction
from `P.prod Q` of the external tensor on `M.prod N`:

\[
 I_P^G(A)\boxtimes I_Q^H(B)
 \;\simeq\;
 I_{P\times Q}^{G\times H}(A\boxtimes B).
\]

This is an equivalence of the actual representations of `G × H`. Its source and
target are the existing smooth induced function spaces, and the map sends a pure
tensor of functions to their pointwise tensor. The semidirect decomposition,
projection and positive Haar half-character of the product are derived from the
factor data.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, is the motivating source.
I.3, printed p.243 (PDF p.9), defines normalized smooth induction by positive
half-modulus left covariance and uniform open right invariance. V.1, printed
p.288 (PDF p.54), defines `L(ω,P)` by induction from `P × P` and uses its natural
identification with the tensor of the two normalized inductions, with the second
inducing object the smooth contragredient.

This module is a derived adapter for that identification. Waldspurger's stated
setting is reductive groups and complex representations. The generic actual
subgroup scope here follows from the Library's semidirect, Haar-modulus and smooth
induction constructions. In particular, the proof reuses
`Langlands.Induction.BinaryTensor.equiv` and the underlying proved finite-product
bijectivity result. The product Haar argument uses Mathlib's actual Haar measure,
product measure and Haar scaling uniqueness. These internal transport and measure
arguments are not attributed verbatim to Waldspurger.

## Hypotheses and universes

The main equivalence takes groups `G : Type uG`, `H : Type uH`, each equipped with
a topology, `LocallyCompactSpace`, `NonarchimedeanGroup`, and
`SecondCountableTopology`. The two second countability assumptions are used in
the product Haar measure argument. `NonarchimedeanGroup` supplies the topological
group structure. `U` and `V` are closed in their respective ambient groups. The
left quotients `P \ G` and `Q \ H`, represented by
`Induction.LeftQuotient P` and `Induction.LeftQuotient Q`, are compact.

The algebraic hypotheses are the existing propositions
`IsSemidirectDecomposition P M U` and
`IsSemidirectDecomposition Q N V`. Each states the two subgroup containments,
normalization of the radical by the parabolic, and the complement property inside
the parabolic. The inducing objects are canonical smooth objects
`A : SmoothRep ℂ M` and `B : SmoothRep ℂ N`. Their carrier universes `uV` and
`uW` are independent of each other and of `uG` and `uH`. The field is `ℂ`.
Tensor carriers have universe `max uV uW`, with induced carriers saturated by the
corresponding ambient group universes as in `normalizedInductionFunctor`.

The semidirect and projection lemmas need only groups. The continuous product
identifications need only group topologies. The raw Haar scaling lemma explicitly
uses locally compact second countable topological groups with Borel measurable
spaces. The closed-radical specialization installs the subgroup Borel structures
and derives local compactness and second countability on the subgroup carriers.

## Product subgroup and projection

`HaarModulus.prod_normalizes` proves that `P.prod Q` normalizes `U.prod V`
by applying the two given conjugation containment laws to the two coordinates.
`HaarModulus.subgroupProdEquiv U V` is the actual continuous multiplicative
equivalence between the literal product subgroup and `U × V`. Both directions
are given by the coordinate inclusions, with the subspace topologies.

`IsSemidirectDecomposition.prod` proves the semidirect decomposition of the
literal product subgroups. The proof uses the characterization of complements by
unique representatives `m` satisfying `m⁻¹ p ∈ U`. For a product element it
chooses the pair of the factor projections. Membership and uniqueness follow
coordinatewise from `projection_inv_mul_mem` and `projection_eq_iff`.

`IsSemidirectDecomposition.prod_projection` then identifies the existing
quotient-defined projection of the product decomposition with the pair of the
factor projections. It applies the characterization `projection_eq_iff` to that
pair and the two proved radical membership statements. Thus subsequent induction
uses the canonical projection of the actual product semidirect decomposition.

## Product Haar modulus and its half-character

`HaarModulus.productAutomorphism a b` acts coordinatewise on `G × H`.
`HaarModulus.haarChar_productAutomorphism` proves

\[
 \operatorname{haarChar}(a\times b)
 =\operatorname{haarChar}(a)\operatorname{haarChar}(b).
\]

For Haar measures `μ` and `ν`, pushforward of `μ.prod ν` by this automorphism is
the product of the two pushforwards. Scaling each factor by its actual Haar
character recovers the original factor measure, so scaling the product by the
product character recovers `μ.prod ν`. Haar scaling uniqueness identifies this
scalar with the actual character of the product automorphism. The convention is
Mathlib's `haarChar(a) • map(a,μ) = μ`.

`HaarModulus.closedRestrictCharacter_prod` applies this result to the actual
conjugation automorphisms of the two closed radicals. Their coordinatewise product
is conjugate to conjugation on `U.prod V` through `subgroupProdEquiv`; the proof
uses the existing `Geometric.haarChar_eq_of_conjugacy`. It yields the product law
for the canonical positive modulus on `P.prod Q`.

`HaarModulus.closedHalfCharacter_prod` takes the canonical nonnegative square
root of that identity and then embeds it in `ℂˣ`. `NNReal.sqrt_mul` proves
multiplicativity of these positive roots. The result is exactly the product of the
two `closedHalfCharacter` values used in the factor normalized inductions.

## Smooth external tensor and inducing action

`isSmooth_binaryExternal` proves smoothness for the ordinary binary tensor
representation with independent group and carrier universes. A pure tensor has
the product of the two factor open stabilizers; sums are treated by tensor
induction and the proved additive closure of smooth vectors.
`binaryExternalObject` bundles this representation as a canonical `SmoothRep`.

`productLeviObject A B` pulls that smooth external object back through
`subgroupProdEquiv M N`. Its carrier is `A ⊗[ℂ] B`, and its representation is
definitionally `Induction.BinaryTensor.inducing M N A.representation
B.representation`. `productLeviObject_representation` states this identity.

`product_inducingRepresentation` proves equality between the actual normalized
inducing action on the product parabolic and `BinaryTensor.inducing` of the two
factor normalized inducing actions. On pure tensors it rewrites the product
projection and product half-character by their proved formulas. The scalar tensor
identity `(a • v) ⊗ (b • w) = (a*b) • (v ⊗ w)` completes the proof; tensor
extensionality gives equality on the whole carrier.
`productInducingEquiv` is the identity linear equivalence between those proved
equal inducing representations.

## Main equivalence and evaluation

`normalizedProductInductionTensorEquiv` first applies
`Induction.BinaryTensor.equiv` to the two actual factor inducing representations.
It then applies `Induction.smoothInducedEquiv` to `productInducingEquiv`.
The latter postcomposes coefficient values by the identity, preserving every
underlying function. Both components are actual representation equivalences, so
the composite intertwines the full `G × H` action.

`normalizedProductInductionTensorEquiv_tmul_eval` proves, for `x : G × H`,

\[
 E(f\otimes j)(x)=f(x_1)\otimes j(x_2).
\]

It follows directly from `BinaryTensor.equiv_tmul_eval`, since the final
coefficient equivalence is the identity. This fixes the canonical pointwise map
and the order of the two factors.

## Remaining scope

This unit constructs the product comparison for the Library's actual normalized
induction functor. Specialization to reductive rational points retains the
structural, closedness, second countability and quotient compactness obligations
of that framework, and the comparison of full-parabolic Haar normalization with
the source's Levi-inflated normalization where needed. Same-parabolic integral
duality, the coefficient map on `L(ω,P)`, compact models, character families,
stabilizer descent, manuscript-wide measure normalization and the analytic
Plancherel and inversion conclusions are separate constructions. The equivalence
does not assert any of those conclusions.
