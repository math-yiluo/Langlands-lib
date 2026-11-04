# Full-parabolic and Levi-inflated normalization

This derived adapter compares the full-parabolic Haar normalization with the
positive Levi normalization in Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, I.3, printed p.243 (PDF p.9),
DOI 10.1017/S1474748003000082. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The passage defines induced functions by
`f(m*u*x) = δ_P(m)^(1/2) π(m) f(x)`, with one open right stabilizer for each
function, and gives the ambient action by right translation.

The generic functor and natural comparison are reused from
`Langlands.Representation.Aubert.General.DynamicInductionNormalization`:
`DynamicNormalization.leviTwistedInductionFunctor` and
`DynamicNormalization.normalizedInductionLeviTwistIso`. This file adds the
literal Waldspurger covariance characterization, a function constructor, and
an evaluation API for that published comparison. The inducing-action equality
also reuses `Langlands.Aubert.General.closedHalfCharacter_eq_comp_projection`.
These adapters are internal consequences of the published constructions,
rather than additional theorems quoted from the source.

## Scope and inputs

The ambient `G` is an arbitrary locally compact nonarchimedean topological
group. The actual subgroups `P`, `M`, `U` have a displayed
`IsSemidirectDecomposition P M U`, and `U` is closed. The group and
representation-carrier universes are independent. All bundled objects are the
canonical complex `SmoothRep` objects.

The Levi-normalized functor and its covariance characterization do not require
unimodularity. Comparing it with the full-parabolic functor requires
`IsUnimodularModulus U hU`, which says that conjugation by each element of `U`
has Haar modulus one on `U`. The comparison retains that explicit input.
For standard rational unipotent radicals it can be supplied by the existing
`RationalPointFamily.standardUnipotent_isUnimodular_of_standardCocharacterStatement`
with its displayed structural and topological premises. This file does not
construct the rational-point structural data.

The source restricts its discussion to admissible Levi representations of
reductive groups. The algebraic covariance comparison applies to every smooth
Levi representation with the displayed actual subgroup data. This broader
construction does not assert preservation of admissibility, a rational
reductive realization, a compact-picture theorem, a Hermitian pairing, or a
Plancherel identity.

## Levi action and source functions

`leviInflatedInducingRepresentation` twists the actual Levi action by
`HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer` and then
precomposes it with `h.projection : P →* M`. Thus its value at `p` is the
positive Levi half-character at `h.projection p`, multiplied by the original
Levi action there.

The published `DynamicNormalization.leviTwistedInductionFunctor`
first performs this smooth Levi twist, then inflates and takes smooth induction
from `P`. Openness of the half-character kernel is the existing Haar-modulus
result. Its object representation is literally smooth induction of the
displayed inducing action, as recorded by
`leviInflatedInductionFunctor_obj_representation`.

`LeviNormalizedCovariant` is the proposition giving the displayed source law
for all actual `m : M`, `u : U` and `x : G`. The theorem
`leviInflated_covariant_iff` proves equivalence with the full `P`-covariance
condition for this inducing action. In the forward direction, apply the
condition to the product of the two subgroup elements and use
`h.projection_mul`. In the reverse direction write `p = m*u` with
`m = h.projection p` and `u = m⁻¹*p`; membership of `u` follows from
`h.projection_inv_mul_mem`. Applying the source law then gives the result.

`leviNormalizedFunctionOf` constructs an actual induced function from this
covariance, an `OpenSubgroup G`, and invariance under every right multiplication
by its elements. It uses the existing `smoothFunctionOf` construction, so the
stabilizer is uniform in the argument of the function. The theorem
`leviNormalizedFunctionOf_eval` gives the original value at every `x`.

## Comparison and naturality

`inducingRepresentation_eq_leviInflated` identifies the existing full-parabolic
inducing representation with the Levi-twist-before-inflation representation
on their common original carrier. Rewrite the full half-character using
`closedHalfCharacter_eq_comp_projection`; the resulting equality of actions is
definitional. The theorem `normalized_covariant_iff_levi` combines that equality
with the preceding covariance equivalence.

The published `DynamicNormalization.normalizedInductionLeviTwistIso` is
reused directly. Its component uses the identity linear
equivalence on the inducing carrier and applies smooth induction to it.
`normalizedInductionLeviEquiv` extracts the component representation
equivalence with `SmoothRep.equivOfIso`. Accordingly,
`normalizedInductionLeviEquiv_eval` and
`normalizedInductionLeviEquiv_symm_eval` are definitional equalities preserving
every actual function value in both directions. The maps are equivariant for
the actual ambient group actions.

`normalizedInductionLeviEquiv_natural` compares the two paths for any actual
Levi morphism. Both apply the original linear map pointwise, so nested subtype
extensionality and function extensionality prove the equality. The additional
`normalizedInductionLeviIso_hom_eval` and
`normalizedInductionLeviIso_inv_eval` expose the same value-preservation laws
directly for the reused categorical isomorphism's component maps.

Finally, `leviInflatedInduction_right_translation` records that the ambient
action on the reused functor sends the value at `x` to the original value at
`x*g`. This fact is definitional and requires no unimodularity hypothesis.
