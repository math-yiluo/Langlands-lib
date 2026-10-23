# Central characters and cusp forms

This module restricts the actual complex automorphic form space
`AutomorphicForms K n`, for a number field `K : Type u` and any natural rank `n`.
It constructs forms with a specified central character, cusp forms, and cusp
forms with a specified central character. The scalar field is complex throughout.

## Construction and finite translation

For an ambient subrepresentation `S` of `continuousRightAction K n`,
`automorphicRestriction K n S` is the inverse image of its submodule along
`automorphicToContinuous`. Thus its elements are actual automorphic forms whose
underlying continuous rational-invariant functions belong to `S`. The membership
theorem is definitional. Ambient right-translation invariance implies invariance
under the finite adelic factor.

`RestrictedAutomorphicForms` is the resulting complex vector space.
`restrictedAutomorphicFiniteRightAction` is its inherited finite adelic
representation. Its smoothness follows from the open stabilizer of the underlying
automorphic form and injectivity of the subtype inclusion.
`restrictedAutomorphicInclusion` is an injective intertwiner into all automorphic
forms. `restrictedAutomorphicToContinuous` is the injective linear realization as
continuous rational-invariant functions. Its equivariance and evaluation formulas
are proved: right translation by `d` sends `f(x)` to
`f(x * AdelicGL.ofFinite K n d)`.

These constructions and proofs apply to each of the three specializations below;
the named actions are abbreviations of this same representation.

## Specified central character

For a continuous character
`χ : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ`,
`centralCharacterAutomorphicSubrepresentation` pulls back
`centralCharacterSubrepresentation K n χ`. Its carrier is
`CentralCharacterAutomorphicForms K n χ`, with finite action
`centralCharacterAutomorphicFiniteRightAction K n χ`.

The explicit membership theorem requires, for every idele `z` and adelic matrix
`x`,

\[
 f(\operatorname{scalar}(z)x)=\chi([z])f(x).
\]

Here `centralIdeleCharacter K χ` is the existing pullback of `χ` along the actual
idele-class quotient. This fixes the character convention without an inverse.
No unitary hypothesis is imposed. Principal ideles act trivially on the character
by the already published `centralIdeleCharacter_principal`.

## Cusp forms and the compactness parameter

All cuspidal declarations retain the instance parameter
`[CompactSpace (AdeleQuotient K)]`. This is the actual additive adele quotient
with its published quotient topology. For every `K : Type u` with
`[Field K] [NumberField K]`, `Langlands.Global.adeleQuotientCompact K` proves
its compactness in
[`Langlands.Global.AdeleQuotientCompactProof`](../Global/AdeleQuotientCompactProof.md).
A caller can add `import Langlands.Global.AdeleQuotientCompactProof` and use
`haveI := Langlands.Global.compactSpace_adeleQuotient K` locally to supply the
required instance. This companion theorem has type
`CompactSpace (AdeleQuotient K)` and is not registered as a global instance.
The explicit parameter remains part of this module's interface; the arithmetic
proof supplies it for the fixed quotient topology. See
[`ConstantTerm`](ConstantTerm.md) for the compactness source and measure
construction.

`cuspidalAutomorphicSubrepresentation` pulls back `cuspidalSubrepresentation`
from `ConstantTerm`. Its carrier `CuspidalAutomorphicForms` therefore consists
exactly of the automorphic forms satisfying the existing `IsCuspidal` predicate.
The finite action is `cuspidalAutomorphicFiniteRightAction`.

That predicate requires the constant term to vanish for every standard maximal
upper block parabolic, with positive block sizes `a,b` and `a+b=n`, at every
adelic matrix. The constant term is the integral of `f(u(X)g)` over the actual
matrix space over `AdeleQuotient K`, using the Borel Haar probability measure from
`ConstantTerm`. The lift-independence and integrability proofs are reused.
`constantTerm_cuspidalAutomorphicForm` exposes this vanishing directly.

`centralCharacterCuspidalSubrepresentation` pulls back the intersection of the
two ambient conditions. Its carrier is `CentralCharacterCuspidalForms` and its
finite action is `centralCharacterCuspidalFiniteRightAction`, with the named
representation type `CentralCharacterCuspidalFiniteAction`. The membership
theorem gives precisely central-character membership and cuspidality of the same
function. The subrepresentation is proved equal to the intersection of the two
separately constructed automorphic subrepresentations.
`constantTerm_centralCharacterCuspidalForm` exposes its constant-term vanishing.

## Source and provenance

The original source is A. Borel and H. Jacquet, *Automorphic forms and automorphic
representations*, Corvallis Part I (1979). Section 4.3(3), printed p.195
(one-based PDF page 190), gives the central-character transformation law.
Section 3.3, printed p.194 (PDF189), defines cuspidality and says it suffices to
test representatives of proper maximal rational parabolics. Section 4.4,
printed p.196 (PDF191), defines a cusp form as a cuspidal automorphic form.
For `GL_n`, the center is the scalar torus and these representatives are the
positive two-block standard parabolics used by `ConstantTerm`.

This is a derived construction from those definitions. The ambient conditions,
idele-class pullback, normalized constant terms, actual automorphic forms and
their finite action are reused by name. The new content is their inverse-image
construction, membership identifications, inherited smooth finite actions and
injective function realizations. The reduction from all proper parabolics to
the block representatives, and an identification of the matrix quotient with
the unipotent quotient, are not new formalized results here.

The module does not assert nonzero forms, admissibility, square-integrability,
irreducibility, a cuspidal automorphic representation object, or a full
archimedean/Hecke action. It includes rank zero, and its block-vanishing condition
is vacuous when the rank is zero or one.

Registered source: `borel-jacquet-1979-automorphic`.
Original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
