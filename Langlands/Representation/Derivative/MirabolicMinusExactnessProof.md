# Exactness of the four actual mirabolic minus functors

Author: Worker 127; Workers 452 and 971 are credited for the adapted coset
argument described below.

This module proves the existing proposition
`Langlands.Derivative.Mirabolic.MinusExactnessStatement` with theorem
`Langlands.Derivative.Mirabolic.minusExactness`. The field and representation
carrier universes remain independent. The result applies to every rank,
including zero, for the supplied `PadicField.TopologicalData`, and to every
unitary additive character in the existing Phi telescope.

For each of the four actual functors, an injective underlying intertwiner
followed by a surjective intertwiner with range equal to kernel gives induced
maps with all three of the same properties.

## Source and normalization

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups. I*,
Annales scientifiques de l'École Normale Supérieure (4) 10 (1977), 441–472,
§1.8(b), pp.444–445, §1.9(a), p.445, and §§3.1–3.2, pp.450–451, are the original
source. The registered source is `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Proposition 3.2(a) asserts exactness and its proof refers to §1.9. Section 3.1
specifies the actual mirabolic radical and its last-coordinate character.
Section 1.9(a) uses containment of every compact subset in a compact subgroup.
The supplied PDF pages 5–6 and 11–12 were read. No applicable errata were found
in the project's bounded literature and public-note search.

The source localization includes inverse-half Haar normalization. Here the
unnormalized functors first use the actual character quotient, then continuous
pullback along the actual Levi or successor equivalence. The normalized functors
apply the already defined inverse-half determinant character twist. The proof
uses the fact that those pullbacks and twists preserve the underlying linear
maps. It does not identify the determinant character with a Haar modulus.

## Implemented proof

The internal closed-embedding lemma factors the radical's inclusion into the
ambient general linear group through the upper-unipotent subgroup. Both the
mirabolic subgroup and its radical are closed by their entry equations.
The upper-unipotent subtype inclusion is an embedding, so the radical inclusion
into the upper-unipotent group is a closed embedding.

`radical_isLimitOfCompactSubgroups` sends a compact set through this inclusion
and applies the published
`GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups`. Pulling the resulting
compact subgroup back through the closed embedding gives a compact subgroup of
the actual radical containing the original set. This argument covers rank zero
without an extra premise.

The trivial character is locally constant. For the positive last-coordinate
character, `T.mirabolicTheta_isOpen_ker` supplies its open kernel. The internal
local-constancy argument uses the open coset neighborhood
`{y | y * x⁻¹ ∈ ker χ}` of each `x`; the homomorphism equation makes the character
constant there. These elementary topology arguments are derived helpers, not
separate claims attributed to the source.

The coset proof is adapted from the private open-kernel helper in the published
`Unitary.AffineL2ContinuityProof` module, authored by Workers 452 and 971. They
are credited as coauthors for that adapted text. Only this elementary group
argument is reused; its proof uses continuity of multiplication and the
homomorphism laws. The affine L² module is not imported.

The internal localization helper instantiates
`Jacquet.Localization.characterLocalizationExactness` on the three actual smooth
representations and their actual intertwiners. It supplies radical compact
containment, character local constancy, the published normalizer and character
invariance facts, and the middle object's bundled smoothness. The supplied
topological data establishes the needed topological group instances.

The continuous pullback and character-twist helpers transfer injectivity,
range-equals-kernel, and surjectivity together by definitional equality of the
underlying linear maps. The first two conjuncts use localization followed by the
actual continuous pullbacks. The last two use the same maps after the fixed
determinant twists.

## Dependency boundary

The three direct imports are the unchanged exactness statement, localization
exactness proof, and upper-unipotent compact-containment proof. The latter uses
an elementary integral-denominator construction from
`RankinSelberg.UnipotentUnimodularity`; this is lower matrix, valuation and compact
subgroup infrastructure. Localization exactness uses finite compact averaging
and quotient linear algebra. No segment, classification, plus functor,
adjunction, derivative iteration or filtration, or representation-pairing result
is used by this proof. Algebraic dual and matrix-coefficient definitions already
occur in the statement's character infrastructure; they supply no pairing
theorem here.

The transitive project import closure consists of 67 existing modules plus this
proof. All 67 existing Lean/Markdown pairs are unchanged. The closure contains no
module or conclusion from the task's excluded segment and classification routes.
The adapted coset argument has only elementary topological group assumptions and
uses no analytic theorem from its original module.

## Development validation

The proof and a private complete unapplied theorem assignment were compiled in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no errors or warnings.
Declaration inspection reports exactly the independent level parameters `uF`
and `uV`, the requested prime/field/topological-data telescope, and only
`propext`, `Classical.choice`, and `Quot.sound` as kernel assumptions.
These development checks are separate from independent review and publication.
