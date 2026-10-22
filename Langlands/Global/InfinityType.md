# Integral infinity characters

Author: Worker 2.

`Langlands.Global.InfinityType K` assigns an integer to each actual complex
embedding of the number field `K : Type u`. The carrier universe is arbitrary;
the coefficients are the usual complex numbers. Conjugation acts by precomposition
with conjugation of embeddings. Anticyclotomic weights are opposite at conjugate
embeddings. Purity of weight `w` means their sum is `w`. These are predicates on
the weights, with no global character-existence assertion.
Conjugation is proved involutive, and the anticyclotomic condition is proved
equivalent to purity of weight zero.

`DistinctWeightsAbove ι τ` expresses injectivity of the weights on the actual
embeddings extending `τ` along `ι`. In Henniart's application, the smaller field
is imaginary quadratic and the chosen complex embedding fixes one half of the
CM embeddings. The generic predicate does not assert this arithmetic hypothesis.

The complex character with weights `(p,q)` is `z^p conjugate(z)^q`.
The map `coordinate` evaluates an actual archimedean idele at its place and
applies Mathlib's continuous extension of the chosen complex embedding to that
completion. For totally complex number fields, `toCharacter` multiplies the
local complex characters, taking the two weights from the chosen embedding and
its conjugate. It is a constructed continuous homomorphism on
`NumberField.InfiniteAdeleRing K` units. Anticyclotomic weights give the formula
`(z/conjugate(z))^p` at each place, and the resulting character is proved to
have modulus one. The local character is unchanged when its exponents are
swapped and its coordinate is conjugated, as proved by
`complexCharacter_conjugate`. The place orientation used in `toCharacter`
is explicitly Mathlib's chosen embedding. `coordinate_diagonal` verifies that
evaluation on the diagonal field units agrees with that embedding.
The comparison with the actual CM involution
uses `NumberField.IsCMField.complexConj` and its embedding identity.

The constructors prove multiplicativity and continuity using integral powers,
complex conjugation, continuous completion embeddings, and finite products.
Unitarity in the anticyclotomic case follows from
`|z/conjugate(z)|=1`; no global unitarity or character-extension theorem is used.

Source: G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
sur un corps p-adique* (2000), section 3.4, printed p.449, condition 2;
section 3.5, printed p.450, prescribed weights and the infinity character
in Lemma 1. These original passages were read directly. The integral
two-exponent construction and purity terminology are generalizations of the
opposite-exponent character used there, expressed on actual completions.
The generic `IsPureOfWeight` predicate records the displayed sum condition;
this source is used for its weight-zero specialization, not for a claim about
purity of arbitrary automorphic or motivic objects.
The formula fixes the exponent sign as written, without an inverse convention.

Literature ID: `henniart-2000-simple-proof`.
SHA256: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

The parent task separately requires a Hecke character with this infinity type,
global conjugate self-duality, finite-place regularity and specified components.
This pair constructs the archimedean character itself. It does not assert descent
through principal units, extension to ideles, existence, or automorphic induction.
