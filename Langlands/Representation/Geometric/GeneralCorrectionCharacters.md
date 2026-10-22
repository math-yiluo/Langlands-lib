# Actual Haar correction characters for the general geometric lemma

This construction imports the published actual normalizer Haar modulus from
`Langlands.Group.HaarModulus`, together with the published normalizer maps
and intersection subgroups. No modulus character or open-kernel assertion
is supplied as an extra input.

Let G be a locally compact topological group, and M, N, U, Q actual subgroups.
Assume U and Q are closed, M normalizes U, and N normalizes Q. For w in G,
write L = M ∩ w⁻¹(N), represented by `intersectionIn M N w`, and
C = U ∩ w⁻¹(Q), represented by `intersectionSource U Q w`.

`intersectionRadicalModulus` pulls the actual Haar character of U back along
`intersectionToRadicalNormalizer`. `intersectionCorrectionModulus` pulls the
actual Haar character of C back along `intersectionToCorrectionNormalizer`.
Their application lemmas expose these compositions. Both normalizer maps send
an element of L to the same underlying element of G; they use conjugation on U
and C, respectively. Closedness of C and local compactness of U and C follow
from the hypotheses through the imported constructions.

`haarCorrectionCharacter` is the complex unit-valued character

```text
mod_U^(1/2) * mod_(U ∩ w⁻¹(Q))^(-1/2)
```

on L. The half powers are the canonical positive real square roots, embedded
in the complex numbers; no square-root branch or modulus is supplied by the
caller. `haarCorrectionCharacter_apply` gives this exact scalar formula.
`haarCorrectionCharacter_sq` gives the product of the complex radical modulus
and the inverse complex correction-subgroup modulus. The proof uses
multiplicativity of the characters and the positive square-root square law.

If G is nonarchimedean, the two positive characters have open kernels by
continuous pullback of the actual normalizer Haar kernels.
Their kernel intersection is open and lies in the kernel of
`haarCorrectionCharacter`, proving its open kernel. No continuity of a
chosen decomposition, supplied smoothness assertion, or geometric-lemma
theorem is needed.

`haarCorrectionSmoothCharacter` bundles this character with the proved open
kernel. `haarCorrectionTwist` reuses the existing smooth-category twist
functor. Its action is the correction scalar times the original action, as
`haarCorrectionTwist_action` states. Its underlying module and linear maps
are those of the imported twist functor. The group universe and the
representation-carrier universe are independent.

For Bernstein--Zelevinsky's two closed triples (M,U,P) and (N,V,Q), the first
correction ε₁ is the construction at `(M,N,U,Q,w)`. The second correction ε₂
is the same construction at `(N,M,V,P,w⁻¹)`. The latter has domain
N ∩ w(M) and formula `mod_V^(1/2) * mod_(V ∩ w(P))^(-1/2)`.
In that application N ≤ Q and M ≤ P imply the required normalization of
Q and P. This generic implementation does not require either semidirect
decomposition, the six decomposability conditions, sigma compactness,
finite double cosets, or the limit-of-compact-subgroups assumptions.
Those remain hypotheses of the later orbit-piece and geometric-lemma statements.

The original source is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 1.7, printed 444 (PDF 5), for the
normalizer modulus convention, and section 5.1, printed 460 (PDF 21), for
the two displayed correction characters and their place in the symmetric
orbit-functor composite. Literature ID `bernstein-zelevinsky-1977-induced-i`;
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The scalar formula was checked against the rendered original page.

The bundled interfaces, weaker hypotheses and elementary restriction,
square and open-kernel proofs are internal implementation of those source
characters. This construction supplies no orbit-piece identification,
geometric-lemma filtration, or exactness theorem.

Author: Worker 14. The imported published Haar-modulus construction is by
Worker 76 and is not part of this unit.
