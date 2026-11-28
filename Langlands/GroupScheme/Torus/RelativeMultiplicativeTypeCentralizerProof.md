# Proof: centralizers of subgroups of multiplicative type over a general base

This module proves `RelativeMultiplicativeTypeCentralizerStatement`
([`RelativeMultiplicativeTypeCentralizerStatement`](RelativeMultiplicativeTypeCentralizerStatement.md);
Conrad, *Reductive group schemes* (2014), Lemma 2.2.4 for subgroups of multiplicative type,
and Remark 3.1.5) in every universe. It contains two theorems and no definitions:

- `relativeMultiplicativeTypeCentralizer_of_identityComponentClopen`: the implication
  `IdentityComponentClopenStatement.{u} → RelativeMultiplicativeTypeCentralizerStatement.{u}`,
  where `IdentityComponentClopenStatement`
  ([`Reductive.IdentityComponentClopenStatement`](../Reductive/IdentityComponentClopenStatement.md))
  is Conrad's Proposition 3.1.3.
- `relativeMultiplicativeTypeCentralizer : RelativeMultiplicativeTypeCentralizerStatement.{u}`:
  this implication applied to `identityComponentClopen`
  ([`Reductive.IdentityComponentClopenProof`](../Reductive/IdentityComponentClopenProof.md)),
  the Library's proof of `IdentityComponentClopenStatement`.

## The proof

Fix a scheme `S`, a group scheme `G` over `S` with `G → S` affine and locally of finite
presentation, a commutative `H` with `IsMultiplicativeType H.toGrp`, and a homomorphism
`i : H.toGrp ⟶ G`. The hypothesis that `i` is a closed immersion is introduced and not used:
the cited theorems hold for every homomorphism.

1. **Representability.** `relativeMultiplicativeTypeCentralizer_isClosedRepresentable_of_affine`
   ([`RelativeMultiplicativeTypeCentralizerGeometry`](RelativeMultiplicativeTypeCentralizerGeometry.md))
   gives a group scheme `Z` and a homomorphism `z : Z ⟶ G` that represents
   `torusCentralizer i` and is a closed immersion. It needs only that `G → S` is affine.
   `relativeMultiplicativeTypeCentralizer_locallyOfFinitePresentation` (same module) shows
   that `Z → S` is locally of finite presentation, since `G → S` is.
2. **Smoothness.** For any `z : Z ⟶ G` representing `torusCentralizer i`,
   `relativeMultiplicativeTypeCentralizer_smooth_of_smooth` (same module) shows that `Z → S`
   is smooth when `G → S` is.
3. **Reductive identity component.** Let `G` be reductive, let `z : Z ⟶ G` represent
   `torusCentralizer i`, and let `z₀ : Z₀ ⟶ Z` satisfy `IsRelativeIdentityComponent Z z₀`. A
   reductive group is smooth (the field `IsReductive.smooth`), so `Z → S` is smooth by step 2.
   `relativeMultiplicativeTypeCentralizer_reductive`
   ([`RelativeMultiplicativeTypeCentralizerReductive`](RelativeMultiplicativeTypeCentralizerReductive.md))
   takes `IdentityComponentClopenStatement`, the field case
   `multiplicativeTypeCentralizerReductive`
   ([`MultiplicativeTypeCentralizerReductiveProof`](MultiplicativeTypeCentralizerReductiveProof.md)),
   the closed representability of step 1 and this smoothness. It gives `IsReductive Z₀`, that
   `z₀` is a closed immersion, and that every residue fibre `Z₀_s` is connected reductive.

The three parts follow the division of Conrad's Lemma 2.2.4 (pp.64–65) and Remark 3.1.5
(p.83). The route of parts (1) and (2) is that of `RelativeMultiplicativeTypeCentralizerGeometry`:
it descends the fixed-ideal construction for diagonalizable groups over rings along an affine
open cover and the fppf splitting cover of `H`, instead of Conrad's argument through the
torsion subgroups `H[n]` and Hochschild cohomology. Part (3) follows Remark 3.1.5: the fibre
assertion comes from the field case, and reductivity and closedness of `Z⁰` from
Proposition 3.1.3.
