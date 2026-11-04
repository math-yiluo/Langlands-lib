# Bruhat bijectivity across components

This internal algebraic module implements the component reduction used in the
authors' corrected proof of Kaletha–Prasad Theorem 7.8.1(2). It does not construct
an Iwahori–Tits system for a reductive group.

The groups and component groups have independent universes. Given compatible
homomorphisms `π : N →* W`, `q : G →* Γ`, and `c : W →* Γ`, `kernelProjection`
restricts `π` to the normalizer inside `ker q` with values in `ker c`.
The assumptions are a Tits system in `ker q`, containment `B ≤ ker q`,
surjectivity of `π`, and normalizer representatives of every component that
normalize `B`. The construction `componentDoubleCosetEquiv` has type `W ≃ B\G/B`.
Its theorem `componentDoubleCosetEquiv_apply` specifies the value on every `n : N`.
The supporting theorem `exists_component_doubleCoset_equiv` proves existence
before the construction selects an equivalence using classical choice.

For injectivity, equality of the double cosets first implies equality of
components because `B ≤ ker q`. Choose one normalizing representative `r`
of that common component. Both `n r⁻¹` and `m r⁻¹` belong to `ker q`.
Conjugating the right Borel factor by `r` preserves `B`, so these two elements
have equal Borel double cosets inside `ker q`. Abstract Bruhat uniqueness
from `IsTitsSystem.eq_of_mem_cell` then gives equality of their images under
`kernelProjection`. Cancellation yields `π n = π m`.

For surjectivity, remove a normalizing representative of the component of
`g`, apply Bruhat existence in the kernel, and move the right Borel factor
past that representative. The kernel of `π` is contained in `B` by the
kernel Tits system, which makes the representative choice in the constructed
equivalence well defined.

This is a derived, reusable algebraic implementation of the correction:
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, Theorem 7.8.1 and 7.8.2,
PDF pages 303–304; and *Corrections and additions*, 1 November 2024,
registered source `kaletha-prasad-2024-corrections`, PDF page 35.
The latter replaces the insufficient printed normalizer-intersection argument
with a component comparison followed by Bruhat uniqueness. Here a single
representative of the common component suffices; uniqueness of a chamber
splitting is not needed for this internal lemma. Application to the published
global building targets still requires the actual Tits system and normalizing
component representatives, proved from those targets' unchanged hypotheses.
