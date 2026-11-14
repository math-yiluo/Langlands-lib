# Isogeny sections of surjections of tori

`Langlands.GroupScheme.TorusSurjectionIsogenySectionStatement.{u}` is an
unproved proposition about homomorphisms of tori over a field. This module
supplies no proof.

## Exact formulation

Let `k : Type u` be a field and let `B` and `C` be commutative group schemes
over `Spec k` (`CommGroupScheme`) whose underlying group schemes are tori.
Let `q : B.toGrp ⟶ C.toGrp` be a homomorphism whose underlying scheme map is
surjective. The conclusion is that there are a positive natural number `n`
and a homomorphism `s : C.toGrp ⟶ B.toGrp` with

```text
s ≫ q = multiplication C.toGrp n,
```

that is, `q ∘ s` is multiplication by `n` on `C`. No hypothesis on the
kernel of `q`, no splitting field and no affineness assumption is imposed.
The statement is at arbitrary universe `u`.

## Provenance

This is an internal statement, not a numbered result of the source. It
supplies the finite-index input of Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Corollary B.8.6, printed pp. 682–683 / PDF pp. 713–714. The Library's
assembly applies the source's Lemma A.4.26 directly over the Henselian ring of
integers, so this input replaces the source's use of Lemma A.4.25 and
completion. The assembly module is
`Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly`.

The intended justification is the standard anti-equivalence between tori
and Galois lattices. A surjection `q` of tori induces an injection
`X^*(C) → X^*(B)` of character lattices that commutes with the Galois
action. Over `ℚ`, Maschke's theorem for the finite Galois group through
which the action factors gives an equivariant retraction
`X^*(B)_ℚ → X^*(C)_ℚ`. A positive multiple `n` of it is integral. Its dual
homomorphism `s` satisfies `q ∘ s = n`.

## Remaining proof obligation

A proof must construct `s` from such a retraction, or by another argument,
and verify the identity of group-scheme homomorphisms.
