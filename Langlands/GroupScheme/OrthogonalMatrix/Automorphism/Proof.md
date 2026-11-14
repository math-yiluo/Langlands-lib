# Automorphisms of the split `SO_{2n}` are conjugations by similitudes

## Statement

`specialOrthogonalAutomorphism` proves the Library proposition
`SpecialOrthogonalAutomorphismStatement` at every universe `u`:

```
theorem specialOrthogonalAutomorphism : SpecialOrthogonalAutomorphismStatement.{u}
```

For a field `L` and `n ≥ 2`, every automorphism `α` of the split special
orthogonal group `SO_{2n}` (the identity component of
`groupScheme (Fin n) L`) is conjugation by a similitude `g` of the split
quadratic form: `g Q gᵀ − μ Q` is alternating for a unit `μ`, and on points
`α(x) = g x g⁻¹`. This is `Aut(SO_{2n}) = PGO_{2n}`
(Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, (26.15) and §26.B),
in every characteristic.

## Proof

The body of the statement for `α` is, once `IsSimilitude` is unfolded,
exactly `IsSimilitudeConj α` (`Automorphism/Conjugation`).

Below, `α ≪≫ γ` is the composite automorphism: first `α`, then `γ`.

1. `exists_isSimilitudeConj_comp_fix hn α` (`Automorphism/TorusNormalization`,
   by Worker 1383) gives an automorphism `γ` with `IsSimilitudeConj γ` and
   `identityTorus (Fin n) L ≫ (α ≪≫ γ).hom = identityTorus (Fin n) L`, that
   is, `α ≪≫ γ` is the identity on the diagonal torus. There,
   `γ = SO.innerIso p ≪≫ specialConjIso (permGL L σ) 1 _`. The rational point
   `p` of `SO_{2n}` comes from the conjugacy of maximal split tori
   (`smoothMaximalSplitTorusConjugacy`). `σ` is a signed permutation of
   `Fin n ⊕ Fin n` that undoes the action on the root lattice
   (`Automorphism/SignedPermutation`, by Worker 1383), and its permutation
   matrix is orthogonal.
2. `isSimilitudeConj_of_comp_identityTorus hn (α ≪≫ γ) hfix`
   (`Automorphism/RootScaling`) shows that `α ≪≫ γ` is conjugation by a
   similitude. Since it fixes the torus, it scales the simple root vectors of
   the pinning of `SO_{2n}` on the diagonal torus. Conjugation by a diagonal
   similitude undoes this scaling, and pinned rigidity finishes the argument.
3. `IsSimilitudeConj.of_trans` (`Automorphism/Conjugation`): since both
   `α ≪≫ γ` and `γ` are conjugations by similitudes, so is `α`
   (it equals `(α ≪≫ γ) ≪≫ γ⁻¹`).
