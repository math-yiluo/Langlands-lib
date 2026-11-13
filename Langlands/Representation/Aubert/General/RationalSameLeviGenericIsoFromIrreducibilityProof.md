# Same-Levi generic isomorphism from generic irreducibility: proof

Author: Worker 5266.

This module proves the published statement
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericInductionIsoFromIrreducibilityStatement.{u, v}`.
Its theorem is
`Langlands.Aubert.General.RationalPointFamily.rationalSameLeviGenericInductionIso_of_irreducibility`.
The module also proves one general helper lemma.

## Helper: Schur's lemma for smooth representations

`Langlands.SmoothRep.nonempty_iso_of_isIrreducible_of_ne_zero` works at
arbitrary universes, over any field `k` and any topological group `G`. Let
`A` and `B` be smooth representations (`SmoothRep k G`) that are both
irreducible (`SmoothRep.IsIrreducible`), and let `f : A ⟶ B` be a nonzero
morphism. Then `A ≅ B`.

The proof applies Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` to the underlying
intertwining map `SmoothRep.hom f`. Both irreducibility hypotheses are placed
in context as instances.

- If that map is bijective, then `IntertwiningMap.ofBijective` gives an
  equivalence of representations. `SmoothRep.mkIso` turns it into an
  isomorphism in the smooth category.
- If the map is zero, then `f = ofHom (hom f) = ofHom 0 = 0`, by
  `SmoothRep.ofHom_hom`. This contradicts `f ≠ 0`.

## Main theorem

Assume the premise `RationalSameLeviGenericInductionIrreducibilityStatement`
and introduce all data of the target `RationalSameLeviGenericInductionIsoStatement`.
The proof then makes three instance facts available:

- the affineness facts needed to form the coordinates (`hG.isAffineHom` and
  `IsAffine G.X.left`);
- `pointTopology` as the topology on `G(k)`.

It then proceeds as follows.

1. The premise, applied to the same data, gives a nonzero polynomial `p`.
   For every `χ` in `leviUnramifiedPrincipalOpen i ν J hLJ p`, both
   `i_{P_J}(σ ⊗ χ)` and `i_{g P_I g⁻¹}(σ ⊗ χ)` are irreducible.
2. The published theorem `rationalSameLeviGenericNonzeroIntertwiner` (module
   `Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerProof`),
   applied to the same data, gives a nonzero polynomial `q`. For every `χ` in
   its principal open there is a nonzero morphism
   `i_{P_J}(σ ⊗ χ) ⟶ i_{g P_I g⁻¹}(σ ⊗ χ)`.
3. The witness is `p * q`. It is nonzero by `mul_ne_zero`, because the
   multivariate polynomial ring over `ℂ` has no zero divisors.
4. Take `χ` in the principal open of `p * q`. Then `mem_leviUnramifiedPrincipalOpen`
   and `map_mul` show that evaluation of `p * q` at the coordinates of `χ`
   is nonzero. By `left_ne_zero_of_mul` and `right_ne_zero_of_mul`, the
   evaluations of `p` and `q` are nonzero. So `χ` lies in both principal
   opens.
5. Steps 1 and 2 give irreducibility of both inductions and a nonzero
   morphism between them at `χ`. The helper lemma turns these into the
   required isomorphism.

The proof uses no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`.
