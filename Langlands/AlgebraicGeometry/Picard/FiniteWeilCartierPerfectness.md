# Cartier perfectness of the actual finite Weil pairing

Author: Worker 195. This is an internal assembly from the published
actual finite Weil construction, relative dual-multiplication comparison,
and the exact proposition `RelativeDualKernelCharacterBijectiveStatement`.
The latter remains an explicit theorem dependency `duality`.

Let `S` be any quasi-separated scheme, `A/S` an actual abelian scheme,
and retain its actual dual-scheme witness, inverse Poincare line bundle
and evaluation isomorphism, together with the seven displayed
tensor/Picard propositions. Let `n` be a natural number whose image
in the global sections of `S` is a unit. The published
`multiplication_isIsogeny_of_isUnit` establishes that the actual map
`[n]` is an isogeny. No numerical rank or polarization is an input.

`dualTorsionCharacter_bijective` applies the relative theorem dependency
to `[n]`. The published actual dual-multiplication kernel isomorphism
identifies its source with the actual `n`-torsion of the constructed dual.
Postcomposition with its inverse is bijective; the proof uses its two
inverse identities explicitly. The resulting map is exactly the
published `dualTorsionCharacter`, which defines `finiteWeilValue`.
This holds on every test scheme `T` over `S`, including nonreduced ones.

`finiteWeilCartierEquiv` retains the additive group structure using the
published `dualTorsionCharacterAddHom`. `finiteWeilCartierIso` packages
these equivalences as a natural isomorphism

`T ↦ A^dual[n](T)  ≅  T ↦ Hom_T(A[n]_T, Gm_T)`.

On the left the actual point group is written additively; on the right
`Cartier.characters` uses its canonical base-change presentation.
Naturality is exactly `dualTorsionCharacter_restrict`.
`finiteWeilCharacterHomIso` composes with the existing explicit
`Cartier.characterHomNatIso` to obtain the displayed actual-Hom
presentation. The component formulas preserve the original character.
`finiteWeilCartierIso_muEvaluation` proves by reflexivity that evaluating
it through the canonical lift to `mu S n` gives the original
`finiteWeilValue`, in the order primal point, dual point.

Thus the second-variable currying of the actual finite Weil pairing
identifies the dual torsion functor with the Cartier dual functor of
primal torsion. This is Cartier perfectness as a group-valued functor
statement, rather than a claim that the group homomorphisms between
the two groups of `T`-points exhaust all characters on `T`-points.
The assertion retains its exact relative theorem dependency; it does
not supply its independent proof, dual existence or dual geometry.
It makes no integral-perfectness assertion about a pairing pulled back
through an arbitrary polarization, and no alternation or rank claim.

All constructions and equalities here are derived from the named
Library declarations. The unchanged finite-Weil and relative-bijectivity
Markdown record their original-source character convention and the
scope of the derived relative formulation; this unit adds no external
mathematical input.
