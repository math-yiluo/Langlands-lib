# Unramified twists in the maximal-Levi reducibility theorem

Module `Langlands.Representation.Exponents.MaximalLeviTwistReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques* (2026 version,
literature ID `renard-2026-representations-groupes-reductifs-padiques`), VII.1.3, first
paragraph of the proof (printed p.224, PDF p.230). If the central character of
`π = i_P^G ρ` is not unitary, Renard picks an unramified character `χ` of `G` that makes
the central character of `π ⊗ χ` unitary (an argument from the proof of VI.8.5). By the
Mackey isomorphism III.2.11, `π ⊗ χ ≅ i_P^G(ρ ⊗ χ|_M)`. So `π` is reducible exactly when
`π ⊗ χ` is, and the conclusion for `ρ` follows from the conclusion for `ρ ⊗ χ|_M`.

This module formalizes that paragraph for the represented-parabolic interface
(`leviInductionFunctor`, `jacquetFunctor`). It assumes two statements from
`Langlands.Representation.Exponents.MaximalLeviReducibilityReductionStatements`:

- `MaximalLeviSupercuspidalReducibilityUnitaryStatement`: the theorem for inductions
  with a unitary central character.
- `MaximalLeviUnitaryCentralTwistStatement`: the existence of the twist `χ`.

The characters `χ_M` used throughout are that module's
`leviRestrictedCharacter p l χ = χ ∘ (l ≫ p)(F)`.

Renard writes "the conclusion is deduced" without detail. The four transfer steps
(irreducibility, supercuspidality, reducibility, conclusion) are spelled out here. The
triviality of unramified characters on unipotent points is the standard fact that
rational characters are trivial on unipotent groups. It is derived in
`UnramifiedTwistRadicals` and is not quoted from a numbered result of Renard.

## Declarations

### Imported general lemmas

The facts that do not depend on the maximal-Levi setting are in the imported module
`Langlands.Representation.Exponents.UnramifiedTwistRadicals`, documented in its own
Markdown file. This module uses from it:

- `unramifiedCharacter_map_eq_one_of_isUnipotent`: an unramified character of `G(F)` is
  trivial on the points of a unipotent group mapped into `G`;
- `unramifiedSmoothCharacter`: an unramified character of `G(F)` as an
  `Induction.SmoothCharacter`;
- `pointImage_radical_le_ker_unramifiedSmoothCharacter`: an unramified character of
  `G(F)` kills the radical image `(r ≫ p)(F)(U(F))`;
- `jacquetFunctor_subsingleton_twist_iff`: for any actual parabolic `p' : P' ⟶ H` and
  any smooth character `χ` of `H(F)` that is trivial on the radical image, the
  normalized Jacquet module of `A ⊗ χ` is zero iff that of `A` is.

### Restricted characters

- `leviRestrictedCharacter_map_eq_of_conj`: if `φ : M ≅ M` satisfies
  `φ ≫ l ≫ p = l ≫ p ≫ Int(g)`, then `χ_M(φ(F) m) = χ_M(m)` for every character `χ` of
  `G(F)`. Proof: `(l ≫ p)(F)(φ(F) m) = g · (l ≫ p)(F)(m) · g⁻¹`
  (`pointMap_comp_apply`, `rationalPoints_map_innerIso`), and `χ` takes values in a
  commutative group.
- `leviRestrictedCharacter_map_radical_eq_one`: for unramified `χ`, `χ_M` is trivial on
  the radical points `(r' ≫ p')(F)(y)` of every parabolic `p' : P' ⟶ M` with geometric
  unipotent radical `r'`. The radical is unipotent, so this follows from
  `unramifiedCharacter_map_eq_one_of_isUnipotent` applied to `r' ≫ p' ≫ l ≫ p`.

### The twisting isomorphism (III.2.11)

- `pullback_leviRestrictedCharacter_twist_representation`: transport `σ ⊗ χ_M` along
  `leviPointsEquiv` to the Levi image `L = (l ≫ p)(F)(M(F)) ⊆ G(F)`. The result is the
  twist of the transported `σ` by `χ` restricted to `L` (`subgroupSmoothCharacter`).
  The actions agree pointwise because `leviPointsEquiv` is the point map of `l ≫ p`.
- `leviInductionUnramifiedTwistIso`:
  `i_P^G(σ ⊗ χ_M) ≅ (i_P^G σ) ⊗ χ`. `leviInductionFunctor` is
  `pullbackFunctor (leviPointsEquiv …).symm ⋙ inductionFunctor`. The isomorphism is
  `inductionFunctor` applied to the identity-carrier isomorphism of the previous lemma
  (`equivOfRepresentationEq`), followed by the inverse of the published
  `normalizedInductionCharacterTwistIso`. That result needs `χ` trivial on the radical
  image, which `pointImage_radical_le_ker_unramifiedSmoothCharacter` supplies.
- `leviInduction_isIrreducible_unramifiedTwist_iff`: `i_P^G(σ ⊗ χ_M)` is irreducible iff
  `i_P^G σ` is. Proof: `SmoothRep.isIrreducible_twist_iff` and transport of
  irreducibility along the isomorphism in both directions.

### Conclusion transfer

- `intertwining_relation_of_twist`: let `ν` be a character with `ν ∘ f = ν`. If a linear
  automorphism `T` satisfies
  `T((ρ ⊗ ν)(m) x) = c(m) • (ρ ⊗ ν)(f m)(T x)` for all `m` and `x`, then
  `T(ρ(m) x) = c(m) • ρ(f m)(T x)`. Proof: expand the twist,
  `ν(m) • T(ρ(m) x) = c(m) • ν(f m) • ρ(f m)(T x)`. Then use `ν(f m) = ν(m)`, commute the
  scalars and cancel the unit `ν(m)` (`smul_right_injective`).

### The reduction

- `maximalLeviSupercuspidalReducibility_of_unitary`:
  `MaximalLeviSupercuspidalReducibilityUnitaryStatement →
  MaximalLeviUnitaryCentralTwistStatement → MaximalLeviSupercuspidalReducibilityStatement`
  (universes `u v` throughout). Proof: introduce the data of the target and an
  irreducible supercuspidal `ρ` whose induction is reducible.
  `MaximalLeviUnitaryCentralTwistStatement` gives an unramified `χ` such that
  `i_P^G(ρ ⊗ χ_M)` has a unitary central character. The twist `ρ ⊗ χ_M` satisfies the
  hypotheses of the unitary statement:
  - it is irreducible (`SmoothRep.isIrreducible_twist_iff`);
  - every proper Jacquet module vanishes (`jacquetFunctor_subsingleton_twist_iff` with
    `leviRestrictedCharacter_map_radical_eq_one`);
  - its induction is reducible (`leviInduction_isIrreducible_unramifiedTwist_iff`).

  The unitary statement then gives `g`, `φ`, `ψ` and `T` for `ρ ⊗ χ_M`. The same
  `g`, `φ`, `ψ` and `T` work for `ρ`: the twist leaves the carrier unchanged, and
  `intertwining_relation_of_twist` applies with `f = φ(F)`, using
  `leviRestrictedCharacter_map_eq_of_conj`.

This theorem is a conditional reduction. It does not prove the target by itself; the
two statements it assumes must still be proved.
