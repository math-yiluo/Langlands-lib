# Actual root support through an integral split torus

This internal construction compares actual adjoint roots through the characters
of a supplied integral split torus. It works at arbitrary universe `u`.
The root convention is the Library convention: a root is a nonzero character
whose adjoint Lie weight space is nonzero.

The general comparison assumes a local domain `R`, two fields `k` and `l`
with `R`-algebra structures, a smooth affine group scheme `H` over `R`,
a commutative group scheme `T`, a split-torus witness for `T.toGrp`,
and a group morphism `j : T.toGrp ⟶ H`.
For each actual integral character `χ`, the theorem
`GroupScheme.mem_roots_baseChange_iff_of_split` states that its base change
is a root of the base change of `j` over `k` if and only if it is a root
over `l`. The theorem needs neither closedness of `j` nor a maximality
assumption on the torus.

## Construction for integral models

Let `R` be a local domain with fraction field `K`, let `G` be an affine
`K`-group scheme, and let `D : RelativeComponentModelData R K G`.
Take `S`, `i : S.toGrp ⟶ G`, and
`T : IntegralTorusData D S i` as supplied data. The latter contains an actual
integral torus, its inclusion into `D.neutral.group`, a generic-fibre
isomorphism with `S`, and the commuting generic-fibre square.
The smoothness of the neutral model is part of `D`.
All comparisons except the generic-fibre transport additionally use
`hT : IsSplitTorus T.torus.toGrp`.

The characters and the specialization map used here are the existing
`T.genericCharacter`, `T.specialCharacter`, and
`T.characterSpecialization hT` from `FacetLieWeights`.
The specialization is the canonical additive equivalence obtained by passing
from generic characters to integral characters and then taking their residue
base change. No extra lattice identification is chosen in this module.

The declarations in namespace `IntegralTorusData` give:

- `mem_relativeRoots_genericCharacter_iff`: root membership of
  `T.genericCharacter χ` is equivalent to root membership of the actual
  base-changed integral character in the generic fibre of the neutral model.
  This transport alone does not require `IsLocalRing R` or a split witness.
- `mem_relativeRoots_specialCharacter_iff`: `T.specialCharacter χ` is a
  root of the neutral special fibre exactly when `T.genericCharacter χ`
  is a root of `G` relative to `i`.
- `mem_relativeRoots_characterSpecialization_iff`: the same assertion for
  every generic character, under the canonical specialization.
- `relativeRoots_specialFibre_eq_image`: the actual neutral special-fibre
  roots are precisely the specializations of the generic roots.
- `rootsSpecializationEquiv`: the resulting equivalence between those two
  root sets. Its value on the underlying character is exactly
  `T.characterSpecialization hT`, as recorded by
  `rootsSpecializationEquiv_character`.
- `relativeRoots_quotient_subset_image`: for a supplied
  `Q : SpecialFibreQuotientData D` satisfying `Q.IsReductiveQuotient`, every
  root relative to `T.specialFibreInclusion ≫ Q.projection` is the
  specialization of a generic root.

The last assertion uses the actual represented reductive quotient and its
radical, through the existing quotient-root containment theorem. It does not
assume or prove that the composite torus map is closed or maximal.

## Implemented proof

For a coordinate split torus, the character-lattice equivalence writes each
integral character as a finite sum of exponent characters. The actual
base-change isomorphism of split tori transports each base-changed character
to the exponent character with the same integer coordinates. The published
`splitTorus.mem_roots_fieldBaseChange_iff_of_isLocalRing` then compares root
membership on the two field-valued fibres. That theorem comes from constancy
of the adjoint weight-rank profile over a local base.

For an arbitrary supplied split torus, the proof chooses a split presentation
and transports the characters and torus morphism through its base change on
each fibre. The published `roots_mem_of_transport_iff` identifies the actual
root sets under these commuting isomorphism squares. Combining both
transports with the coordinate result proves the general comparison.

For the integral-model adapter, the same transport theorem applies to the
generic-fibre square specified in `T`. The general comparison then applies
to the fraction-field and residue-field fibres of `D.neutral.group`.
The existing generic-character equivalence accounts for every generic
character. Restricting the canonical specialization equivalence to the two
root predicates constructs `rootsSpecializationEquiv`; its character formula
is definitional. Finally, rewriting the neutral special-fibre root set using
the proved equality reduces the quotient inclusion to
`SpecialFibreQuotientData.relativeRoots_subset_specialFibre`.

## Provenance and scope

This is an internal composition of published Library results:
`LocalRootSupportComparison`, the actual split-torus base-change and
character-lattice constructions, `CrossTorusLieTransport`,
`FacetLieWeights`, and `ReductiveQuotientRoots`.
It adds their actual-character and integral-model adapters and does not
claim a new direct formulation of a literature theorem.

The quotient inclusion gives only generic root support. It does not identify
which neutral weight spaces survive the radical quotient, characterize those
roots by affine roots vanishing on a facet, construct facet reflection
representatives, or compare coroots. In particular, the host proposition
`UnramifiedFacetRootDatumStatement` remains an additional proof obligation.
