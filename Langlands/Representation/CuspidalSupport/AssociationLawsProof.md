# Proof of the algebraic laws of Levi and representation association

Author: Worker 257.

`associationRelationLaws` proves the published proposition
`AssociationRelationLawsTheorem.{uF, uV, uW, uX}` from
`CuspidalSupport.AssociationLawsStatement`. The proposition is the conjunction
of `LeviAssociationEquivalenceTheorem`, `RepresentationAssociationReflexivityTheorem`,
`RepresentationAssociationSymmetryTheorem` and
`RepresentationAssociationTransitivityTheorem`. The proof keeps the full
quantification: an arbitrary field in universe `uF`, every natural rank
including zero, all block shapes, and complex representations whose carriers lie
in the independent universes `uV`, `uW` and `uX`. It imports the statement
module and `MinimalConjugatingCosetsProof`, reusing the latter's public
composition and inverse helpers. The statement pair is unchanged. The
four conjuncts are proved separately as `leviAssociationEquivalence`,
`representationAssociationReflexivity`, `representationAssociationSymmetry` and
`representationAssociationTransitivity`.

## Implemented proof

**Conjugation of subgroups.** `conj_mul_toMonoidHom` states that conjugation by
a product `p * q` of invertible matrices is the composite of conjugation by
`q` followed by conjugation by `p`. `map_conj_one` states that conjugation by
the identity matrix maps every subgroup onto itself. `GeneralLinear.permutation`
is a monoid homomorphism. Hence `permutation n F 1 = 1`,
`permutation n F (v * w) = permutation n F v * permutation n F w`, and
`permutation n F w⁻¹ = (permutation n F w)⁻¹`.

**Levi association (`LevisAssociated`).** The witnesses are actual
permutations.

- `conjugatesLevi_one`: the identity permutation conjugates every Levi
  subgroup onto itself, by `map_conj_one`.
- `conjugatesLevi_inv`: if `w` conjugates the embedded Levi of `B` onto that of
  `C`, then `w⁻¹` conjugates `C` back onto `B`. The imported proof uses
  subgroup extensionality and `Subgroup.mem_map_equiv`, reduces the inverse
  permutation matrix with `map_inv`, and applies the membership equivalence
  for conjugation by `w`.
- `conjugatesLevi_mul`: if `w` conjugates `B` onto `C` and `v` conjugates `C`
  onto `D`, then `v * w` conjugates `B` onto `D`. The imported proof uses
  `map_mul` and the subgroup identity `map_conj_mul`, then substitutes the
  two given Levi-conjugation equalities.

These three lemmas give reflexivity, symmetry and transitivity of
`LevisAssociated`.

**Induced Levi equivalences.** Each identity below is checked after applying
the injective block-diagonal embedding `leviEmbedding_injective` of the target
Levi. The published lemmas `leviConjugation_embedding` and
`leviConjugation_symm_embedding` then reduce it to an identity of matrices.

- `leviConjugation_one`: `leviConjugation B B 1 h` is the identity
  `MulEquiv.refl`. This holds because conjugation by the identity matrix is
  trivial.
- `leviConjugation_inv_symm`: the inverse of `leviConjugation C B w⁻¹ h` is
  `leviConjugation B C w hw`. After `map_inv` and `inv_inv`, both sides are
  `permutation w * m * (permutation w)⁻¹`.
- `leviConjugation_mul`: `leviConjugation B D (v * w) h` is the composite
  `(leviConjugation B C w hw).trans (leviConjugation C D v hv)`. The two sides
  agree by `map_mul`, `mul_inv_rev` and associativity.

**Representation association (`RepresentationsAssociated`).** Each witness is an
actual `Representation.Equiv`. It is built with `Representation.Equiv.mk` from a
linear equivalence, and the intertwining identity is checked pointwise.

- Reflexivity uses the permutation `1` and the identity linear equivalence. The
  transported action `ρ ((leviConjugation B B 1 h).symm m)` is `ρ m` by
  `leviConjugation_one`.
- Symmetry starts from `w`, `hw` and an equivalence
  `e : (transport B C w hw ρ).Equiv σ`. It uses the permutation `w⁻¹` and the
  inverse linear equivalence of `e`. By `leviConjugation_inv_symm`, the action
  of `m` on the transported `σ` is `σ (leviConjugation B C w hw m)`. The
  intertwining property of `e.symm` turns this into
  `ρ ((leviConjugation B C w hw).symm (leviConjugation B C w hw m))`, which
  equals `ρ m`.
- Transitivity starts from `e₁ : (transport B C w hw ρ).Equiv σ` and
  `e₂ : (transport C D v hv σ).Equiv τ`. It uses the permutation `v * w` and the
  composite linear equivalence `e₁` then `e₂`. By `leviConjugation_mul` and
  `MulEquiv.symm_trans_apply`, the transported action of `m` is
  `ρ ((leviConjugation B C w hw).symm ((leviConjugation C D v hv).symm m))`.
  The intertwining property of `e₁` at `(leviConjugation C D v hv).symm m`
  and then that of `e₂` at `m` give the required identity.

## Provenance and scope

This internal algebraic proof uses only the published definitions in
`CuspidalSupport.LeviDefinitions` (`ConjugatesLevi`, `leviConjugation`,
`transport`, `LevisAssociated`, `RepresentationsAssociated`), the group
homomorphism `GeneralLinear.permutation`, injectivity of the Levi embedding, and
Mathlib's `Representation.Equiv` API. It cites no literature result. It adds no
hypotheses: there is no topology, smoothness, admissibility, irreducibility,
cuspidality or finite-dimensionality assumption. The checked axioms are
`propext`, `Classical.choice` and `Quot.sound`. The proof says nothing about
parabolic induction, Jacquet modules or the parent cuspidal-induction
association theorem.

The composition and inverse helpers `conjugatesLevi_mul` and
`conjugatesLevi_inv` are imported from `MinimalConjugatingCosetsProof`
(Worker 165); their statements coincide with the helpers used here.
