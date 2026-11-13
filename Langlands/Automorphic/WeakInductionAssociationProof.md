# Weak automorphic induction gives weak association with the induced Weil representation

Lean module: `Langlands.Automorphic.WeakInductionAssociationProof`
(namespace `Langlands.ClassField.Global.RelativeWeilGroup`).

Author: Worker 5130. This is the proof for task `f096b984-dff5-4425-861f-8f298e5896fb`.

## Statement

`weakInductionAssociation : WeakInductionAssociationStatement.{u, uV, uP}` proves the
published proposition
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement`
(module `Langlands.Automorphic.WeakInductionAssociationStatement`) exactly. All three
universes stay free and there is no added hypothesis; in particular neither `ξ` nor `π`
is assumed unitary.

The statement covers every arithmetic class family `c` with
`FundamentalClass.Restriction c`, every tower `F ⊆ E' ⊆ L` of number fields with `L / F`
Galois (and `AdeleQuotient F` compact), every cuspidal class `π` of `GL_r(𝔸_F)` and every
Hecke character `ξ` of `E'`. If `π` is a weak automorphic induction of `ξ`, then `π` is
weakly associated with `inducedReciprocityRepresentation c F E' L h ξ`, that is,
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` (Henniart (2000), §3.4, with Harris (1998),
Definition 1.3(b)).

## Proof

The proof applies one published theorem to three published theorems:

```
weakInductionAssociation_reduction
  LocalClassField.geometricWeilReciprocityExistenceUniqueness.{u}
  localRelativeWeilMapExistence.{u}
  localInducedRestriction.{uV, u}
```

- `weakInductionAssociation_reduction` (module
  `Langlands.Automorphic.WeakInductionAssociationReduction`, by the same author) proves
  `WeakInductionAssociationReductionStatement.{u, uV, uP}`. This is the implication
  `WeilReciprocityExistenceUniqueness.{u} → LocalRelativeWeilMapExistenceStatement.{u} →
  LocalInducedRestrictionStatement.{uV, u} → WeakInductionAssociationStatement.{u, uV, uP}`.
  Its paired Markdown describes the argument in full. In outline, write
  `S = inducedReciprocityRepresentation c F E' L h ξ`. The reduction works at the
  cofinitely many finite places `v` of `F` allowed by the weak induction hypothesis. There
  every place `u` of `E'` above `v` has ramification index `1`, `ξ` is unramified at `u`,
  and the Euler polynomial of `π` at `v` is
  `inducedEulerPolynomial ξ v ϖ = ∏_{u | v} (1 - ξ_u(ϖ_u) X^{f(u|v)})`.
  At each place `w` of `L` above `v`, the first antecedent gives a geometric reciprocity
  candidate `e` of `L_w`. The second antecedent then gives a local map
  `ι : W_{F_v} → W_{L/F}` with `IsLocalRelativeWeilMap v w e ι`. For any such `ι`, the
  third antecedent at `K = E'` writes the restriction of `S` along `ι` as a sum over `u`
  of representations induced from characters. Applying the L-factor homomorphism shows
  that the Euler polynomial of `S ∘ ι` on inertia invariants is that same product. The
  product has degree `Σ_u f(u|v) = [E' : F] = rank S`. So inertia acts trivially on
  `S ∘ ι`, and the local Euler polynomial of `S` along `ι` equals the Euler polynomial of
  `π` at `v`.
- `LocalClassField.geometricWeilReciprocityExistenceUniqueness` (module
  `Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof`) proves
  `WeilReciprocityExistenceUniqueness.{u}`: every p-adic field, with any of its
  topological realizations, has a unique geometrically normalized Weil reciprocity
  candidate.
- `localRelativeWeilMapExistence` (module
  `Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof`) proves
  `LocalRelativeWeilMapExistenceStatement.{u}`. For arithmetic class families, every
  geometric candidate of `L_w` has a local map `ι : W_{F_v} → W_{L/F}` with
  `IsLocalRelativeWeilMap v w e ι`.
- `localInducedRestriction` (module
  `Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof`) proves
  `LocalInducedRestrictionStatement.{uV, u}`. This is the local restriction formula for
  representations induced from `W_{L/E'}`, with local maps whose transfer is inverse
  geometric local reciprocity (Tate (1979), (2.3.5) with (1.6.1)).

None of these inputs uses a local Langlands result, so the argument is not circular.
`lean_check` reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. This contribution leaves the target pair and every pair it imports
unchanged.
