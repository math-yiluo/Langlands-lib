# Proof of the associated central character statement

Authors: Worker 5151, with Worker 5137 (automorphic half).

The theorem
`Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter :
AssociatedCentralCharacterStatement.{u, uV, uP}` proves the published statement
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement`
(module `Langlands.Automorphic.AssociatedCentralCharacterStatement`), unchanged and at
arbitrary universes `u`, `uV`, `uP`. It uses no hypotheses beyond those of the statement
and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

At an arithmetic class family `c`, let `S` be a finite-dimensional complex representation of
`W_{E/F}` and let `T` be an actual irreducible cuspidal realization of `GL_{r+1}` over `F`.
If `S` is weakly associated with the cuspidal class of `T`, the theorem gives a Hecke
character `ω` with the following properties: `ω` is a central character of `T`,
`det S = ω ∘ τ_F`, every central character of `T` equals `ω`, and every Hecke character `χ`
with `det S = χ ∘ τ_F` equals `ω`. This is Henniart (2000), §2.2, `det S = ω_Π ∘ τ_F`.

## The implemented proof

Fix `c`, `F`, `E`, `r`, `S` and `T` with `IsWeaklyAssociatedClass S T.isoClass`.

1. **A presentation.** The published `isWeaklyAssociatedClass_isoClass_iff` gives a
   cuspidal spectral presentation `P` of `T` in universe `uP` with
   `IsWeaklyAssociated S P.spectralSystem`. In particular `S` is continuous.
2. **The Hecke character of `det S`.**
   `existsUnique_determinantCharacter_eq_reciprocityCharacter` (module
   `AssociatedCentralCharacter.DeterminantDescent`) gives a Hecke character `δ` with
   `det S = reciprocityCharacter c F E δ`, and shows that every `χ` with
   `det S = reciprocityCharacter c F E χ` equals `δ`. This gives clauses 2 and 4.
3. **Good places.** `eventually_finiteUniformizerValue_eq_elementaryCoefficient` (module
   `AssociatedCentralCharacter.GoodPlaces`) shows that at cofinitely many finite places
   `v`, `δ` is unramified at `v`, `v` is not exceptional for `P`, and
   `δ_v(ϖ_v) = elementaryCoefficient (P.spectralSystem.eigenvalues v hs) (r + 1)`.
4. **Central character.** Worker 5137's
   `Langlands.Automorphic.CuspidalOperatorRealization.hasCentralCharacter_of_eventually_elementaryCoefficient`
   (module `Langlands.Automorphic.CentralCharacterTopCoefficient`) turns step 3 into
   `T.HasCentralCharacter δ`. This gives clause 1.
5. **Uniqueness of the central character.**
   `CuspidalOperatorRealization.hasCentralCharacter_unique` (module
   `AssociatedCentralCharacter.CentralCharacterUniqueness`) shows that any `ω'` with
   `T.HasCentralCharacter ω'` equals `δ`. This gives clause 3.

The witness is `ω := δ`.

## Relation to the argument in the statement's Markdown

The statement's Markdown sketches an eight-step argument. This proof takes a different
route for steps 1, 6, 7 and 8:

- It never proves that `T` has some central character in advance (step 1, Schur–Dixmier),
  and it does not use the rigidity statement `HeckeLocalComponentRigidityStatement`
  (step 8). The central character is built directly as the Hecke character `δ` of `det S`.
  At each good place `v`, irreducibility of the local action makes the scalar matrices of
  `F_v^×` act on all of `T` by `δ_v`. The ideles whose scalar matrices act by `δ` form a
  closed subgroup that contains the principal ideles, so weak approximation
  (`Langlands.Global.IdeleDensity.eq_top_of_isClosed`, module
  `Langlands.Global.IdeleClosedSubgroupDensity`) shows that it is everything.
- For local–global compatibility at good places (step 6), the proof uses the published
  `RelativeWeilGroup.reciprocityCharacter_eq_finiteUniformizerValue` (module
  `Langlands.ClassField.Global.RelativeWeilUnramifiedTwist`). This holds at places all of
  whose places above in `E` have ramification index one, split or not. Cofinitely many
  places of `F` have this property.
- The identity `det S(ι Fr) = z_1 ⋯ z_n` (step 4) is in
  `AssociatedCentralCharacter.EulerTopCoefficient` and `GoodPlaces`. The action of the top
  Hecke operator (step 5) is in `Langlands.Representation.Unramified.TopHeckeOperator` and
  `CentralCharacterTopCoefficient`.

## Modules of this proof, in dependency order

Worker 5151:

- `Langlands.Automorphic.AssociatedCentralCharacter.DeterminantDescent`: continuous
  descent of `det S` through the transfer, and injectivity of
  `χ ↦ reciprocityCharacter c F E χ`. Uses the published `relativeWeilTransferReciprocity`,
  `transferCharacterFactorization` and `FiniteRepresentation.continuous_determinantCharacter`.
- `Langlands.Automorphic.AssociatedCentralCharacter.EulerTopCoefficient`: the top
  coefficient of `det(1 - X A)` is `(-1)^n det A`, so an unramified match gives
  `det S(ι Fr) = ∏ z_i`.
- `Langlands.Automorphic.AssociatedCentralCharacter.GoodPlaces`: step 3 above.
- `Langlands.Automorphic.AssociatedCentralCharacter.CentralCharacterUniqueness`: step 5
  above, from `space_nontrivial` and the injectivity of the inclusion of forms.

Worker 5137 (copied verbatim from their draft revision 1 of Task 5210):

- `Langlands.Representation.Unramified.TopHeckeOperator`: the top standard Hecke operator
  is the scalar diagonal `ϖ_v · 1` and acts by the top elementary coefficient.
- `Langlands.Global.IdeleClosedSubgroupDensity`: a closed subgroup of the ideles that
  contains the principal ideles and `F_v^×` for cofinitely many finite `v` is everything.
- `Langlands.Automorphic.OperatorScalarCentralCharacter`: the subgroup of ideles whose
  scalar matrices act by `δ`, and its local membership criteria.
- `Langlands.Automorphic.CentralCharacterTopCoefficient`: step 4 above.

Each module's Markdown describes its own lemmas.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), 439–455, §2.2, printed p.444 (literature ID
  `henniart-2000-simple-proof`).
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part 2 (1979),
  §1.2 and §2 opening (literature ID `tate-1979-number-theoretic-background`).
