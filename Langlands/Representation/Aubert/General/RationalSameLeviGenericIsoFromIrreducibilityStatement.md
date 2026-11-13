# Same-Levi generic isomorphism from generic irreducibility

Author: Worker 5266.

This module states one proposition,
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericInductionIsoFromIrreducibilityStatement.{u, v}`.
It supplies no proof.

## Exact content

The proposition is an implication between two published statements, both at
the same universes `u` (field and group) and `v` (Levi representation
carriers):

`RationalSameLeviGenericInductionIrreducibilityStatement.{u, v} →
  RationalSameLeviGenericInductionIsoStatement.{u, v}`.

Neither side is restated or modified. Both are imported unchanged from the
Library modules
`Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityStatement`
and `Langlands.Representation.Aubert.General.RationalSameLeviGenericIsoStatement`.

1. The premise, `RationalSameLeviGenericInductionIrreducibilityStatement`, is
   generic irreducibility. Take the actual standard rational-point family over a
   nonarchimedean local field of any characteristic: a connected reductive `G`
   with its canonical `pointTopology`, a maximal split torus, a generic
   cocharacter, `StandardCocharacterStatement` and closed literal unipotent
   radicals. Take also simple-root subsets `I`, `J`, a point `g ∈ G(k)`
   conjugating `L_I` to `L_J`, connected reductivity of the Levi scheme of `J`,
   and an irreducible admissible smooth complex representation `σ` of the
   literal Levi `L_J`. For all such data, some nonzero polynomial `p` in the
   coordinates `leviRationalUnramifiedCharacterCoordinates` has the following
   property. For every unramified character `χ` in
   `leviUnramifiedPrincipalOpen i ν J hLJ p`, both the normalized induction
   `i_{P_J}(σ ⊗ χ)` (`normalizedInductionFunctor`) and the induction
   `i_{g P_I g⁻¹}(σ ⊗ χ)` (`conjugateInductionFunctor`) are irreducible.
2. The conclusion, `RationalSameLeviGenericInductionIsoStatement`, has the
   same data. It concludes that some nonzero polynomial `p` in the same
   coordinates has the following property. For every `χ` in its principal open,
   there is an isomorphism of smooth `G(k)`-representations
   `i_{P_J}(σ ⊗ χ) ≅ i_{g P_I g⁻¹}(σ ⊗ χ)` between the same two functors
   applied to the same literal twist `σ.twist χ`.

The premise is quantified over all data. It is the whole published
statement, not an instance at fixed data. The implication adds no hypothesis
to the conclusion.

## Provenance

The statement is derived and internal to this project. It is the intermediate
conditional result named in Task 5266, revision 2. It records the reduction
of the generic isomorphism target to generic irreducibility. The route behind
it is the classical one recorded in the conclusion's own Markdown, through
Waldspurger IV.1 and IV.3: irreducibility of both inductions together with a
nonzero intertwining operator gives an isomorphism by Schur's lemma.

The Library already contains the nonzero-intertwiner half:
`rationalSameLeviGenericNonzeroIntertwiner`, in
`Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerProof`.
It provides a generic nonzero morphism from `i_{P_J}(σ ⊗ χ)` to
`i_{g P_I g⁻¹}(σ ⊗ χ)`. It is therefore not a premise here.

The premise is a published proof target that is not yet proved. Its proof is
owned by Task 5364. The Library reduces it, in
`Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityReduction`,
to Renard VI.8.4 (Task 5147) and to the existence of an irreducible induced
unramified twist (Konno, Theorem 4.2).

This is a proof target, not a theorem. Proving it does not prove the
generic isomorphism target. That target still needs a proof of the premise.
