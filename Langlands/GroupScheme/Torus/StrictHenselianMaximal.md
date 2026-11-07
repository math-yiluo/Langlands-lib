# Split maximal tori over strictly Henselian local rings: the proof

This module proves the Library proposition
`Langlands.GroupScheme.StrictHenselianSplitMaximalTorusStatement.{u}`, from
`Langlands.GroupScheme.Torus.StrictHenselianMaximalStatement`, for every
universe `u`, with no extra hypotheses.

## Main statement

`strictHenselianSplitMaximalTorus : StrictHenselianSplitMaximalTorusStatement.{u}`.

Let `R : Type u` be a commutative Henselian local ring whose residue field
`IsLocalRing.ResidueField R` is separably closed, and let `G` be a reductive
group scheme over `Spec R`. Then there is a commutative group scheme `T` over
`Spec R` and an actual homomorphism `i : T.toGrp ⟶ G` such that `T` is a split
torus, `i` is a closed subgroup, and for every point `s` of `Spec R` the pullback
of `i` along `Spec κ(s) → Spec R` satisfies `IsMaximalTorus`. The theorem
claims exactly this proposition, unchanged.

## Proof

The proof applies three published Library theorems and adds no new argument:

1. `strictHenselianSplitMaximalTorusReduction`
   (`Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction`) proves
   `StrictHenselianSplitMaximalTorusReductionStatement.{u}`. That proposition says
   that `RelativeSplitTorusLiftingStatement.{u}` and the pointed Henselian
   étale-section property together imply the target.
2. `relativeSplitTorusLifting`
   (`Langlands.GroupScheme.Torus.RelativeLiftingProof`) proves
   `RelativeSplitTorusLiftingStatement.{u}`. It is the first argument.
3. `Langlands.CommutativeAlgebra.HenselianSections.henselianEtaleSection`
   (`Langlands.CommutativeAlgebra.HenselianSections`) proves
   `HenselianEtaleSectionStatement.{u}`. That proposition is the same as the
   inline section hypothesis of the reduction: for a Henselian local `R`, an
   étale `p : U ⟶ Spec R` and a point
   `b : Spec ((Spec R).residueField (closedPoint R)) ⟶ U` over the closed point,
   there is a section `σ` of `p` with `fromSpecResidueField (closedPoint R) ≫ σ = b`.
   It is the second argument. Lean accepts it without any conversion.

The reduction's own proof works as follows. It finds a split maximal torus on the
separably closed closed fibre. It lifts that torus to an étale neighbourhood with
a point over the closed point, descends it to `Spec R` along a Henselian section,
and then spreads maximality from the closed fibre to every residue fibre
(`localClosedFibreMaximalPropagation`). The reduction module's Markdown describes
these steps in detail.

## Provenance

This is internal derived infrastructure. It only composes Library results, so it
adds no external mathematical assertion. Conrad, *Reductive group schemes*
(2014), gets the same conclusion through the scheme of maximal tori (Theorem
3.2.6, Corollary 3.2.7) and the splitting of multiplicative-type groups over
strictly Henselian bases (Proposition B.3.4). The statement's Markdown records
those citations. The Lean route never builds the scheme of maximal tori. It uses
residue-fibre torus lifting, Henselian sections and closed-fibre maximality
propagation instead.
