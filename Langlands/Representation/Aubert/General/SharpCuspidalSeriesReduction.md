# Cuspidal-series retention from irreducibility and support retention

Implementation and documentation: Worker 1513 (task
`6316db5a-5618-43bb-a920-eadd3a912b88`).

This module reduces the cuspidal-series retention target for the actual
terminal cokernel `E#` to four inputs. Two are the irreducibility target and the
support-retention target. The other two are named here as propositions about
the association relation: reflexivity at the identity, and transport of
irreducible inside-Levi cuspidal representations along the association. The
module asserts no target and imports no proof of any of these inputs. All four
are explicit hypotheses of the reduction.

## Reflexivity of the subquotient relation (`Langlands.SmoothRep`)

`isSubquotient_self A`: every smooth representation `A` (over any commutative
ring, of any topological group, at any universes) is a subquotient of itself.
The proof applies the Library's `SmoothRep.isSubquotient_iff_exists` to the
identity intertwiner `𝟙 A`, used both as the injection and as the surjection.
`SmoothRep.hom_id` identifies its underlying map with the identity.

## The association interfaces (`Langlands.Aubert.General`)

* `AssociationReflexive IsAssociate : Prop` is `∀ I, IsAssociate I I 1`: every
  index set is associated to itself by the identity. Here
  `IsAssociate : Finset ι → Finset ι → G → Prop` is any relation on index sets
  with a representative in a group `G`.
* `AssociationCuspidalTransport.{uI, uG, uW} P M U hclosed hM hL IsAssociate :
  Prop` says the following. Take index sets `I` and `J`, an element `n : G` and
  a proof `hn : ∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`, so that `M J = n (M I) n⁻¹`,
  with `IsAssociate I J n`. Take a representation `σ` of `M I` with carrier in
  `Type uW` that is irreducible and cuspidal inside `M I`
  (`IsLeviCuspidal … I (hM I) (hL I) σ`). Then the conjugate
  `(conjugationFunctor n hn).obj σ`, a representation of `M J`, is irreducible
  and cuspidal inside `M J` (`IsLeviCuspidal … J (hM J) (hL J)`). The families
  and hypotheses `P M U hclosed hM hL` are those of the generic standard
  families. The definition uses the Library's `conjugationFunctor` and
  `IsLeviCuspidal` unchanged.

## The reduction

`sharpCuspidalSeries_of_irreducible_supportRetention hirr hret hrefl htrans`
proves `SharpCuspidalSeriesTarget P M U h hclosed hδ hP hU hM hL IsAssociate` at
universes `uI, uG, uV` from the following hypotheses:

* `hirr : SharpIrreducibleTarget P M U h hclosed hδ hP hU hM hL` at the same
  universes. For `E ∈ 𝔈(I)`, `E#` is irreducible.
* `hret : SharpSupportRetentionTarget P M U h hclosed hδ hP hU hM hL IsAssociate`
  at the same universes. `E ∈ Alg({I})` implies `E# ∈ Alg({I})`.
* `hrefl : AssociationReflexive IsAssociate`.
* `htrans : AssociationCuspidalTransport.{uI, uG, max uG (max uI uV)} P M U
  hclosed hM hL IsAssociate`. The carrier universe `Type (max uG uI uV)` is
  that of the representations of the Levis in the target.

Proof. Let `E ∈ 𝔈(I)`.

1. By `hirr`, `E#` is irreducible.
2. By the Library's `IsInCuspidalSeries.isInSupportCategory` with `hrefl I`,
   `E ∈ Alg({I})`. By `hret`, `E# ∈ Alg({I})`.
3. Apply the definition of `IsInSupportCategory` to the irreducible
   subquotient `E#` of `E#` (by `isSubquotient_self`). This yields `J`, `n`, a
   proof `hn` of `M J = n (M I) n⁻¹` (as the membership equivalence),
   `IsAssociate I J n`, and an irreducible inside-Levi cuspidal `σ` of `M I`.
   `E#` is a subquotient of the normalized induction
   `i^G_{L_J}((conjugationFunctor n hn).obj σ)`.
4. By `htrans`, the conjugate `(conjugationFunctor n hn).obj σ` is an
   irreducible inside-Levi cuspidal representation of `M J`.
5. The witness of the target is `I' := J` and `n`. The association is
   `IsAssociate I J n` and the Levi equivalence is `hn`. The membership
   `E# ∈ 𝔈(J)` comes from step 1, the conjugate datum of step 4, and the
   subquotient relation of step 3.

No finite-length, admissibility or finite-generation hypothesis is used. The
reduction uses no classification, character-independence, geometric-lemma or
adjointness result.

## Provenance

The statement reduced here is the derived obligation of the proof of Aubert's
Corollaire 3.9 (c) (Aubert 1995, printed p.2189). That proof applies `#` a second
time to `E#`, which needs `E#` in the cuspidal series of a standard Levi
associated to `L_I`. The support category `Alg({I})` and the terminal cokernel
`E#` are those of the 1996 erratum (printed pp.4687 and 4690). The argument here
is the standard one: an irreducible member of `Alg({I})` is its own irreducible
subquotient, so its support datum is a cuspidal-series datum for the associated
Levi once the conjugate cuspidal datum is known to be irreducible and cuspidal.
`AssociationReflexive` and `AssociationCuspidalTransport` are internal
interfaces. They isolate the structural properties of the association used for
this, to be discharged for the actual rational root association.
