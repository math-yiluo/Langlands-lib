# Filtration by the full geometric pieces of a supercuspidal induction

This internal assembly takes a supplied family of actual geometric-lemma
intersection data and a supplied gluing of the actual normalized composite
`leviJacquetInductionFunctor`. It constructs neither input and does not prove
the final VI.5.3(iii) proposition.

## Preliminary lemmas

For a datum whose two intersection parabolics `p'` and `q'` are full,
`fullLeviConjugacy_inv` inverts the published conjugacy equation of
`fullLeviConjugacy`. The inverse isomorphism `L ≅ M` satisfies
`ε⁻¹ ≫ l ≫ p = lQ ≫ q ≫ inner(z)`, which is the orientation of the
representative `z` used for the conjugates of the inducing representation.
`fullLeviPointsEquiv_symm_apply` shows that the inverse of the continuous point
equivalence `fullLeviPointsEquiv` is the point map of this inverse scheme
isomorphism, not an unrelated isomorphism of abstract point groups.
`nonempty_representationEquiv_trans` composes two nonempty equivalences of
representations.

## Data and construction

`FullPieceFiltrationData z D ρ` records:

* an actual filtration of the composite applied to `ρ`, with `length` grades;
* a bijection between its grades and *every* index `i` whose source
  intersection parabolic `(D i).p'` is full;
* for each grade, a scheme isomorphism `L ≅ M` satisfying the ambient
  conjugacy equation with the representative of the enumerated index;
* the continuous point equivalence of each such isomorphism, equal pointwise
  to its point map;
* equivariant identifications of every grade with the pullback of `ρ` along
  that point equivalence.

`nonempty_fullPieceFiltrationData` proves that such data exist when `ρ` is
supercuspidal in the all-proper-actual-parabolics sense and the outer Levis
admit some isomorphism `M ≅ L`. The supercuspidality condition annihilates the
Jacquet module of every proper source intersection parabolic, hence the
corresponding actual geometric piece (`subsingleton_pieceFunctor_obj`).
`IsGluedFrom.exists_selected_filtration` then evaluates the gluing at `ρ`,
deletes those vanishing factors and enumerates exactly the full
source-intersection indices, retaining every such index even if its factor
is zero. For each retained index, the isomorphism `M ≅ L` makes the target
intersection parabolic full as well (`isIso_q'_of_isIso_p'_of_iso`). Each
selected grade identification is composed with the published actual
full-piece equivalence `fullPieceEquiv`, which identifies the piece with `ρ`
pulled back along the inverse recovered point equivalence. The conjugacies and
point equivalences are the inverses from the preliminary lemmas.

`fullPieceFiltration` chooses such data by `Classical.choice`. The selected
enumeration and filtration are not canonical. The construction is phrased as
an existence theorem followed by a choice so that elaboration of the data
remains tractable; this does not change its content.

Neither irreducibility nor finite length of `ρ` is assumed, and the field and
carrier universes remain independent.

## Provenance and scope

This internal assembly combines existing Library constructions. It is derived
support for Renard 2026, VI.5.3(iii), whose proof filters the composite by the
geometric-lemma pieces and notes that only the pieces with full source
intersection survive on a supercuspidal representation. Three obligations
remain separate: comparing the selected full indices with the double cosets
that contain a Levi-conjugating element, constructing the geometric gluing,
and proving supercuspidality of the final composite.
