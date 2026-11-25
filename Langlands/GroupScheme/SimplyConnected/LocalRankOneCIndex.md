# The complete local rank-one type-C index alternative

This internal module proves the complete type-C alternative in
the published actual-index enumeration `LocalRankOneTitsIndexStatement`. Let `G` be a simply connected,
absolutely almost-simple group over any nonarchimedean local field `K`,
with split rank one. Let `d` be its actual `TitsIndexData`, and suppose a
numbering `e : d.Vertex ≃ Fin n` identifies every Cartan entry with
`CartanMatrix.C n`, where `n ≥ 2`.

`localRankOneTypeC_index` proves `d.HasRankOneCIndex n`: the absolute rank
is two or three, the distinguished vertices are exactly those numbered
two in one-based notation, and every element of the full absolute Galois
group fixes every vertex. The proof retains every field and residue
characteristic, including two, and an arbitrary universe for `K`.

## Implemented proof

`localRankOneTypeC_presentation_and_marking` supplies an actual central
division algebra of dimension four over `K`, an actual first-kind
involution whose symmetric subspace has dimension three, and an
invertible trace-valued antihermitian form in `n` variables of Witt index
one. The presentation includes a group-scheme isomorphism from `G` to
the form's quaternionic symplectic group. The same theorem supplies the
exact marking under the original numbering `e` and the trivial full star
action.

Apply `card_le_three_of_wittIndex_one` to that form. Its all-characteristic
scalar quadratic-form argument gives `n ≤ 3`. Together with the hypothesis
`2 ≤ n`, this gives `n = 2 ∨ n = 3`. These facts, the supplied exact
marking and the full star action are precisely the three conjuncts of
`HasRankOneCIndex`.

## The chosen small presentation

`nonempty_localRankOneTypeCSmallPresentation` combines this rank conclusion
with the actual presentation in `n` variables. Replacing `n` by two or
three places the presentation in the corresponding summand of
`LocalRankOneTypeCPresentation K G 2 ⊕
LocalRankOneTypeCPresentation K G 3`.

`localRankOneTypeCSmallPresentation` chooses an element of that sum. Each
summand retains the actual division algebra, involution, form, Witt index
and group-scheme isomorphism; the result is presentation data, not merely
a type label.

## Provenance and scope

This is an internal composition of the type-C presentation and marking
theorem with the local quaternionic dimension bound. It introduces no
additional local arithmetic or classification premise. Those inputs
derive from the division-form theorem, elementary form theory, the
reduced-degree bound and the all-characteristic local quadratic dimension
bound, independently of the downstream local group classification and
Kneser--Tits.

The theorem assumes an actual type-C Cartan numbering. It completes that
alternative of the enumeration; it does not establish that an arbitrary
rank-one group is of type C or prove the other alternatives of
`LocalRankOneTitsIndexStatement`.
