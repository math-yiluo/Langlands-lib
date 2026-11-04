# Connectedness of torus centralizers and Cartan subgroups

This derived module proves connectedness for every actual representative of
the all-test centralizer of a torus homomorphism into a smooth connected affine
group scheme over an arbitrary field. The torus homomorphism need not be closed,
maximal or split. The field has arbitrary universe and characteristic. Neither
reductivity nor perfection is assumed.

For a split torus, the published `centralizingCocharacter` construction supplies
an actual cocharacter whose dynamic centralizer equals the whole-torus
centralizer on all test schemes. `splitTorusCentralizerDynamicIso` is the unique
represented-subgroup comparison from a given centralizer representative to the
chosen dynamic centralizer representative. Its inclusion compatibility follows
from the represented-subgroup isomorphism theorem. The published dynamic
centralizer connectedness theorem then applies to the given representative
after rewriting by the all-test centralizer equality. The cocharacter equality
requires only affine local finite type, and does not use the reductive-only
generic centralizer statement.

For an arbitrary torus, choose a splitting field extension supplied by the
actual torus predicate. Smoothness and affineness of the ambient group persist
under base change. Its connectedness persists by the existing geometric
connectedness theorem for finite-type connected group schemes. The existing
all-test torus-centralizer base-change theorem transports the representation to
the split extension. Apply the split connectedness theorem there, then descend
connectedness along the surjective projection from that pullback to the original
representative. Surjectivity follows from the field extension's fpqc property.

Every actual Cartan embedding represents the centralizer of one of its
witnessing maximal tori. Applying the preceding result proves
`IsCartanSubgroup.connectedSpace`. Combining it with the published exact
torus-centralizer smoothness theorem gives `IsCartanSubgroup.smooth_connected`.
Geometric nilpotence of Cartans and full Cartan generation remain open.

All constructions and proofs are internal consequences of the named Library
results. No additional original-source assertion is introduced as a premise.
