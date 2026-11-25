# Laws of algebraic dual maps: implemented proof

The closing theorem `Langlands.algebraicDualLaws` proves the complete
`AlgebraicDualLawsStatement`.
Its checked proposition fingerprint is
`6fb1e449640282657db09d6ddbd0de310d89650b9ac89c60e9fb1e19f6c3083b`.

The pullback, equivalence, and evaluation formulas are definitional equalities.
The identity, composition, and bidual-naturality equations follow by intertwiner
and linear-map extensionality: after application to a functional and a vector,
both sides are the same expression. Composition reverses because functionals
are precomposed with the original maps.

The reusable lemmas are `dualIntertwining_apply`, `dualIntertwining_id`,
`dualIntertwining_comp`, `dualEquiv_apply`, `bidualIntertwining_apply`, and
`bidualIntertwining_natural`. The closing theorem packages them in the order of
the target's six clauses, retaining all five independent universes.

Only the target and its underlying definition pair are imported. The closing
proof uses exactly the ring, group, and module hypotheses of the target.
No reflexivity or finite-dimensionality theorem is used.

The source context is Casselman Chapter II, Section 3, page 6, recorded under
`casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
See [the target](LawsStatement.md) and [definitions](Definitions.md).

The sole project definition dependency is the `Dual.Definitions` pair.
The pinned environment is
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The complete closing theorem has been checked against the whole proposition
without additional ambient assumptions. Its axiom closure contains only
`propext` and `Quot.sound`.
