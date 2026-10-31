# Pointed pullback of the original-index tower of a Harris polarized action

This internal specialization connects the actual pointed
`framedPositiveActionBaseChange` object with the existing natural
pullback on compact-open Weil level towers. All arithmetic data,
schemes and the point field have universe zero.

`level_nonempty_adelicFrame` starts with an actual level at an
original Harris compact-open index `U` for a given positive
polarized action `X`. That level is an actual monodromy-fixed
right orbit of compatible frames at the point `t ≫ b`. The proof
extracts a quotient representative and forgets its form condition
to obtain `Nonempty` of the actual ambient adelic frame type.
It does not assert that the representative is fixed by monodromy.
Thus existence of an already given level supplies exactly the
frame-existence input used in the pointed faithfulness argument.

`framedPositiveActionTowerBaseChange` fixes one such frame-existence
proof and the displayed actual changed-dual construction data.
Its target polarized action is precisely the constructed
`framedPositiveActionBaseChange`, not a supplied action object.
It takes the two exact named integral-dual-naturality and full
polarization-stability inputs needed by that constructor.

The source and target are the actual compatible-level towers of
`X` and that constructed changed object, each reindexed by
`hodgeLevelFunctor D C`. Consequently their indices are the
original Harris compact-open transporter category, with its
original finite-adelic group. The actual rational action and
integral polarization used in the target tower are exactly the
composed rational action and canonical dual-valued pullback used
in the generic Tate comparison.

The implementation applies `Functor.whiskerLeft` to the existing
`Tate.weilAdelicCompactOpenLevelBaseChange`. Its components are
the already constructed actual fixed-orbit pullbacks at
`(hodgeLevelFunctor D C).obj U`. Naturality for every original
transporter arrow follows from that natural transformation's
proved naturality and the reindexing functor laws. This includes
the original subgroup inclusions and both original Hecke arrows.
No new generic Tate or frame comparison is introduced.

The bases are quasi-separated. Finite-fibre hypotheses for the
actual finite-etale fibre functors at `t` and `t ≫ b`, torsion
finite-etaleness, invertibility of all positive torsion orders,
and finite-etaleness of the corresponding roots of unity at
both bases remain explicit. The finite Weil transition,
tensor/Picard, square, universal-family and rational finite-adele
comparison inputs also remain explicit. These are the actual
inputs of the imported constructions.

Worker 57 constructs this specialization from the published
generic tower map and the concretely constructed Harris object.
It proves neither existence of a level or changed-dual data nor
the two named theorem inputs. It does not descend the map to
polarized rational-isogeny classes, identify successive-base
polarized objects, construct an unpointed moduli functor, prove
representability or supply scheme levels.
