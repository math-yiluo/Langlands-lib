# Profinite quotients of actual idele classes by positive powers

Authors: Worker 53 and Worker 1232.

`Langlands.Global.IdeleClassPowerQuotientProfiniteStatement.{u}` states that
for every number field `K : Type u` and every positive natural number `m`,
the group
`IdeleClasses K ⧸ (powMonoidHom m : IdeleClasses K →* IdeleClasses K).range`
is Hausdorff, compact and totally disconnected. Its topology is the actual
quotient topology inherited from the Library's actual idele-class quotient,
which is itself the quotient of actual ideles by principal ideles. No
alternative topology, abstract class-field-theory model or chosen reciprocity
map appears. The field universe is unrestricted. The power subgroup consists
of all `m`th powers; commutativity makes it normal.

The source is Artin and Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Chapter X, Section 2, Lemmas 3, 5 and 6 and their proofs, printed pp.77–79
(one-based PDF pp.86–88), together with the closedness of `C^m` used in Lemma 3.
The registered source is `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata at one-based PDF p.202 contain no correction to these
passages. Both authors read these passages in preparing the prescription proof.

This is a derived packaging of those topological facts. Closedness of `C^m`
makes the quotient Hausdorff. Lemma 5 proves its compactness. Lemma 6 gives
arbitrarily small open finite-index subgroups containing `C^m`; their images
in the quotient supply a separating open-subgroup neighborhood basis and hence
total disconnectedness. The word profinite in the declaration name means
precisely these three topological properties; no specific inverse-limit
presentation is part of the statement.

The Lean file defines a proposition only, with the three properties as
conjuncts. It does not prove them, install them as instances or replace them by
assumptions in the final character-prescription target. The intended consumer
combines this topology with the finite image of a local product modulo powers
to separate the required finite subgroup. That consumer does not require a
comparison between the local product topology and the topology induced on its
image in idele classes. Worker 1232 proposed this smaller consumer interface
during the arithmetic prerequisite audit.
