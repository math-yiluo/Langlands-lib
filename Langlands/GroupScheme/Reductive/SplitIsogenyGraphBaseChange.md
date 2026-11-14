# Local-isogeny graphs under field extension

This module is derived support for the split isogeny construction. It uses the
published actual graph pullback, simple-root transport and fpqc reflection
interfaces from `SplitLeviGluingGraphBaseChange`,
`SplitLeviGluingSimpleGraphBaseChange` and `IsogenyStability`. Its new input is
the two-torus local-isogeny graph, whose target maps may be inseparable.

## Scope and constructions

Let `k : Type u` and `K : Type u` be fields with a `k`-algebra structure.
Write `B` for group-scheme pullback along `Spec K → Spec k`, and `C` for
commutative-group-scheme pullback. The field and group schemes retain the
arbitrary universe `u`; the auxiliary indexing universe is unrestricted.

`GraphEnvelope.congrTorusMaps` replaces the two torus maps by equal maps. It
retains the supplied graph group, inclusion and geometric properties. Its
generation proof transports the torus generator and leaves local generators
unchanged. It introduces no additional existence premise.

`LocalIsogeny.baseChange` pulls back both actual local groups, their closed
centralizer inclusions, their torus factorizations and the local isogeny.
The cocharacters are the actual base-changed cocharacters. The centralizer
representation statements follow from the published base-change theorem;
the local homomorphism remains an isogeny by base-change stability, including
its full scheme kernel.

For `D : SimpleIsogenyGraph i i' t`, the ambient source and target groups are
smooth and affine, and the source is connected. The record already supplies
the split source torus. `D.baseChangeComparisons K` pulls back the local
isogenies and indexes them by the actual simple roots of the extended source
torus. `D.baseChange K`, the entry construction, makes the resulting
`SimpleIsogenyGraph (B.map i) (B.map i') (C.map t)`.
Its target directions are the pulled-back original target directions, indexed
by the same source-simple-root equivalence.

## Preservation and descent

The constructed envelope is the actual pullback of `D.envelope`, followed
by reindexing and replacement of equal generator maps. In particular its
group is the actual pulled-back graph group. Functorial composition supplies
the second torus map and second local maps. The target-direction equation
uses naturality of cocharacter transport.

`baseChange_first` and `baseChange_second` identify its two projections with
`B.map D.envelope.first` and `B.map D.envelope.second` exactly.
`baseChange_torusLift` identifies its distinguished torus lift with
`B.map D.envelope.torusLift`; the two projection squares and joint faithfulness
of the envelope prove this identity.

`isIso_first_of_baseChange` descends invertibility of this first projection
along the field extension. The pullback identity gives invertibility of the
actual pulled-back homomorphism; the field-extension fpqc theorem and the
published reflection theorem then give `IsIso D.envelope.first`.

These results transport the supplied graph and its local data. They do not
supply root-datum transport or establish first-projection invertibility over
the extended field. Those inputs remain separate in the intended descent
application.
