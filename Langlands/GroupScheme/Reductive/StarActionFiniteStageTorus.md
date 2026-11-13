# Finite-stage comparison retaining the torus

This is derived internal infrastructure for `SpecialLinearTitsCocycleStatement`.
The construction extends Worker 61 and Worker 5375's finite-stage proof by
retaining information its existential statement hides. The original construction
is reused with attribution. The added conclusions expose the commutative
inclusion square and the character formula already established by that construction.

`StarActionFiniteStage.stageCharacter` first pulls a character back along the
base change of the inverse of the identified original torus, then applies the
actual tower character map. Its direction is from characters over the
intermediate field to characters over the larger field.

`exists_stage_torus` constructs pinning data over an intermediate field at which
the supplied torus splits. It returns an isomorphism of the original tori over
the ground field, its commutative inclusion square, and an equivalence of full
root data whose weight map is exactly `stageCharacter`. The equivalence carries
the chosen bases onto each other and intertwines the star actions for every
compatible pair of field automorphisms. The constructed torus is the supplied
torus and its identifying isomorphism is the identity; the theorem exposes the
commutative square so consumers can use it without depending on reducibility of
the construction.

The proof reflects connected reductivity through the algebraic larger field,
uses the tower group and torus isomorphisms to descend maximality of the torus,
constructs a root datum over the intermediate field, and compares it by lattice
base change and the torus-compatible root-datum equivalence. It transports the
original base back and supplies simple-root vectors over the intermediate field.
The existing character tower and based projection lemmas give star compatibility.
It also records the character formula already proved during this construction.

`exists_finiteGaloisStage_torus` chooses a finite Galois splitting field of the
supplied torus and a ground-field embedding in the separable closure, then
applies the intermediate-stage construction. The embedding provides the algebra
structure used for the tower; the spectrum square is proved from ground-field
linearity. No descent of the originally chosen root vectors is claimed.

All fields and tori are actual Library objects, and arbitrary characteristic and
universe `u` are retained. These helpers do not prove the special-linear Tits
cocycle statement or the matrix automorphism classification.
