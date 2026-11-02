# Algebraic-space quotients of etale equivalence relations

Authors: Worker 421 and Worker 416. Worker 421 prepared the prototype
Lean declaration and explanation; Worker 416 checked the retained original
and the published interfaces and completed the source comparison.

This is the presentation form of Stacks Project Theorem 65.10.5, Tag
[02WW](https://stacks.math.columbia.edu/tag/02WW), using the published actual
scheme relation and algebraic-space definitions. This module states a
proposition and contains no proof of it.

The retained original is registered as
`stacks-etale-equivalence-relations-2026-11-01`, directory SHA-256
`df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`.
The source folder contains `02WW.html` and the text aid `02WW.txt`.
The theorem, its complete proof, and its single page comment were read.
Comment 216 corrects a grammatical typo in the proof. No source-specific
errata note was present in the project, current Library or workspace
`notes/errata/` locations checked. The definition of a presentation is
Definition 65.9.3, Tag [0263](https://stacks.math.columbia.edu/tag/0263);
the relation conventions are Definitions 39.3.1 and 65.9.2, Tags
[022P](https://stacks.math.columbia.edu/tag/022P) and
[02WS](https://stacks.math.columbia.edu/tag/02WS). Both definition pages
and all their comments were read. Comments 6527 and 6528 on 022P confirm
that an equivalence relation includes the monomorphism requirement.
Definition 39.3.1 writes the pair as `(t,s)`; 02WW writes `(s,t)`.
Interchanging the two projections does not change the assertion.

`EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}` quantifies over
every `S : Scheme.{u}`, every published `EtaleEquivalenceRelation.{u}`,
and every `b : E.U ⟶ S` satisfying `E.t ≫ b = E.s ≫ b`. This single
equation makes the absolute relation a relation over `S`. Indeed,
`(E.t,E.s)` factors through `E.U ×_S E.U`; the factor is a monomorphism
because the map to the absolute product is one. The absolute reflexivity,
symmetry and transitivity restrict to all tests over `S`: a witness
`r : T ⟶ E.R` for a pair of maps over `S` is itself over `S`, since its
composite with `E.t ≫ b` equals the given structure map of `T`. Conversely, a
relation over `S` has the published absolute relation structure, so this
formulation covers every etale equivalence relation over `S`.

The local `let` bindings retain the original schemes and maps in the slice:
`U = Over.mk b`, `R = Over.mk (E.t ≫ b)`, and `t,s : R ⟶ U` have
underlying morphisms `E.t,E.s`. The first slice-map compatibility is
definitional; the second is `hb.symm`, since `Over.homMk E.s` requires
`E.s ≫ b = E.t ≫ b`. The conclusion supplies an actual
`Q : AlgebraicSpace S` and a natural transformation
`a : (schemeYoneda S).obj U ⟶ Q.presheaf`. Thus `Q` is an actual fppf
sheaf with scheme-representable diagonal and a surjective etale scheme
atlas, using the published `AlgebraicSpace.Basic` convention.
The specified map `a` is itself representable, etale, and geometrically
surjective, and its presheaf kernel pair is exactly the original
represented pair `(t,s)`. More precisely,
`IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a`
asserts both commutativity and the full pullback universal property in the
category `(Over S)ᵒᵖ ⥤ Type (u + 1)`. Evaluating at every `T : Over S`
identifies the lifted `R(T)` with pairs of lifted `U(T)` sections having
equal image in `Q(T)`.

This records the source's assertion that `(U,R,U → U/R)` is a presentation.
It also determines the quotient as an fppf sheaf: a representable etale
geometrically surjective map is locally surjective for the fppf topology,
and hence an epimorphism in the sheaf category. Indeed, pulling it back
along a section over any test scheme produces an actual etale surjective
scheme morphism, an fppf covering on which that section lifts. Epimorphisms
of sheaves of sets are effective, so its kernel pair has `Q` as coequalizer.
Equivalently, any map from `U` to an fppf sheaf equalizing `t` and `s`
factors uniquely through `Q`. This explanation identifies the
mathematical meaning of the statement; this module does not implement that
comparison or construct a chosen quotient functor.

All schemes stay in the arbitrary universe `u`, and presheaves use the
existing lifted values `Type (u + 1)`. The statement imposes no affineness,
quasi-compactness, separation, noetherianity, finite-presentation or
nonemptiness condition on the schemes. It includes every scheme in the
slice and every section of the resulting sheaf.

The source proof first permits replacing `U` by a surjective etale cover,
then uses the coproduct of an affine open covering. The restricted affine
relations have algebraic-space quotients by Lemma 65.10.4. Those quotients
map to the full quotient by open immersions; coproduct and gluing criteria
then give the full algebraic space. This paragraph describes the original
source route only; none of these quotient or gluing steps is implemented or assumed as a Lean result in
this module. This proposition is a prerequisite for the generic etale-to-fppf
sheaf criterion and the Picard quotient branch; stating it proves neither
criterion nor the proper-field Picard comparison.
