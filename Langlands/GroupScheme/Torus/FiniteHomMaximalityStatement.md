# Reflection of maximal tori along a finite homomorphism: statement

Authors: Worker 1437 (the Lean proposition and the original source route),
Worker 1482 (the audit of its quantifiers and source route, and the task),
Worker 1388 (the verification and this Markdown).

This file defines the proposition
`Langlands.GroupScheme.FiniteHomMaximalTorusReflectionStatement.{u}`. It
proves nothing. A Lean proof is a separate successor obligation.

## Statement

For every field `k : Type u`, in an arbitrary universe and of any
characteristic, imperfect fields included, take the following data:

- connected reductive group schemes `G` and `H` over `Spec k`;
- a homomorphism `π : G ⟶ H` whose underlying morphism of schemes is finite;
- commutative group schemes `T` and `S` over `Spec k`;
- homomorphisms `j : T ⟶ G` and `i : S ⟶ H`, and a homomorphism
  `f : T ⟶ S` of commutative group schemes.

Assume that `T` is a torus, that `j` is a closed subgroup and that `i` is a
maximal torus. Assume also that the underlying morphism of schemes of `f`
is surjective, and that `j ≫ π = groupHom f ≫ i` as homomorphisms
`T ⟶ H`. The proposition concludes that `j` is a maximal torus of `G`.

## Meaning of each hypothesis in Lean

- `GroupScheme (Spec (CommRingCat.of k))` is a group object in schemes
  over `Spec k`. `CommGroupScheme` adds explicit commutativity, and
  `T.toGrp` is the underlying group scheme.
- `IsConnectedReductive G` is the Library structure. It requires
  `G.X.hom` to be smooth and affine and `G.X.left` to be a connected space.
  It also requires the unipotent radical of the base change of `G` to
  `AlgebraicClosure k` to be trivial.
- `IsFinite π.hom.hom.left` says the morphism of schemes `G.X.left ⟶ H.X.left`
  underlying `π` is finite. Nothing else is assumed about `π`. It need not
  be central, flat, surjective or separable, and its kernel need not be
  smooth.
- `IsTorus T.toGrp` is the Library definition (Milne 12.14). It says `T`
  becomes a split torus after base change to some field extension
  `K : Type u` of `k`.
- `IsClosedSubgroup j` says the morphism of schemes underlying `j` is a
  closed immersion.
- `IsMaximalTorus i` has three parts: `S` is a torus, `i` is a closed
  subgroup, and `i` has no strictly larger closed torus. That last part
  means that whenever `i = g ≫ i'` with `i' : T' ⟶ H` a closed immersion
  and `T'` a torus, `g` is an isomorphism.
- `Surjective (CommGroupScheme.groupHom f).hom.hom.left` is
  `AlgebraicGeometry.Surjective` for the morphism of schemes
  `T.X.left ⟶ S.X.left` underlying `f`. It is surjectivity of the
  underlying map of topological spaces, not surjectivity of `T(k) ⟶ S(k)`
  on rational points.
- `j ≫ π = CommGroupScheme.groupHom f ≫ i` is an equality of group-scheme
  homomorphisms `T.toGrp ⟶ H`.

## Maximal tori and maximal split tori

`IsMaximalTorus` compares `i` with every closed torus `T'` of the ambient
group. It includes tori that do not split over `k`. The Library predicate
`IsMaximalSplitTorus` (in `Rational/SplitTorus`) compares only with split
subtori, and over a field that is not separably closed it is in general a
weaker property. For example, over `ℝ` the norm-one torus of `ℂ/ℝ` has no nontrivial
split subtorus. Its trivial subgroup is therefore a maximal split torus but
not a maximal torus.

Both the hypothesis on `i` and the conclusion on `j` concern maximality among
all tori. Neither `T` nor `S` is required to be split. The intended consumer,
proof task `aa3b37a9-010c-46d5-8cc8-cdc83c6a456b`, lifts a maximal split
torus along a homomorphism and then needs all-torus maximality of the lift.
Maximality among split tori alone would not give it.

## Provenance

This is a derived structural statement. It is not a numbered result of
J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`. The following original passages were read.

- Proposition 17.20, printed pp.357–358 (one-based PDF pp.373–374). Section
  17b states at its start (printed p.353) that `G` is a connected group
  variety over an algebraically closed field. For a quotient map
  `q : G → Q` of connected group varieties, 17.20 says that the image of a
  maximal torus is a maximal torus, and that every maximal torus of `Q`
  arises this way. This is a forward statement about quotient maps over an
  algebraically closed field. The proposition here goes the other way, for
  an arbitrary finite homomorphism over an arbitrary field. Using 17.20
  requires first passing to the image of `π`, so the proposition is not a
  translation of 17.20.
- Theorem 17.82, printed p.379 (one-based PDF p.395): for a group variety
  `G` over `k` and a field `k'` containing `k`, a torus `T` in `G` is maximal
  if and only if `T_{k'}` is maximal in `G_{k'}`.
- Definition 19.20 and the paragraph after it, printed pp.401–402 (one-based
  PDF pp.417–418). The rank of `G` is the dimension of a maximal torus in
  `G_{k^a}`. By 17.82 it is also the dimension of any maximal torus in `G`.
  This proposition introduces no rank.

The registered author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read in full. Its
Chapter 17 entries (pp.360, 364, 386) and its Chapter 19 entry (p.399) do
not concern 17.20, 17.82 or 19.20.

## Proof routes

**Source route** (Worker 1437):

1. Base change to an algebraic closure. By 17.82, `S` stays maximal.
2. Extend `T` to a maximal torus `M` of `G`.
3. The image of `M` in `H` is a torus containing `S`, so it equals `S`.
   (Over the image of `π` this step is 17.20.)
4. The restrictions of the finite `π` give `dim T = dim S = dim M`.
5. A closed inclusion of tori of equal dimension is an isomorphism, so
   `T = M`.
6. Descend maximality to `k` with 17.82.

In the Library, this route would need two inputs:

- the forward implication of 17.82, which is published only as
  `MaximalTorusBaseChangeForwardStatement`, with a reduction to explicit
  unproved premises;
- a dimension comparison for tori under finite maps.

The route that is now available avoids both.

**Library route** (Worker 1482). Everything this route needs is now
published.

- `finiteHomMaximalTorusReflection_of_torusImage`, in module
  `Langlands.GroupScheme.Torus.FiniteHomMaximalityReduction`, proves
  `FiniteHomMaximalTorusReflectionReductionStatement.{u}`. That statement
  says the published proposition `TorusImageClosedTorusStatement.{u}`
  implies a conclusion with exactly the quantifiers and hypotheses of the
  present proposition. The proof runs as follows:
  1. Take any closed torus `M` through which `j` factors as `a ≫ m`.
  2. The torus-image hypothesis factors `m ≫ π` through a closed torus `Z`
     of `H`.
  3. `S` factors through `Z`, because `T ⟶ S` is schematically dominant.
     Maximality of `S` then makes `S ≅ Z`.
  4. The resulting `q : M ⟶ S` is finite, and `a ≫ q = groupHom f` is
     schematically dominant.
  5. Integral incomparability (`isIso_of_closedImmersion_finite_comp_schematic`
     in `Torus.FiniteHomRigidity`) makes the closed immersion `a` an
     isomorphism.
- `torusImageClosedTorusStatement`, in module
  `Langlands.GroupScheme.Torus.ImageProof`, proves
  `TorusImageClosedTorusStatement.{u}`. It takes the actual schematic image
  of a torus and shows that it is a torus, using a splitting field.

Together these leave no unproved structural input. The intended successor
proof is the term
`finiteHomMaximalTorusReflection_of_torusImage torusImageClosedTorusStatement`.
In a private development check, not part of this candidate, that term
elaborated with this proposition as its type. It used only the standard
axioms. Publishing the proof remains a separate successor obligation, and
this file claims no proof.
