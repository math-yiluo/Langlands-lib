# Scalar extension of compatible equivariant coefficients

The module `Langlands.Geometry.EtaleScalarExtensionDiagram` constructs
sheafified extension of scalars on compatible equivariant coefficient diagrams.
Its declarations lie in `Langlands.Geometry.EtaleCohomologyAction`, with
the diagram constructions in the nested `EquivariantCoefficientDiagram`
namespace.

## Parameters and provenance

Let `R A : Type u` be arbitrary commutative rings and `φ : R →+* A`.
Schemes and module carriers have the same universe `u`. The index category
`J` has object universe `v` and morphism universe `w`. Supply
`S : J ⥤ Scheme.{u}ᵒᵖ`, with every induced map

```text
f_a := (S.map a).unop : (S.obj j).unop ⟶ (S.obj i).unop
```

etale, for `a : i ⟶ j`. A fixed group `G : Type t`, with independent
universe `t`, acts through homomorphisms
`ρ i : G →* (Aut (S.obj i).unop)ᵐᵒᵖ`. The supplied equations `hρ a g` are

```text
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

These are exactly the geometric inputs of the existing coefficient category.
The opposite-automorphism convention is retained. No topology on `G`,
flatness of `φ`, or invertibility of the coefficient transitions is required.

This is an internal categorical construction using the actual functor and
comparisons in
[equivariant scalar extension](EtaleEquivariantScalarExtension.md),
[its pullback comparison](EtaleEquivariantScalarExtensionPullback.md), and
[compatible equivariant coefficients](EtaleEquivariantCoefficientDiagram.md).
The equality comparisons come from
[equivariant pullback coherence](EtaleEquivariantPullbackCoherence.md).
No external theorem is transcribed, and no new comparison or coherence
equation is supplied as an assumption.

Write `L_i` for `scalarExtensionFunctor φ (ρ i)`,
`P_a^R` and `P_a^A` for the equivariant diagram restrictions, and `β_a`
for the forward extension/pullback comparison

```text
P_a^A (L_i F) ⟶ L_j (P_a^R F).
```

Here `;` denotes composition in order of application.

## Geometric comparison laws

`scalarExtensionEquivariantPullbackIso_congr` applies to any two equal
etale maps `f k : Y ⟶ X`, supplied source and target actions, and
their respective equivariance proofs. With `e : f = k`, it proves

```text
β_f(F) ; L_Y.map(congr_R(e)_F)
  = congr_A(e)_(L_X F) ; β_k(F).
```

Its proof substitutes the equal scheme map; the equality comparisons
then become identities, and functoriality proves the equation.

`scalarExtensionEquivariantPullbackIso_comp_hom` restates the existing
composition law using the forward geometric comparison. If `f : Y ⟶ X`
and `k : Z ⟶ Y` are equivariant etale maps, write
`d_R : P_f^R ⋙ P_k^R ≅ P_(k≫f)^R`, and likewise `d_A`. Then

```text
d_A.hom(L_X F) ; β_(k≫f)(F)
  = P_k^A.map(β_f(F)) ; β_k(P_f^R F) ; L_Z.map(d_R.hom(F)).
```

The proof cancels the isomorphism `L_Z.map(d_R.inv(F))`, applies the
published inverse-comparison equation, and uses the inverse identities
and preservation of composition and identity.

The diagram comparisons include transport along `S.map_id` and
`S.map_comp`. The next two lemmas handle that transport explicitly.
Writing `e_i^R : P_id^R ≅ Id` and
`d_ab^R : P_a^R ⋙ P_b^R ≅ P_(a≫b)^R` for those comparisons, they prove

```text
scalarExtension_diagramRestrictionId:
  β_id(F) ; L_i.map(e_i^R.hom(F)) = e_i^A.hom(L_i F),

scalarExtension_diagramRestrictionComp:
  d_ab^A.hom(L_i F) ; β_(a≫b)(F)
    = P_b^A.map(β_a(F)) ; β_b(P_a^R F) ; L_k.map(d_ab^R.hom(F)).
```

The first expands the diagram identity comparison, moves extension
past equality transport by the congruence lemma, and applies the existing
geometric identity law. The second expands the diagram composition
comparison, applies the same congruence lemma and the forward geometric
composition law, and reassociates.

## The extension functor

`extendScalars φ D` has vertex `L_i(D.obj i)` and transition

```text
β_a(D.obj i) ; L_j.map(D.map a).
```

Thus the new transition is a genuine equivariant sheaf morphism.
Its identity law follows from `D.map_id` and the diagram identity
comparison law. For composition, the diagram composition comparison
law moves extension through the two successive geometric restrictions.
The proof then uses `D.map_comp` and naturality of `β_b` at `D.map a`.
No compatibility law for the new diagram is assumed.

`extendScalars_map_hom` identifies the underlying sheaf transition as
the ordinary `sheafExtendScalarsPullbackIso` component followed by
ordinary `sheafExtendScalars` applied to the original underlying
transition. This is a definitional equality for the chosen functors.

`extendScalarsMap φ α` has component `L_i.map(α.app i)`. Its transition
square follows by applying extension to `α.comm` and using naturality
of `β_a`. The construction packages into

```text
extendScalarsFunctor φ :
  EquivariantCoefficientDiagram R S ρ hρ
    ⥤ EquivariantCoefficientDiagram A S ρ hρ.
```

Functorial identity and composition are proved at each vertex by the
corresponding laws of `scalarExtensionFunctor`.
`extendScalarsEvaluationIso i` is the identity natural isomorphism
between evaluation after diagram extension and evaluation followed
by scalar extension on that vertex.

## Scope

This construction applies to any supplied index category and the geometric
data above, including oppositely oriented indexing diagrams. It does not
construct a limit or an inverse-limit comparison. The unit constructs the
extension functor; a diagram-level adjunction and coefficient identity,
composition, reindexing and mixed ring/geometric coherence remain separate.
No exactness, preservation of injectives, commutation of scalar extension
with global sections or higher cohomology, topology or smoothness of
group actions, compact-support comparison, ideal reduction, actual Harris
coefficient system or Shimura tower, or Harris comparison theorem is
asserted here.
