# Source changes of compatible coefficient trivializations

Author: Worker 13.

This module constructs change-of-source comparisons for the compatible
associated and constant coefficient diagrams. It proves that the actual
invariant-section trivialization commutes with these comparisons, naturally
in the entire equivariant coefficient diagram.

## Provenance

This is an internal categorical construction from
[SourceSlice](../../Sheaf/SourceSlice.md) and
[VaryingCoverLocalTrivialization](VaryingCoverLocalTrivialization.md).
The latter imports the constructed associated invariant sheaves,
varying-cover transitions, evaluation maps and geometric section-splitting
theorem. The new comparison is the generic global-sheaf comparison at these
specific diagrams. No new assertion is attributed directly to Harris,
Berkovich or other literature, and the imported files are unchanged.

The generic prerequisites use the actual induced slice topologies and
`Under.map` from Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`; their original definitions
are in `Mathlib/CategoryTheory/Sites/Over.lean` and
`Mathlib/CategoryTheory/Comma/Over/Basic.lean`.

## Evaluation under source change

The first two lemmas apply to an arbitrary category `C : Type w` with
`Category.{v} C` and binary products, a Grothendieck topology `J` and a
commutative ring `R : Type u`. The three universes are independent.
Write `L_Z = J.overPullback (ModuleCat R) Z`,
`P_a = J.overMapPullback (ModuleCat R) a`, and
`c_a(F) = (overPullbackMapIso J (ModuleCat R) a).hom.app F`.
For `a : T → Z`, `b : Z → Y` and a module sheaf `F`,
`productEvaluationAlong_sourceChange` proves

```text
P_a.map (productEvaluationAlong J b F) ≫ c_a(F)
  = c_a(productSheaf(Y).obj F) ≫ productEvaluationAlong J (a ≫ b) F.
```

At `U : Over T`, evaluation on the restricted slice uses the graph of
`(U.hom ≫ a) ≫ b`. Evaluation along the composite uses the graph of
`U.hom ≫ (a ≫ b)`. The proof evaluates the sheaf morphisms on `U`,
simplifies the identity section comparisons, and uses associativity.

For a group `G : Type u`, `Y : Action C G` and a coefficient action
`F : Action (Sheaf J (ModuleCat R)) G`,
`associatedEvaluationAlong_sourceChange` proves the corresponding equation
for `associatedEvaluationAlong`, with `associated J Y F` in the upper
left corner and `F.V` in the lower right. Its proof expands evaluation as
invariant inclusion followed by product evaluation, uses the product
equation, and applies naturality of `overPullbackMapIso` to the actual
invariant inclusion. No trivialization, splitting or torsor hypothesis is
needed for either equation.

## Small-etale inputs and comparison functors

Fix `X : Scheme.{u}`, `R : Type u` with `CommRing R`, an index category
`I : Type uI` with `Category.{vI} I`, and `D : I ⥤ GrpCat.{u}`.
Let `Y : EquivariantDiagram D X.Etale`, and assume
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`.
The geometric predicate is the one in [Etale](Etale.md): finite group,
finite surjective structure morphism and unique transport of geometric
lifts. The scheme, group, ring and coefficient-module carriers share `u`;
the two index universes are independent.

Write `J = Scheme.smallEtaleTopology X` and `Y_k = Y.obj.obj k`.
The input `M : EquivariantDiagram D (ModuleCat.{u} R)` is the full
coefficient diagram. At a source `k`, denote the published functors by

```text
A_k(M) = etaleAssociatedSourceSystem X Y hY k M,
C_k(M) = etaleConstantSourceSystem X Y k M.
```

Both have domain `Under k` and codomain
`Sheaf (J.over Y_k) (ModuleCat R)`. Each constant sheaf is formed on
the original site `J` and then restricted to the slice.

For `f : k → l`, let `P_f` be `sourceSliceRestriction` for `Y.obj`.
It postcomposes a whole `Under l` diagram with
`J.overMapPullback (ModuleCat R) (Y.obj.map f)`.
Let `Q_f` be `sourceSliceReindex`; it precomposes a whole `Under k`
diagram with `Under.map f : Under l ⥤ Under k`, sending
`a : l → i` to `f ≫ a : k → i`. The new isomorphisms are

```text
etaleAssociatedSourceChangeIso f M : P_f(A_l(M)) ≅ Q_f(A_k(M)),
etaleConstantSourceChangeIso f M   : P_f(C_l(M)) ≅ Q_f(C_k(M)).
```

They specialize `sourceSliceChangeIso` respectively to
`etaleAssociatedVaryingSystem X Y hY M` and
`M.obj ⋙ constantSheaf J (ModuleCat R)`. Their forward and inverse maps
are identities on section modules. The identity and composition equations
in SourceSlice apply to these specializations directly, with the same
standard slice comparisons and `Y.obj` functor laws.

`etaleAssociatedSourceChangeFunctorIso` and
`etaleConstantSourceChangeFunctorIso` make these comparisons natural in
the entire coefficient diagram. They whisker the generic
`sourceSliceChangeFunctorIso` by the associated varying-system functor
and the underlying-constant-diagram functor respectively. The two `_app`
lemmas identify their components with the displayed ordinary diagram
isomorphisms by reflexivity.

## The compatibility square

The theorem `etaleAssociatedEvaluationAlong_sourceChange` specializes the
generic invariant-evaluation equation to the sheafified coefficient action
at `i`. It only uses the actual map `a : T → Z`, the lift
`b : Z → Y_i` and the full coefficient input; it needs no `hY`.

Write `t_k(M) = (etaleAssociatedSourceTrivialization X Y hY k M).hom`,
and `a_f(M)`, `c_f(M)` for the forward associated and constant source
comparisons. The theorem `etaleAssociatedSourceTrivialization_sourceChange`
proves the equality of transformations of `Under l` diagrams

```text
P_f.map (t_l(M)) ≫ c_f(M) = a_f(M) ≫ Q_f.map (t_k(M)).
```

At `i : Under l`, it is the evaluation source-change equation for
`Y.obj.map f` followed by `Y.obj.map i.hom`. The functor law identifies
their composite with `Y.obj.map (f ≫ i.hom)`, exactly the lift selected
by `Under.map f`. Thus the square uses the proved canonical
invariant-section trivialization, whose components come from geometric
section splitting.

Finally, `etaleAssociatedSourceTrivializationFunctor_sourceChange` states
the same square as an equality of natural transformations on
`EquivariantDiagram D (ModuleCat R)`. Its proof is the ordinary diagram
square at every `M`. All evaluation and compatibility lemmas carry
`@[reassoc]` variants.

## Scope

The scheme and compatible finite geometric torsors are genuine supplied
inputs. The reachable terms are indexed by arrows out of the chosen source;
this does not assert that a finite cover trivializes arbitrary later terms.
There is no filteredness, cofinality or separating-tower assertion.

The comparisons are on the actual induced slices of `X.Etale`; no
identification with an independently formed geometric site or constant
sheaf is assumed. This unit constructs ordinary local sheaf diagrams and
their maps. Particular Harris geometry, derived source-change functors,
global or compact-support cohomology, inverse limits, smooth or Galois
actions, uniformization and the Ext spectral sequence remain separate
obligations.

Formal environment: Lean 4.34.0 and the Mathlib commit given above.
All intrinsic naturality, invertibility and compatibility obligations are
proved without new axioms or proof holes.
