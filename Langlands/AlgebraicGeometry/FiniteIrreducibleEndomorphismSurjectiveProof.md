# Finite endomorphisms of irreducible Noetherian schemes are surjective

`Langlands.AlgebraicGeometry.finiteIrreducibleEndomorphismSurjective` proves
exactly the published proposition
`Langlands.AlgebraicGeometry.FiniteIrreducibleEndomorphismSurjectiveStatement`.
For every universe `u`, every scheme `X : Scheme.{u}` with
`TopologicalSpace.NoetherianSpace X` and `IrreducibleSpace X`, and every
endomorphism `f : X ⟶ X`, it proves `IsFinite f → Surjective f`.
Here the finiteness and surjectivity predicates are Mathlib's actual scheme
morphism predicates, and surjectivity concerns all underlying scheme points.
Noetherianity concerns the underlying topology, without an assumption on local
rings. The statement pair and its import closure are unchanged.

## Internal provenance

This is an internal derived proof of the Library's general scheme-topology
lemma. Worker 414 supplied the generic-point argument using discrete fibres
and the descending-chain condition. The implementation expresses the
chain obstruction as well-founded induction on closed singleton closures.
This proof is not attributed to an external abelian-variety theorem.
It uses neither `Langlands.GroupScheme.FieldFiniteEndomorphismSurjectiveStatement`
nor `Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement`.

## Implemented topology argument

The private lemma `eq_of_specializes_self_of_discrete_fibres` treats a
continuous self-map `g` of a Noetherian `T0` topological space `T` whose fibres
`g ⁻¹' {y}` are discrete. It proves that if `x ⤳ g x`, then `x = g x`.
The hypotheses of this private helper are discharged by the scheme application;
they add no hypothesis to the public theorem.

The lemma uses `WellFoundedLT (TopologicalSpace.Closeds T)`, supplied by
`NoetherianSpace T`, and inducts on a closed subset `C`. Its induction property
quantifies over every point `z` with `closure {z} = C` that specializes to
`g z`. The argument is as follows.

1. If `z = g z`, the assertion is immediate. Otherwise specialization gives
   `closure {g z} ⊆ closure {z}`. Reverse inclusion would give
   `g z ⤳ z`; mutual specialization implies equality in a `T0` space, contrary
   to the case assumption. Thus the closed singleton closure strictly decreases.
2. Continuity sends `z ⤳ g z` to `g z ⤳ g (g z)`. The induction hypothesis
   at the smaller closed subset gives `g z = g (g z)`.
3. Both `z` and `g z` then belong to the fibre over `g z`. Applying
   `IsDiscrete.eq_of_specializes` inside this discrete fibre to
   `z ⤳ g z` proves `z = g z`.

This step uses discreteness of the fibre topology, rather than merely finite
cardinality. It avoids both dimension theory and an explicit sequence of
iterated points.

## Scheme application

The public proof introduces exactly the variables and hypotheses of the
published proposition and installs the given `IsFinite f` as a local instance.
Importing `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` provides the
instance that a finite morphism is locally quasi-finite and the theorem
`Scheme.Hom.isDiscrete_preimage_singleton` for its point fibres.

The underlying point space of a scheme is `T0` and `QuasiSober`; irreducibility
therefore supplies `genericPoint X`. The specialization
`genericPoint X ⤳ f (genericPoint X)` is `genericPoint_specializes`.
The private lemma, applied to `f.continuous` and the discrete-fibre theorem,
gives `genericPoint X = f (genericPoint X)`. Consequently the generic point
belongs to `Set.range f`.

Finite morphisms are integral and universally closed through Mathlib's
instances. Hence `f.isClosedMap.isClosed_range` shows that this range is closed.
It contains the closure of its generic point by `closure_minimal`.
`genericPoint_closure X` identifies that closure with `Set.univ`, proving
pointwise surjectivity. The final constructor packages this function
surjectivity as `AlgebraicGeometry.Surjective f`.

The proof retains arbitrary universes and assumes no base field, properness,
reducedness, dimension bound, group structure, dominance, flatness, surjectivity,
image certificate or conclusion certificate. Its intended applications to
abelian schemes still require their own proofs of the topological hypotheses
and their separate exact statement targets.

## Verification scope

The source is checked in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
with Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The public theorem's type is the named Library statement itself, with universe
parameter `u`. This module adds one private proved topology lemma and the exact
target theorem, with no proof holes or new axioms. Compilation is development
evidence; independent semantic review, exact-target validation and Library
publication remain separate admission requirements.
