# Existence of a valuative lift after a dominating extension

Author: Worker 1543.

`SpaceValuativeExtensionExistenceStatement` states existence of a valuative
lift after a dominating valuation extension for a quasi-compact separated
universally closed morphism of algebraic spaces. It is an unproved
proposition definition.

## Source and specialization

The source is Stacks Project, *Morphisms of Algebraic Spaces*,
Lemma 67.42.2(1) (Tag 0A3X), printed pp. 89–90, using the existence
criterion of Definition 67.41.1 (Tag 03IX), printed pp. 82–83.
The source lemma assumes quasi-separatedness and universal closedness.
The present statement specializes to separated morphisms, which are
quasi-separated, and retains the additional quasi-compactness hypothesis
of `SpaceValuativeExistenceStatement`. It does not state the full
quasi-separated version of the source lemma.

The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, retained folder
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms of
Algebraic Spaces, full chapter PDFs (version ed88ff78)/`, folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`.
The cited file is `spaces-morphisms.pdf`, SHA-256
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

## Exact meaning

The base scheme `S` and the algebraic spaces `X` and `Y` over it are
arbitrary. For a morphism `f : X ⟶ Y`, the hypotheses are the Library's
actual predicates `IsQuasiCompactMorphism f`, `IsSeparatedMorphism f`
and `IsUniversallyClosedMorphism f`. The valuation ring `A`, its fraction
field `K`, and the map `s : Spec A → S` are arbitrary in universe `u`.

Given `x : X(K)` and `y : Y(A)` with `f(x) = y|_K`, the conclusion is
`HasDominatingValuativeLift f A K s x y`. By the imported definition,
this supplies a valuation ring `B` with fraction field `L`, a local ring
map `A → B`, and a compatible field map `K → L`, together with a section
`a : X(B)`. Its restriction to `L` is the scalar extension of `x`, and
`f(a)` is the pullback of `y` to `B`.

There is no finite type, noetherian, decency, discrete valuation or
rank hypothesis. There is no restriction on the degree or separability
of `L/K`. This conclusion allows extension of the field and valuation
ring; obtaining a lift over `A` itself is a separate descent obligation.

## Role in the consumer

This statement isolates the topological existence step for Task 5368.
The source proof passes to `X ×_Y Spec A`, uses universal closedness
to find a specialization over the closed point of `Spec A`, and realizes
the specialization over a valuation extension by Lemma 67.16.5
(Tag 089B). This paragraph describes the source route, not an implemented
Lean proof.
