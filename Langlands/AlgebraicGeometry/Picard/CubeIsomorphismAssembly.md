# Algebraic assembly of isomorphisms from pullback comparisons

This internal construction turns a supplied triviality-detection principle
for three actual scheme morphisms into an actual isomorphism between two
line bundles. It keeps its tensor and triviality hypotheses explicit. It
does not prove the unconditional geometric cube theorem or
`FieldCubeIsomorphismStatement`.

## Exact interface

All schemes have an arbitrary universe parameter `u`.
`pullbackTensorInverseTrivialization` takes a morphism `f : T ⟶ S`, actual
module sheaves `L M N` on `S`, an isomorphism `f^* L ≅ f^* M`, and an
isomorphism `tensorObj M N ≅ O_S`. Under the explicit proposition
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u}`, it
returns an actual isomorphism `f^*(tensorObj L N) ≅ O_T`.

`lineBundleIsoOfThreePullbackComparisons` takes four schemes `S T₁ T₂ T₃`,
three actual morphisms `fᵢ : Tᵢ ⟶ S`, and the following explicit premises:

- `LocallyFreeRankOneIffTensorInvertibleStatement S`, the comparison for
  every actual module sheaf on the ambient scheme;
- invertibility of the canonical pullback-tensor comparison for every
  morphism of schemes in universe `u`;
- a triviality principle: every `D : LineBundle S` whose three pullbacks
  are isomorphic to their respective structure sheaves is itself isomorphic
  to `O_S`.

Given `L M : LineBundle S` and an actual isomorphism `fᵢ^* L.obj ≅
fᵢ^* M.obj` for each of the three morphisms, the output is an actual
module-sheaf isomorphism `L.obj ≅ M.obj`. The triviality premise uses
`Nonempty` of isomorphism types. The construction uses classical choice
to select an isomorphism from the resulting existence proof. It asserts
no uniqueness or extension of any selected pullback witness.

## Implemented construction

The pullback helper uses the canonical tensor comparison forwards, tensors
the given comparison with the identity on `f^* N`, uses the canonical
comparison backwards, pulls back the supplied tensor-inverse isomorphism,
and applies `pullbackUnitIso f`. The local `IsIso` instance is obtained
from the explicit preservation argument. A strong monoidal pullback
structure and its coherence laws are not required.

For the second construction, local rank one of `M.obj` gives an existential
right tensor inverse `N` under the explicit comparison assumption.
Braiding gives `N ⊗ M.obj ≅ O_S`, so `N` is also tensor-invertible.
`L.obj` is tensor-invertible by the same comparison; closure under tensor
therefore makes `L.obj ⊗ N` invertible. The published
`localizedTensorIso` compares this monoidal tensor with the explicit
sheaf tensor `tensorObj L.obj N`. Transporting invertibility across
that isomorphism and applying the reverse comparison makes the explicit
tensor a line bundle, called `difference`.

The pullback helper converts the three given comparisons into
trivializations of the three pullbacks of `difference`. The supplied
triviality principle yields `difference.obj ≅ O_S`. Finally the
construction composes actual monoidal isomorphisms

`L.obj ≅ L.obj ⊗ O_S ≅ L.obj ⊗ (N ⊗ M.obj) ≅
(L.obj ⊗ N) ⊗ M.obj ≅ O_S ⊗ M.obj ≅ M.obj`.

These are the right unitor inverse, tensor with the inverse of the
braided tensor-inverse isomorphism, the associator inverse, tensor with
the global trivialization after `localizedTensorIso`, and the left
unitor. No scheme Picard group or concrete dual construction is used.

## Intended geometric application and remaining obligations

The geometric application takes `S = (X ⨯ (Y ⨯ Z)).left`, with the three
actual `CubeFace` morphisms as `f₁`, `f₂`, and `f₃`. A proof of
`FieldCubeTrivialityStatement` specialized to the chosen field, nine
geometric hypotheses and three specified rational sections will provide
the triviality argument. It is not supplied by this construction.

As of the construction's submission, the required exact proof tasks are:
the local comparison, `45730c00-045d-4204-bf5f-1f49e61f733b` revision 2
(Worker 344); canonical pullback-tensor invertibility,
`a2c3b108-b55b-4f55-862a-6ef3eac96399` revision 2 (Worker 150); and the
geometric cube theorem, `43f34b60-51af-49af-a39f-c17180f99b48` revision 1
(Worker 337). Their published proposition definitions and conditional
helpers are not their proofs.

This is an intermediate construction for task
`059cc734-d99b-4088-b28d-507ce8fdb005` revision 2, which retains the full
unconditional all-universe target `FieldCubeIsomorphismStatement`. The
final theorem must obtain all its prerequisites from accepted published
proofs and add none of these explicit helper arguments to that target.

## Provenance and original source

The construction is internal tensor algebra abstracted from the usual
two-line-bundle corollary of Milne's geometric theorem of the cube. It
works for actual scheme-module sheaves and arbitrary three morphisms;
Milne does not state this general conditional interface. Its geometric
motivation is J. S. Milne, *Abelian Varieties*, corrected January 2, 2022
author version of the 1986 chapter, Theorem 6.1, printed/PDF p.8.
The conventions on p.2 and the theorem, proof and descent Lemma 6.2 on
pp.8–9 were read. Their geometric arguments are not implemented here.

Registered source `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The complete retained author errata page was also read; none of its
entries changes Theorem 6.1. Registered snapshot
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
retained at
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.

Author: Worker 482. The construction reuses the published tensor,
invertibility and line-bundle interfaces by Lean name; no unpublished
draft from another worker was used.
