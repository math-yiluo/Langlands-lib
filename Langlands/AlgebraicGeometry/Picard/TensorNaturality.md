# Tensor as a natural operation on rigidified Picard presheaves

This module packages the existing tensor operations as natural transformations
on the presheaves of rigidified line-bundle classes and of geometric Picard-zero
classes. The source of each transformation is the pointwise product of its
target presheaf with itself. All schemes have universe `u`; the presheaves take
values in `Type (u + 1)`.

## Explicit premises

Both natural transformations retain the following published propositions as
explicit hypotheses:

- `pullbackTensorComparisonIsIsoStatement`, asserting invertibility of the
  specified canonical pullback tensor comparison;
- `PullbackTensorCompositionStatement`, its compatibility with the specified
  composite-pullback comparison;
- `PullbackTensorLeftUnitorStatement`, compatibility of the fixed pullback-unit
  and tensor comparison maps with the explicit left unitor;
- `RigidifiedModule.PullbackCoherenceStatement`, the identity and composition
  compatibility needed for the existing rigidified class presheaf.

The Picard-zero construction additionally retains
`AbelianScheme.PicardZeroPullbackStatement`, which says that actual pullback of
rigidified relative families preserves the geometric Picard-zero condition.
None of these premises is proved by this module. They concern the existing
specified operations, not freely supplied functors or multiplication maps.

## All rigidified classes

For a morphism `f : X → S` and a section `ε : S → X`, let `F` be the existing
`classPresheaf`. `classTensorNatTrans` has source

`F.prod' F ⋙ Functor.uncurry.obj Limits.Types.binaryProductFunctor`

and target `F`. At a test scheme `T`, the source is the actual product type
`F(T) × F(T)`, with pullback applied in both components. The transformation
sends `(q,r)` to `classesTensor T q r`, the quotient operation induced by the
constructed rigidified line-bundle tensor.

Naturality is exactly the previously proved `classesPullback_tensor` equation,
with the orientation required for a natural transformation. That equation is
induced by the canonical compatible isomorphism for pullback of tensor along
the relative square. The component formula `classTensorNatTrans_app` is
reflexive, so packaging has not changed the operation.

## Geometric Picard-zero classes

The existing `PicardZeroClasses A T` is the subtype of rigidified classes whose
underlying line bundles, on every algebraically closed geometric fibre, are
invariant under all point translations. The existing tensor and pullback on
this subtype use their separately proved or explicitly hypothesized closure
properties.

`picardZeroClassesPullback_tensor` proves

`h*(q ⊗ r) = h*q ⊗ h*r`

for every `h : T → U` over `S` and every two Picard-zero classes at `U`.
Subtype extensionality reduces the equation to `classesPullback_tensor` for
the underlying rigidified classes. This equation requires the first three
comparison premises and Picard-zero pullback stability. It does not require
rigidified pullback coherence, since it is an equation for a single pullback
map rather than the construction of a presheaf.

`picardZeroTensorNatTrans` then packages the restricted tensor as a natural
transformation from the pointwise product of `picardZeroPresheaf` with itself
to that presheaf. Here rigidified pullback coherence is additionally needed for
the presheaf. `picardZeroTensorNatTrans_app` records its component formula.
Finally, `picardZeroTensorNatTrans_inclusion` states componentwise that the
existing inclusion into all rigidified classes preserves this natural tensor.
It holds by reflexivity: the restricted tensor forgets to the original tensor.

## Provenance and scope

This is a derived packaging of the Library's constructed operations.
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph (6.2),
printed p.88 (PDF p.92), specifies the tensor and pullback operations on
compatible isomorphism classes of rigidified line bundles. The geometric
Picard-zero convention used by the imported subtype is motivated by the point
formula for `φ_L` on printed p.95 (PDF p.99) and its kernel characterization in
Corollary (7.22), printed p.106 (PDF p.110). This module proves no new equivalence
with an identity component.

No assumptions of projectivity or noetherianity are used in these categorical
calculations. The transformations are natural binary operations on the
existing set-valued presheaves. This module does not supply the associativity
and inverse constructions needed for a full group-valued presheaf, nor any
sheaf comparison or representability theorem.
