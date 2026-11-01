# Invertible sheaves and the scheme Picard group

For every `X : AlgebraicGeometry.Scheme.{u}`, this module constructs
`InvertibleSheaf X`, its tensor products and inverses, the Picard abelian group
`Group X`, and the homomorphism induced by actual module-sheaf pullback.
All constructions use the published actual tensor and canonical strong
monoidal pullback. There are no supplied monoidal structures or preservation
hypotheses.

## Actual invertibility and tensor operations

`InvertibleSheaf X` is the full subcategory of `X.Modules` satisfying
`Langlands.CategoryTheory.TensorInvertible`. Thus an object is an actual
module sheaf `M` together with the proposition that there exists a module
sheaf `N` and an isomorphism `M ⊗ N ≅ 𝟙_ X.Modules`. Morphisms are all
module-sheaf morphisms between these objects; `forget` is the inclusion.

The imported `Modules.TensorMonoidal` supplies the symmetric monoidal
structure. Its unit is definitionally `SheafOfModules.unit X.ringCatSheaf`,
the structure sheaf as a module over itself. Its tensor is identified with
sheafification of the sectionwise tensor by
`Langlands.Scheme.Modules.localizedTensorIso X M N`.
The lemma `tensorInvertible_iff_tensorLeft_isEquivalence X M` specializes
the published categorical `tensorInvertibilityEquivalence` to prove that
this inverse-existence predicate is equivalent to tensoring on the left
being an equivalence, as in Stacks Definition 17.25.1.

`InvertibleSheaf.trivial` is the structure module. `ofIso` transports the
property along a module-sheaf isomorphism. `tensor` uses the actual monoidal
tensor and the proved closure of tensor-invertibility. `inverse` chooses a
witness from the inverse-existence proposition; braiding the chosen
isomorphism proves that this witness is itself tensor-invertible.
`tensorInverseIso` is the chosen isomorphism
`L.obj ⊗ L.inverse.obj ≅ 𝟙_ X.Modules`. This module does not identify the
chosen inverse with the internal-Hom dual.

## The group of classes and its laws

`Group X` is `Langlands.CategoryTheory.PicardGroup X.Modules`, namely
`Additive ((Skeleton X.Modules)ˣ)`. The skeleton is the actual quotient of
module sheaves by existence of an isomorphism. The associator and unitors
make its tensor a monoid, braiding makes it commutative, and its units form
a commutative group. These are the proved Mathlib skeleton/units
constructions specialized by the published categorical Picard module.
Consequently the additive commutative group instance on `Group X` proves
the group laws; no group or laws are input data.

`classOf X L` sends an invertible sheaf to its unit in this skeleton.
`classOf_eq_iff` proves that two such classes are equal exactly when their
underlying module sheaves are isomorphic. `Group.representative X x`
chooses an actual invertible sheaf representing every class, and
`Group.classOf_representative` proves that its class is `x`. Together these
properties characterize the classes as precisely the isomorphism classes
of actual invertible sheaves, even though the implementation takes units
after forming the skeleton of all module sheaves.

`classOf_trivial` identifies the structure sheaf with zero;
`classOf_tensor` identifies tensor product with addition.
`classOf_inverse` identifies the chosen inverse with negation: braiding
followed by `tensorInverseIso` identifies the inverse tensor with the unit,
so the corresponding sum is zero, and the additive group cancellation
lemma gives the required negative.

## Actual pullback

`InvertibleSheaf.pullback f` lifts Mathlib's actual
`Scheme.Modules.pullback f` on objects and morphisms. The imported
`Modules.PullbackMonoidal` supplies its canonical strong monoidal structure,
whose comparisons preserve the tensor-inverse equation. This is the
published categorical `TensorInvertible.map` argument.
`Group.pullback f : Group Y →+ Group X` is the induced homomorphism on
skeleton units. `Group.pullback_classOf` proves that it sends an object's
class to the class of its actual pullback. Identity/composition laws and
the contravariant functor are supplied separately in `Picard.Functor`.

## Universes, provenance and scope

`X.Modules`, `InvertibleSheaf X` and `Group X` lie in `Type (u+1)` for
`X : Scheme.{u}`. The construction does not assert a quotient in `Type u`
or implement the set-smallness refinement in Stacks Lemma 17.25.8.
Representatives here are tensor-invertible sheaves. Their local rank-one
interpretation and the ordinary `LineBundle` inverse interface are handled
using the published comparison in a separate module.

Worker 148 authored this specialization of the published categorical Picard
construction and canonical scheme tensor/pullback. The registered original
is `stacks-local-freeness-invertibility-sections-2026-10-21`, SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
retained file `01CR.html`. Definition 17.25.1, Lemmas 17.25.2 and 17.25.3,
Lemma 17.25.5(1), and Definition 17.25.9 were read directly. They give,
respectively, the equivalence definition, tensor-inverse criterion,
pullback preservation, tensor closure, and the Picard group interpretation.
The chosen inverse and skeleton implementation are internal categorical
constructions realizing those definitions. No claim about dual identification
from Lemma 17.25.5(2) is made here.
