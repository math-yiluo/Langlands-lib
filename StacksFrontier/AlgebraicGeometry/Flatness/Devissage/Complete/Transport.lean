module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.FieldTheory.MvRatFunc.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.Topology.Dimension.Krull

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Transporting the data of a dévissage

This file collects the comparisons used to move the data of a one-step dévissage, and of a
stage of a complete dévissage, along an isomorphism of the source and along a cartesian
square: the inverse image of a free module, the invariance of the support of a module under
an isomorphism, the comparison of the fibres of the two vertical morphisms of a cartesian
square, the behaviour of generic points under continuous surjections and open embeddings, and
the dévissage data carried along an isomorphism of the source over the base.

It also carries a whole complete dévissage along an isomorphism of the source over the base and
along an isomorphism of the base matching the base points. The first of the two leaves every
stage but the first untouched, because a later stage dévisses a cokernel on the smooth scheme of
its predecessor, which the transport does not move; the second changes every stage, since the
structure morphism of each smooth scheme is composed with the inverse of the isomorphism, and is
therefore a recursion down the chain.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`: the inverse image of the free module on
  `I` is the free module on `I`.
* `AlgebraicGeometry.fiberMapOfIsPullback`: for a cartesian square with vertical morphisms
  `g'` and `g` and lower horizontal morphism `h`, the morphism `g'.fiber s' ⟶ g.fiber (h s')`
  of scheme-theoretic fibres.
* `AlgebraicGeometry.Scheme.Modules.pushforwardInvIsoPullback`: the direct image along the
  inverse of an isomorphism is the inverse image along the isomorphism.
* `AlgebraicGeometry.fiberIsoOfSourceIso` and
  `AlgebraicGeometry.fiberSupportHomeoOfSourceIso`: the fibres, and the supports of the
  modules on them, carried along an isomorphism of the source over the base.
* `AlgebraicGeometry.OneStepDevissage.ofSourceIso`,
  `AlgebraicGeometry.OneStepDevissageAt.ofSourceIso` and
  `AlgebraicGeometry.DevissageStage.ofSourceIso`: a one-step dévissage, a one-step dévissage
  at a point, and a stage of a complete dévissage, carried along an isomorphism of the source
  over the base.
* `AlgebraicGeometry.OneStepDevissageAt.ofModuleIso` and
  `AlgebraicGeometry.OneStepDevissageAt.ofClosedModuleIso`: a one-step dévissage at a point
  carried along an isomorphism of the module being dévissed, and along an isomorphism of the
  module on the closed subscheme.
* `AlgebraicGeometry.OneStepDevissage.ofModuleIso` and
  `AlgebraicGeometry.DevissageStage.ofModuleIso`: a one-step dévissage and a stage of a complete
  dévissage, carried along an isomorphism of the module being dévissed.
* `AlgebraicGeometry.DevissageChain.ofSourceIso`,
  `AlgebraicGeometry.PointedDevissageStage.ofSourceIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofSourceIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofSourceIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofSourceIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofSourceIso`: a whole complete dévissage carried along
  an isomorphism of the source over the base, and along one matching a chosen point of the new
  source with the point the dévissage is taken at. Only the first stage of the chain changes,
  since every later stage dévisses a cokernel on the smooth scheme, which the transport leaves
  untouched.
* `AlgebraicGeometry.suppPullbackHomeoOfIso`: the supports of the two inverse images of a
  module along two morphisms whose sources are identified over the common target.
* `AlgebraicGeometry.fiberIsoOfBaseIso` and `AlgebraicGeometry.fiberIsoOfBaseIsoPoint`: the
  fibre of a morphism over a point of the base, carried along an isomorphism of the base.
* `AlgebraicGeometry.OneStepDevissage.ofBaseIso`,
  `AlgebraicGeometry.OneStepDevissageAt.ofBaseIso` and
  `AlgebraicGeometry.DevissageStage.ofBaseIso`: a one-step dévissage, a one-step dévissage at a
  point, and a stage of a complete dévissage, carried along an isomorphism of the base.
* `AlgebraicGeometry.DevissageChain.ofBaseIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofBaseIso`,
  `AlgebraicGeometry.PointedDevissageStage.ofBaseIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofBaseIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofBaseIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofBaseIso`: a whole complete dévissage carried along
  an isomorphism of the base, with new structure morphism `f ≫ d.inv`.
* `AlgebraicGeometry.DevissageChain.ofBaseIsoHom`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofBaseIsoHom`,
  `AlgebraicGeometry.PointedDevissageChain.ofBaseIsoHom`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofBaseIsoHom` and
  `AlgebraicGeometry.CompleteDevissageAt.ofBaseIsoHom`: the same, with the structure morphism
  over the new base prescribed by any `f' : X ⟶ S'` with `f' ≫ d.hom = f`.
* `AlgebraicGeometry.DevissageChain.ofModuleIso`,
  `AlgebraicGeometry.PointedDevissageChain.ofModuleIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissage.ofModuleIso`,
  `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofModuleIso` and
  `AlgebraicGeometry.CompleteDevissageAt.ofModuleIso`: a whole complete dévissage carried along
  an isomorphism of the module being dévissed. Only the first stage of the chain changes, since
  every later stage dévisses a cokernel which the transport leaves untouched.

## Main results

* `SheafOfModules.mem_supp_iff_of_iso`: a point lies in the support of a module on a scheme
  exactly when it lies in the support of any isomorphic module.
* `SheafOfModules.isFiniteType_of_iso`, `SheafOfModules.isQuasicoherent_of_iso` and
  `Stacks.Modules.isQuasicoherent_pullback`: the two finiteness conditions under isomorphism
  and under inverse image.
* `AlgebraicGeometry.surjective_fiberMapOfIsPullback` and
  `AlgebraicGeometry.fiberMapOfIsPullback_genericPoint`: the comparison of fibres attached to
  a cartesian square is surjective and carries the generic point to the generic point.
* `IsGenericPoint.map_eq_of_surjective` and `IsGenericPoint.map_eq_of_isOpenEmbedding`: a
  continuous surjection, and an open embedding into an irreducible space, carry the generic
  point to the generic point.
* `AlgebraicGeometry.isIso_pullback_map_fromSpecResidueField`: a morphism of modules which
  becomes invertible over the residue field of the image of a point has an inverse image
  which becomes invertible over the residue field of that point.
* `topologicalKrullDimAt_congr`: the local dimension of a subspace at a point depends only on
  the underlying subset.
* `AlgebraicGeometry.supp_pullback_eq_preimage_of_iso`,
  `AlgebraicGeometry.topologicalKrullDim_supp_pullback_of_iso` and
  `AlgebraicGeometry.topologicalKrullDimAt_supp_pullback_of_iso`: the support of the inverse
  image of a module, its dimension and its local dimension depend on the morphism only up to an
  isomorphism of its source over the target.
* `AlgebraicGeometry.DevissageStage.ofSourceIso_coker`: the cokernel of the free-module map of a
  stage is unchanged by the transport along an isomorphism of the source.
* `AlgebraicGeometry.PointedDevissageStage.g_y`: the distinguished point of the smooth scheme of
  a pointed stage lies over the base point of the dévissage.
* `AlgebraicGeometry.topologicalKrullDim_fiber_of_baseIso`,
  `AlgebraicGeometry.topologicalKrullDim_fiberSupport_of_baseIso` and
  `AlgebraicGeometry.topologicalKrullDimAt_fiberSupport_of_baseIso`: the dimension of a fibre,
  the dimension of the support of the module on it and that dimension taken locally at a point
  are unchanged by an isomorphism of the base.
* `AlgebraicGeometry.purelyTranscendental_residueField_of_baseIso`: the pure transcendence of
  the residue field of the distinguished point of the smooth scheme over the residue field of
  the base point survives an isomorphism of the base.
* `AlgebraicGeometry.mem_fiberSupport_iff_mem_fiberSupport`: whether a point lies in the support
  of the module on its fibre does not depend on the morphism to the base.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` is Mathlib's
`SheafOfModules.pullbackObjFreeIso` for the ring-sheaf morphism induced by a morphism of
schemes; it is given a name because the two instances its Mathlib form requires — the right
adjointness of the direct image and the finality of the inverse-image functor on opens — are
always available for a morphism of schemes, and supplying them at every use obscures the
statements.

The comparison of fibres attached to a cartesian square is the canonical morphism of fibre
products: a fibre is the fibre product with the spectrum of the residue field of the base
point, and the square induces a map of those data. It is surjective because it is, up to the
cartesian square of the fibres over the residue fields, a base change of a morphism between
spectra of fields.

Carrying a one-step dévissage along an isomorphism `e` of the source changes only the closed
immersion, which is composed with `e.inv`; the closed subscheme, the smooth scheme, the
finite and smooth morphisms and the module on the closed subscheme are unchanged, and the
projections of the construction are therefore definitional. The identification of the module
is composed with the affine base-change isomorphism of the square exhibiting `e` as an
isomorphism over the source, and the fibre-dimension condition is transported by the
homeomorphism of fibre supports.

The structure morphism produced by the transport along an isomorphism `d` of the base is
`f ≫ d.inv` rather than an arbitrary `f' : X ⟶ S'` with `f' ≫ d.hom = f`. The two differ by the
identity isomorphism of the source, so the `ofBaseIsoHom` family is the `ofBaseIso` family
followed by `AlgebraicGeometry.DevissageChain.ofSourceIso` for `Iso.refl`; prescribing the
morphism in the recursion instead would make the structure morphism of every stage a parameter
of it, and the recursion is what the base transport is for.

The comparison of the fibres under an isomorphism of the base is the canonical morphism of
fibre products attached to the cartesian square exhibiting `f ≫ d.inv` as the base change of
`f` along `d.hom`; it is an isomorphism because its three components are. Every clause of a
one-step dévissage except the fibre-dimension condition is carried by it formally, and that
condition is carried by the resulting homeomorphism of fibre supports. The pure transcendence
of the residue field at the distinguished point is the one clause of a one-step dévissage *at a
point* whose base field changes: the two algebra structures on `Y.residueField y` differ by the
residue-field isomorphism induced by `d`, and
`Stacks.Flatness.purelyTranscendental_of_ringEquiv_base` transports pure transcendence along
exactly such a change of base field.

`SheafOfModules.isFiniteType_of_iso`, `SheafOfModules.isQuasicoherent_of_iso` and
`Stacks.Modules.isQuasicoherent_pullback` are the specializations to modules on a scheme of
results stated over a general site or ringed space; they exist because those results have
universe parameters in front of their instance arguments, or are stated for the ringed-space
inverse image, so that neither applies without help at a scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

/-! ### Free modules -/

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules

namespace SheafOfModules

end SheafOfModules

/-! ### Local dimension -/

/-! ### Supports -/

namespace SheafOfModules

/-! ### Finiteness and quasi-coherence -/

end SheafOfModules

/-! ### Generic points -/

/-! ### Fibres of a cartesian square -/

namespace AlgebraicGeometry

variable {Y Y' S S' : Scheme.{u}} {pY : Y' ⟶ Y} {g' : Y' ⟶ S'} {g : Y ⟶ S} {h : S' ⟶ S}

/-! ### Supports under a comparison of the sources -/

/-! ### Isomorphisms of the source -/

section SourceIso

variable {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} {F : X.Modules} {F' : X'.Modules}

/-- An isomorphism `e : X' ≅ X` over `S` induces an isomorphism of the fibres over any point
of `S`. -/
def fiberIsoOfSourceIso (e : X' ≅ X) (he : e.hom ≫ f = f') (t : S) :
    f'.fiber t ≅ f.fiber t := by
  let m : f'.fiber t ⟶ f.fiber t :=
    pullback.map f' (S.fromSpecResidueField t) f (S.fromSpecResidueField t)
      e.hom (𝟙 _) (𝟙 S) (by simp only [Category.comp_id]; exact he.symm) (by simp)
  haveI : IsIso m := by
    change IsIso (pullback.map f' (S.fromSpecResidueField t) f (S.fromSpecResidueField t)
      e.hom (𝟙 _) (𝟙 S) _ _)
    infer_instance
  exact asIso m

variable [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]

end SourceIso

/-! ### Isomorphisms of the source of a complete dévissage -/

section ChainSourceIso

variable {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} {F : X.Modules} {F' : X'.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent] [ht' : F'.IsFiniteType]

end ChainSourceIso

/-! ### Isomorphisms of the modules -/

section ModuleIso

variable {X S : Scheme.{u}} {f : X ⟶ S} {F F' : X.Modules} [LocallyOfFiniteType f]
  [F.IsQuasicoherent] [F.IsFiniteType] [F'.IsQuasicoherent] [F'.IsFiniteType]

end ModuleIso

/-! ### Isomorphisms of the module of a complete dévissage -/

section ChainModuleIso

variable {X S : Scheme.{u}} {s : S} {f : X ⟶ S} {F F' : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hq' : F'.IsQuasicoherent] [ht' : F'.IsFiniteType]

end ChainModuleIso

/-! ### Fibres under an isomorphism of the base -/

section Fiber

variable {X S S' : Scheme.{u}} {f : X ⟶ S} {f' : X ⟶ S'}

end Fiber

/-! ### Residue fields under an isomorphism of the base -/

/-! ### One-step dévissages under an isomorphism of the base -/

section OneStep

variable {X S S' : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]

end OneStep

/-! ### Complete dévissages under an isomorphism of the base -/

section Chain

variable {S S' : Scheme.{u}} {s : S} {s' : S'}

end Chain

/-! ### Isomorphisms of the base with a prescribed structure morphism -/

section BaseIsoHom

variable {X S S' : Scheme.{u}} {s : S} {s' : S'} {f : X ⟶ S} {f' : X ⟶ S'} {F : X.Modules}
  [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType]
  [hl' : LocallyOfFiniteType f']

end BaseIsoHom

end AlgebraicGeometry

end
