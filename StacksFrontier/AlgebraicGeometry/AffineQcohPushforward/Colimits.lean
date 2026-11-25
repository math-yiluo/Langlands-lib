module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Quasi-coherent modules are closed under colimits

Let `X` be a scheme.  This file proves that the quasi-coherent `𝒪_X`-modules are closed under
colimits of any shape `K` for which the categories of modules over the rings of sections of the
affine opens of `X` have colimits of shape `K`.  In particular a cokernel of a morphism of
quasi-coherent modules is quasi-coherent, and a coproduct of quasi-coherent modules is
quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit_spec` is the
  affine case over a spectrum.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens` is
  the locality of quasi-coherence in the form needed here.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`: the point of a
  colimit cocone of quasi-coherent modules on an arbitrary scheme is quasi-coherent, recorded
  also as the instance
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape`.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel` and
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma` are the two
  specializations that the quasi-coherence theory of a sheaf of algebras uses.

## Implementation notes

The affine case is the whole content, and it is a formal consequence of the structure of
`AlgebraicGeometry.tildeEquiv`.  Quasi-coherence on `Spec R` is the essential image of `~` by
`AlgebraicGeometry.essImage_tilde`, so `tildeEquiv` identifies `ModuleCat R` with the full
subcategory of quasi-coherent modules; a diagram of quasi-coherent modules is therefore
isomorphic to `G ⋙ tilde.functor R` for a diagram `G` of modules, and `~`, being a left
adjoint, carries a colimit of `G` to a colimit of that diagram.  The resulting colimit is in
the image of `~`, hence quasi-coherent.

The passage from the affine case to an arbitrary scheme uses that `restrictFunctor` is a left
adjoint, hence preserves colimits, together with the locality of quasi-coherence.  The locality
statement in the form needed here is assembled from
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations` and
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec`: the former wants
presentations of the restrictions of the module to the members of an open covering, and on an
affine open the latter manufactures one out of quasi-coherence.

No hypothesis of the form `HasColimitsOfShape K X.Modules` is imposed; the statements are about
a colimit cocone that is given, or about `colimit` under a `HasColimit` hypothesis.  What is
assumed is `HasColimitsOfShape K (ModuleCat R)` for the rings `R` that occur, which for the two
shapes used downstream, `WalkingParallelPair` and `Discrete I` with `I : Type u`, is automatic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

namespace Stacks.AlgebraicGeometry.QuasicoherentColimits

variable {K : Type u₂} [Category.{v₂} K]

/-! ### The case of a spectrum -/

/-! ### Locality of quasi-coherence -/

/-- A module on a scheme whose restriction to every affine open is quasi-coherent is
quasi-coherent. -/
theorem isQuasicoherent_of_restrict_affineOpens {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ V : X.affineOpens,
      ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj M).IsQuasicoherent) :
    M.IsQuasicoherent :=
  AffinePushforward.isQuasicoherent_of_presentations M (fun V : X.affineOpens ↦ (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) fun V ↦
      have := h V
      (AffinePushforward.nonempty_presentation_of_isoSpec V.2.isoSpec _).some

/-! ### A scheme isomorphic to a spectrum -/

/-! ### An arbitrary scheme -/

section Scheme

variable [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]

end Scheme

/-! ### The two specializations -/

end Stacks.AlgebraicGeometry.QuasicoherentColimits

end
