/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Closed-immersion right adjoint before restriction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-existence/lem-exc-closed-ambient.md,
node lemma-local-cohomology-right-adjoint--1, order 1803
(blueprint: lemma-local-cohomology-right-adjoint--1).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem closedLowerStar_isLeftAdjoint
    (A : Type (u + 1)) [Ring A] {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).IsLeftAdjoint := by
  let C := ModuleCat.{u + 1} A
  let W : T.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hji : Disjoint (Set.range W.ι.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  let F := lowerStar C i
  let L := upperStar C i
  let J := upperStar C W.ι
  let adj := upperStarLowerStarAdjunction C W.ι
  have : (lowerStar C W.ι).Full :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).full_R_of_isSplitMono_counit_app
  have : (lowerStar C W.ι).Faithful :=
    (openImmersionRestrictionLowerStarAdjunction C W.ι).faithful_R_of_epi_counit_app
  -- Restriction kills the kernel of its unit.
  let K (N : Sheaf T.smallEtaleTopology C) := kernel (adj.unit.app N)
  have hK (N : Sheaf T.smallEtaleTopology C) : IsZero (J.obj (K N)) := by
    have : IsIso (J.map (adj.unit.app N)) := inferInstance
    exact (isZero_kernel_of_mono (J.map (adj.unit.app N))).of_iso
      (PreservesKernel.iso J (adj.unit.app N))
  let adjI := upperStarLowerStarAdjunction C i
  have hunit (N : Sheaf T.smallEtaleTopology C) : IsIso (adjI.unit.app (K N)) :=
    (adjI.isIso_unit_app_iff_mem_essImage).mpr
      (mem_essImage_lowerStar_of_isZero_upperStar i hij (hK N))
  -- Maps out of a closed pushforward vanish after restriction to the open part.
  have hz (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C)
      (f : F.obj M ⟶ N) : f ≫ adj.unit.app N = 0 := by
    apply (adj.homEquiv (F.obj M) (J.obj N)).symm.injective
    exact (isZero_upperStar_lowerStar_of_disjoint_range C W.ι i hji M).eq_of_src _ _
  -- Factor through the kernel, identify it with a closed pushforward, then use fullness.
  let e (M : Sheaf Z.smallEtaleTopology C) (N : Sheaf T.smallEtaleTopology C) :
      (F.obj M ⟶ N) ≃ (M ⟶ L.obj (K N)) :=
    { toFun := fun f ↦ F.preimage
        (kernel.lift (adj.unit.app N) f (hz M N f) ≫ adjI.unit.app (K N))
      invFun := fun g ↦ F.map g ≫ inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N)
      left_inv := by
        intro f
        simp
      right_inv := by
        intro g
        apply F.map_injective
        simp only [Functor.map_preimage]
        rw [← cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))]
        simp }
  have he : ∀ M' M N f g, e M' N (F.map f ≫ g) = f ≫ e M N g := by
    intro M' M N f g
    apply F.map_injective
    simp only [Functor.map_comp]
    apply (cancel_mono (inv (adjI.unit.app (K N)) ≫ kernel.ι (adj.unit.app N))).1
    simp [e]
  exact (Adjunction.adjunctionOfEquivRight e he).isLeftAdjoint

/-- Closed direct image has a right adjoint on the ordinary, unbounded derived categories.
The open complement is canonical and is not extra input to this existence assertion.
Source: blueprint smooth-purity, theorem-existence-exceptional-inverse-image, node order 1803
(blueprint: lemma-local-cohomology-right-adjoint--1).

Proof:
1. For the open complement j put Gamma_Z N = ker(N → j_* j^* N). Geometric-stalk
   conservativity (lemma-weil-pbc-geometric-stalk-conservative) identifies sheaves
   supported on Z with sheaves on Z via the exact fully faithful i_*. Its inverse
   is i^* (def-weil-pbc-inverse-image). Every map i_* M → N factors uniquely through
   Gamma_Z N, giving the sheaf adjunction i_* ⊣ i^* Gamma_Z.
2. Resolve by K-injectives with injective terms
   (prop-weil-pbc-kinjective-resolutions-exist). Since i_* is exact, its right
   adjoint preserves K-injectives: Hom from an acyclic complex stays acyclic by the
   termwise adjunction. Computing derived Hom into those resolutions gives the
   ordinary derived adjunction. Closed i_* is already exact, so its derived functor
   (def-weil-pbc-direct-image) is i_* applied termwise. No constructibility is used. -/
@[instance]
theorem isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion
    (A : Type (u + 1)) [Ring A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    (R(lowerStar (ModuleCat.{u + 1} A) i)).IsLeftAdjoint := by
  let F := lowerStar (ModuleCat.{u + 1} A) i
  have : F.IsLeftAdjoint := closedLowerStar_isLeftAdjoint A i
  let adj := Adjunction.ofIsLeftAdjoint F
  have : F.rightAdjoint.Additive := adj.right_adjoint_additive
  have : F.mapDerivedCategory.IsLeftAdjoint :=
    adj.mapDerivedCategoryRightDerivedAdjunction.isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso F.rightDerivedFunctorIsoMapDerivedCategory.symm

end AlgebraicGeometry.Etale
