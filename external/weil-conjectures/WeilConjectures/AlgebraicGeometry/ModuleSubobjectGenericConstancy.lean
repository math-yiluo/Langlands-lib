/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood

/-! # Generic constancy of module subsheaves -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module subsheaf of a constructible sheaf is finite locally constant on a dense open.
Source: Stacks Project, Tag 09BH, proof of (3), generic-neighbourhood argument
(blueprint: lem-weil-pbc-module-subobject-generic-constancy).

Proof: On a dense open the target is finite locally constant. At each of the finitely
many component generic points, choose an etale trivialization and remove the other
components. The target is a constant finitely generated module M on an irreducible
scheme. Its generic submodule N is finitely generated over the Noetherian ring.
Lift finitely many generators to sections on one pointed etale neighbourhood,
shrinking until their images are the corresponding constant sections of M.
Monicity makes the lifts agree on the fibre product, so etale descent descends them
to its open image. The constant N embeds in the source there. The quotient embeds
in the constant M/N and has zero generic stalk, hence is zero: a nonzero locally
constant germ in a constant sheaf on an irreducible etale neighbourhood would remain
nonzero at its generic point. Thus the source is constant N on that neighbourhood.
Descent gives finite local constancy on an open about each component generic point.
Remove the other components before taking these opens; they are pairwise disjoint.
Their finite union is dense and the source is finite locally constant on it.
For the empty scheme take the empty open; the zero sheaf is also covered. -/
theorem exists_dense_open_of_mono_noetherian
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsConstructibleSheaf G] :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F) := by
  classical
  obtain ⟨U, hU, hG⟩ := IsConstructibleSheaf.exists_dense_open G
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  have : IsNoetherian U.toScheme := ⟨⟩
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F
  let G' := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj G
  let φ' : F' ⟶ G' := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map φ
  have : IsFiniteLocallyConstantSheaf G' := hG
  have : Mono φ' := by dsimp [φ']; infer_instance
  have hfin : IsFiniteSheaf F' := by
    constructor
    intro Ω _ _ s
    have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    exact ConcreteCategory.FinitelyGeneratedOfMono.isFinitelyGenerated_of_mono
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map φ')
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := G') Ω s)
  have hlocal (η : genericPoints U.toScheme) :=
    exists_open_locallyConstant_of_mono_at_genericPoint φ' η.val η.property
  choose V hη hV using hlocal
  have hFV (η : genericPoints U.toScheme) :
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (V η).ι).obj F') := by
    have := hfin
    exact { toIsLocallyConstantSheaf := hV η
            toIsFiniteSheaf := IsFiniteSheaf.upperStar (V η).ι F' }
  let W : U.toScheme.Opens := ⨆ η, V η
  have hW : Dense (W : Set U.toScheme) := by
    apply (dense_iff_closure_eq.mpr (genericPoints.closure (α := U.toScheme))).mono
    intro η hη'
    exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨η, hη'⟩, hη ⟨η, hη'⟩⟩
  have hFW : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) W.ι).obj F') := by
    have hcover (η : genericPoints U.toScheme) : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((Opens.iSupOpenCover V).f η)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) W.ι).obj F')) := by
      have := hFV η
      refine IsFiniteLocallyConstantSheaf.of_iso (F :=
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (V η).ι).obj F') ?_
      exact eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj F')
        (homOfLE_ι U.toScheme (le_iSup V η)).symm) ≪≫
          (Etale.upperStarComp _ ((Opens.iSupOpenCover V).f η) W.ι).app F'
    exact IsFiniteLocallyConstantSheaf.of_openCover (Opens.iSupOpenCover V) _
  let f : W.toScheme ⟶ X := W.ι ≫ U.ι
  have hFf : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) := by
    have : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) W.ι).obj F) := hFW
    exact IsFiniteLocallyConstantSheaf.of_iso
      ((Etale.upperStarComp _ W.ι U.ι).app F).symm
  refine ⟨f.opensRange, ?_, ?_⟩
  · have hd : DenseRange U.ι := by simpa [DenseRange, Opens.range_ι] using hU
    have hd' : DenseRange W.ι := by simpa [DenseRange, Opens.range_ι] using hW
    exact hd.comp hd' U.ι.continuous
  · have := hFf
    apply IsFiniteLocallyConstantSheaf.upperStar_of_range_subset f.opensRange.ι f _ F
    simp [Opens.range_ι, Hom.coe_opensRange]


end AlgebraicGeometry.Scheme
