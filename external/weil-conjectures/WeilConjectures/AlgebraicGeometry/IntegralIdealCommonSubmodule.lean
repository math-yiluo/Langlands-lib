/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.RankOneGenericIdealInclusion
import WeilConjectures.AlgebraicGeometry.IntegralIdealsCommonGenericLattice
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A common submodule with generically vanishing cokernels

Source: Stacks Project, Cohomology of Schemes, Tag 01YH,
`lemma-property-irreducible`, proof, generic ideal inclusion and ideal intersection.
(blueprint: lem-pc-a2-integral-ideal-common-submodule)
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module with finitely presented sections on every affine open
is finitely presented. No Noetherian or coherence hypothesis is required. -/
private theorem finitePresentation_of_affine_sections (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hF : ∀ U : X.affineOpens, Module.FinitePresentation Γ(X, U.1) Γ(F, U.1)) :
    F.IsFinitePresentation := by
  have (U : X.affineOpens) : (F.over U.1).IsFinitePresentation := by
    exact (((quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1
      U.1 U.2).2.mpr (hF U)
  exact SheafOfModules.IsFinitePresentation.of_coversTop F (fun U : X.affineOpens ↦ U.1)
    ((Opens.coversTop_iff X _).mpr
      (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)))

/-- A generically surjective map to a sheaf supported in S has cokernel support
strictly inside S whenever the chosen point belongs to S. -/
private theorem cokernel_support_ssubset (X : Scheme.{u}) {K F : X.Modules}
    (f : K ⟶ F) (S : Set X) (ξ : X) (hξ : ξ ∈ S)
    (hF : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆ S)
    (hf : Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map f)) :
    {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊂ S := by
  have qsurj (x : X) : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (cokernel.π f)) := by
    have : Epi ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
      (cokernel.π f)) := ((RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x).1
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hQξ : Subsingleton ((cokernel f).presheaf.stalk ξ) := by
    have hz (v : (cokernel f).presheaf.stalk ξ) : v = 0 := by
      obtain ⟨v', rfl⟩ := qsurj ξ v
      obtain ⟨v'', rfl⟩ := hf v'
      have hc := congrArg (fun g ↦ g v'')
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_comp f (cokernel.π f))
      rw [cokernel.condition, Functor.map_zero] at hc
      exact hc.symm
    exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩
  have hsub : {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊆ S := by
    intro x hx
    apply hF
    intro hFx
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := hFx
    exact hx ((qsurj x).subsingleton)
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have : ξ ∈ {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} := by
    rw [heq]
    exact hξ
  exact this hQξ

-- The residue-field instance is used implicitly by finrank.
set_option linter.unusedVariables false in
/-- A nonzero ideal pushforward and a coherent module of generic rank one admit
monomorphisms from a common module, with coherent cokernels of strictly smaller support.
No filtration is asserted here.

Source: Stacks Project, Cohomology of Schemes, Tag 01YH,
`lemma-property-irreducible`, proof, paragraphs beginning "Let G" and "Next, suppose".
(blueprint: lem-pc-a2-integral-ideal-common-submodule)

Proof: The closed subscheme W of the Noetherian X is Noetherian. Every quasi-coherent
ideal on W is coherent, since its affine section modules are ideals in Noetherian
rings, and closed pushforward preserves coherence. The nonzero pushforward hypothesis
implies I is nonzero. Apply the coherent generic-point ideal inclusion to G. On the
generic stalk it identifies G with a finite sum of copies of the generic stalk of an
ideal J. G has dimension one over the residue field, so J is nonzero and the number
of summands is one. Thus obtain a monomorphism i_*J into G which is an isomorphism
near the generic point. The intersection L = I inf J is a quasi-coherent ideal. On
any nonempty affine open both ideals contain nonzero elements, whose product is
nonzero in the domain and belongs to L. Hence L is nonzero, and the generic stalks
of L, I and J are the full generic field. Set K = i_*L and take its inclusion into
i_*I and its inclusion into i_*J followed by the map into G. Both are monomorphisms.
Their sources and targets are coherent, so their cokernels are coherent and
finitely presented on the locally Noetherian scheme X. Exactness
of stalks and the generic stalk identifications make both cokernels zero at the image
of genericPoint W; outside i(W) all source and target stalks are zero. Each cokernel's
support is therefore contained in i(W) but omits its generic point, giving strict
inclusion. The argument also covers zero cokernels, whose supports are empty. -/
theorem exists_integral_ideal_common_submodule (X W : Scheme.{u})
    [IsNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hGann : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0)
    (hGrank : ∃ inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
        = 1)
    (I : W.IdealSheafData) (hI : ¬ IsZero ((pushforward i).obj I.toModules)) :
    ∃ (K : X.Modules) (a : K ⟶ G) (d : K ⟶ (pushforward i).obj I.toModules),
      Mono a ∧ Mono d ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel a) ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel d) ∧
      (cokernel a).IsFinitePresentation ∧ (cokernel d).IsFinitePresentation ∧
      {x : X | ¬ Subsingleton ((cokernel a).presheaf.stalk x)} ⊂ Set.range i.base ∧
      {x : X | ¬ Subsingleton ((cokernel d).presheaf.stalk x)} ⊂ Set.range i.base  := by
  classical
  obtain ⟨J, hJ, α, hα, hαξ⟩ :=
    rank_one_generic_ideal_inclusion i G hGcoh hGann hGrank
  have : Mono α := hα
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    (i.base (genericPoint W))).map α) := hαξ
  obtain ⟨K, b, d, hIpcoh, hK, hb, hd, hbξ, hdξ⟩ :=
    integral_ideals_common_generic_lattice i I J hI hJ
  have : Mono b := hb
  have : Mono d := hd
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    (i.base (genericPoint W))).map b) := hbξ
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    (i.base (genericPoint W))).map d) := hdξ
  let a : K ⟶ G := b ≫ α
  have ha : Mono a := inferInstanceAs (Mono (b ≫ α))
  have haξ : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).map a) := by
    dsimp only [a]
    rw [Functor.map_comp]
    exact (ConcreteCategory.bijective_of_isIso
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map α)).2.comp
      (ConcreteCategory.bijective_of_isIso
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map b)).2
  have hQa := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
    K G hK hGcoh).1 a |>.2
  have hQd := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
    K ((pushforward i).obj I.toModules) hK hIpcoh).1 d |>.2
  have : (cokernel a).IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hQa).1
  have : (cokernel d).IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hQd).1
  have hQafp : (cokernel a).IsFinitePresentation :=
    finitePresentation_of_affine_sections X _ fun U ↦ by
      have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      have : Module.Finite Γ(X, U.1) Γ(cokernel a, U.1) :=
        coherent_affine_sections_finite X _ hQa U.1 U.2
      exact Module.finitePresentation_of_finite Γ(X, U.1) Γ(cokernel a, U.1)
  have hQdfp : (cokernel d).IsFinitePresentation :=
    finitePresentation_of_affine_sections X _ fun U ↦ by
      have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      have : Module.Finite Γ(X, U.1) Γ(cokernel d, U.1) :=
        coherent_affine_sections_finite X _ hQd U.1 U.2
      exact Module.finitePresentation_of_finite Γ(X, U.1) Γ(cokernel d, U.1)
  refine ⟨K, a, d, ha, hd, hQa, hQd, hQafp, hQdfp, ?_, ?_⟩
  · exact cokernel_support_ssubset X a (Set.range i.base) (i.base (genericPoint W))
      ⟨genericPoint W, rfl⟩ (by rw [hGsupp]) haξ
  · apply cokernel_support_ssubset X d (Set.range i.base) (i.base (genericPoint W))
      ⟨genericPoint W, rfl⟩
    · intro x hx
      by_contra hxout
      exact hx ((closedImmersion_pushforward_stalks i i.isClosedEmbedding I.toModules).1
        x hxout)
    · exact (ConcreteCategory.bijective_of_isIso
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map d)).2



end AlgebraicGeometry.Scheme.Modules
