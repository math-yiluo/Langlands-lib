/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyMono
import WeilConjectures.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyEpi

/-! # Unbounded section comparison from affine-basis acyclicity

Source: Stacks Project, Tag 08C2, singleton-cover case on an affine open.
(blueprint: lem-sc-affine-basis-sections-derived-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The three affine-basis acyclicity conditions make the ordinary-to-derived
section comparison invertible for an unbounded complex. No quasi-coherence is assumed.
Source: Stacks Project, Tag 08C2, conditions (3)(a), (3)(b), (3)(c).
(blueprint: lem-sc-affine-basis-sections-derived-unit).

Proof: Restrict the complex to V. Affine opens W contained in V form a basis,
and include V itself, so use the singleton covering of V by V in 08C2.
The hypotheses give positive cohomology vanishing for the terms, differential
cokernels and cohomology sheaves on every basis member. For a bounded-below
complex, the acyclic Cech comparison computes derived sections. For an unbounded
complex use the good truncations in degrees at least -m: cokernel vanishing
makes each truncation satisfy the bounded-below hypothesis. Cohomology-sheaf
vanishing provides the compatible K-injective resolution tower of Tag 071B.
In each fixed degree the section cohomology of the singleton Cech complexes
stabilizes. The Mittag-Leffler calculation identifies the cohomology of the
inverse-limit section complex with that value. The comparison is the canonical
ordinary-to-derived map, hence the displayed derived unit. Finally, restriction
of a K-injective complex to V remains K-injective (08BS), identifying derived
sections after restriction with the derived functor of evaluation on X. The
module comparison is detected after forgetting scalars to abelian groups;
injective module sheaves are flasque and hence section-acyclic as abelian sheaves.
Empty V has zero section complexes, so its comparison is invertible as well. -/
theorem affineBasisSections_isIso_derivedUnit
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F : CochainComplex X.Modules ℤ)
    [HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V)))]
    (hterms : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.X n).restrict W.ι).H (q + 1)))
    (hcokernels : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict W.ι).H (q + 1)))
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    IsIso (S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj F)) := by
  dsimp
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let : IsGrothendieckAbelian.{u} X.Modules :=
    RingedSpace.moduleGrothendieckAbelian X.toRingedSpace
  obtain ⟨J, hJ, i, _, hi⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective F
  let := hJ
  let := hi
  have hS : QuasiIso ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := by
    apply (quasiIso_iff _).mpr
    intro n
    apply (quasiIsoAt_iff_isIso_homologyMap _ n).mpr
    let := affineBasisSections_resolution_homology_mono X V hV F J i
      hterms hcokernels hhomology n
    let := affineBasisSections_resolution_homology_epi X V hV F J i
      hterms hcokernels hhomology n
    exact isIso_of_mono_of_epi _
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  have hQi : IsIso (DerivedCategory.Qh.map (Q.map i)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hi
  have hSi : IsIso (((S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).map (Q.map i))) := by
    change IsIso (DerivedCategory.Qh.map
      ((S.mapHomotopyCategory (ComplexShape.up ℤ)).map (Q.map i)))
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hS
  let := hQi
  let := hSi
  have : IsIso ((DerivedCategory.Qh ⋙ S.rightDerivedFunctor).map (Q.map i)) := by
    change IsIso (S.rightDerivedFunctor.map (DerivedCategory.Qh.map (Q.map i)))
    infer_instance
  have hnat := S.rightDerivedFunctorUnit.naturality (Q.map i)
  have hcomp : IsIso (S.rightDerivedFunctorUnit.app (Q.obj F) ≫
      (DerivedCategory.Qh ⋙ S.rightDerivedFunctor).map (Q.map i)) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Qh ⋙ S.rightDerivedFunctor).map (Q.map i))

end AlgebraicGeometry
