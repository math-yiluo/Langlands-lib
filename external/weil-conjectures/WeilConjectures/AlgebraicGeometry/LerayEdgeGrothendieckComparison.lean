/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LerayEdgeCocycleData
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.LeraySectionsResolutionComparison

/-! # Comparison of the cocycle Leray edge with the Grothendieck edge

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX
(blueprint: lem-pc-leray-edge-grothendieck-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Compare two maps on classes by unique lifts of cycles through a monomorphism. -/
private theorem moduleCocycleComparison
    {R S : Type u} [Ring R] [Ring S] {A B : ModuleCat.{u} R}
    {Z W V C : ModuleCat.{u} S} (p : A ⟶ B) [Epi p]
    (a : (forget₂ _ AddCommGrpCat).obj B ⟶ (forget₂ _ AddCommGrpCat).obj C)
    (e : (forget₂ _ AddCommGrpCat).obj B ⟶ (forget₂ _ AddCommGrpCat).obj V)
    (edge : V ⟶ C) (i : Z ⟶ W) [Mono i] (r : Z ⟶ C) (t : Z ⟶ V)
    (restrict : A → W)
    (ha : ∀ s, ∃ z, restrict s = i z ∧ a (p s) = r z)
    (he : ∀ s, ∃ z, restrict s = i z ∧ e (p s) = t z)
    (ht : t ≫ edge = r) : a = e ≫ (forget₂ _ AddCommGrpCat).map edge := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨s, rfl⟩ := (ModuleCat.epi_iff_surjective p).mp inferInstance x
  obtain ⟨z, hz, haz⟩ := ha s
  obtain ⟨z', hz', hez⟩ := he s
  have hzz : z = z' := (ModuleCat.mono_iff_injective i).mp inferInstance
    (hz.symm.trans hz')
  subst z'
  change a (p s) = edge (e (p s))
  rw [haz, hez]
  exact (CategoryTheory.congr_fun ht z).symm

-- Comparing resolution maps unfolds composed module and forgetful functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Comparison of the edge on module cohomology with the abstract Grothendieck edge.
There is no vanishing assumption: this is only the resolution comparison and
identification of the edge, not the degeneration assertion.

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.
(blueprint: lem-pc-leray-edge-grothendieck-comparison)

Proof: For the supplied acyclicity witness `hFG`, use the canonical Grothendieck
edge of direct image followed by global sections. Sections of the direct image
at the whole space
are sections on X, restricted along the equality of the inverse image of the
whole space with the whole space. This gives a natural isomorphism of the
underlying additive sections functors. Apply it termwise to an injective
resolution, take homology, and compare with the right derived functors to obtain
`e`. The generic Grothendieck edge is described by its map from cycles to
cohomology (Tag 01F2). Every class is represented by a global cycle, since the
cycles-to-homology map is an epimorphism in modules. Its lift to the cycle sheaf
is unique: the cycle inclusion is monic and sections preserve monomorphisms.
Applying the cocycle characterization to this same lift shows equality of the
two edge values on every class. This proves the displayed equality. -/
theorem leray_edge_grothendieck_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ε : LerayEdge X Y f) (hε : LerayEdgeCocycle f ε) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
    letI : PreservesFiniteLimits G := inferInstanceAs
      (PreservesFiniteLimits
        (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    ∀ hFG : D.IsAcyclicComposablePair G,
      ∃ e : ∀ q : ℕ,
        (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
          ((D ⋙ G).rightDerived q ⋙ forget₂ _ AddCommGrpCat),
      ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        (ε q).app F = (e q).hom.app F ≫
          (forget₂ _ AddCommGrpCat).map ((D.grothendieckLeftEdgeMap G hFG q).app F) := by
  classical
  -- Share the category structures throughout the resolution comparison.
  let _ : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let _ : Abelian (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let _ : Abelian (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
    inferInstance
  let _ : Abelian (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) :=
    inferInstance
  dsimp only
  intro hFG
  let grothX := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  let grothY := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let derivedX := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let derivedY := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let derivedM := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits D := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
    infer_instance
  let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let : PreservesFiniteLimits G := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  obtain ⟨e, he⟩ := leray_sections_resolution_comparison f
  refine ⟨e, ?_⟩
  intro q F
  let I := injectiveResolution F
  let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T := ((D ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  obtain ⟨c, hc, hcπ⟩ := (grothendieck_left_edge_cocycle D G hFG F I).1 q
  apply moduleCocycleComparison
    ((RingedSpace.globalSectionsComplex I).homologyπ q ≫
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv)
    ((ε q).app F) ((e q).hom.app F) ((D.grothendieckLeftEdgeMap G hFG q).app F)
    (G.map (K.iCycles q))
    (G.map (K.homologyπ q) ≫ G.map (I.isoRightDerivedObj D q).inv)
    (c ≫ T.homologyπ q ≫ (I.isoRightDerivedObj (D ⋙ G) q).inv)
    (fun s ↦ (I.cocomplex.X q).val.presheaf.map
      (eqToHom (congrArg op (Opens.map_top f.base).symm))
      ((RingedSpace.globalSectionsComplex I).iCycles q s))
  · intro s
    obtain ⟨z, hz, hεz⟩ := hε q F I K rfl s
    refine ⟨z, ?_, ?_⟩
    · simpa only [eqToHom_refl, HomologicalComplex.id_f, Category.comp_id] using hz
    · dsimp only [D, G]
      simpa only [eqToHom_refl, HomologicalComplex.homologyMap_id, Category.id_comp,
        Functor.map_comp, ConcreteCategory.comp_apply] using! hεz
  · intro s
    obtain ⟨z, hz, hez⟩ := he q F I s
    exact ⟨z, hz, hez c hc⟩
  · have heq := congrArg (fun a ↦ a ≫ G.map (I.isoRightDerivedObj D q).inv) hcπ
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id] at heq
    erw [Category.comp_id] at heq
    exact heq

end AlgebraicGeometry
