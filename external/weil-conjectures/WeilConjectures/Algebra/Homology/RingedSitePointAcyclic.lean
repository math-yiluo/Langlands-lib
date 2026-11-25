/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSitePointExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Detection of acyclicity by a conservative family of module stalks -/

@[expose] public section
set_option autoImplicit false
universe u v w t
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.RingedSitePoint

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}

private theorem jointlyReflectModules
    {I : Type t} (p : I → GeometricMorphism (Type w) (Sheaf J (Type w)))
    (s : ∀ i : I, RingedSitePoint R (p i))
    (hp : JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse)) :
    JointlyReflectIsomorphisms (fun i : I ↦ (s i).modules) := by
  let U := SheafOfModules.toSheaf.{w} ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})
  constructor
  intro M N f hf
  have (i : I) : IsIso ((p i).inverse.map (U.map f)) := by
    have he : (p i).inverse.map (U.map f) =
        (s i).moduleUnderlying.inv.app M ≫
          (forget (ModuleCat.{w} (s i).ring)).map ((s i).modules.map f) ≫
            (s i).moduleUnderlying.hom.app N := by
      simpa [U] using
        ((s i).moduleUnderlying.inv.naturality f =≫ (s i).moduleUnderlying.hom.app N)
    rw [he]
    infer_instance
  have : IsIso (U.map f) := hp.isIso _
  exact isIso_of_reflects_iso f U

/-- A conservative family of topos points detects acyclicity of module complexes,
including when the family is empty.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0DEN.
(auxiliary; not a blueprint node)

Proof: exactness of each module inverse image preserves the homology of every
consecutive triple. Conversely, vanishing of these images of homology makes the map
from homology to zero an isomorphism at each point. The prescribed underlying-set
comparisons transfer this to the given conservative family on set sheaves. Forgetting
module structure reflects isomorphisms. Thus the original homology is zero. The proof
uses no selected member of the family. -/
theorem acyclic_iff
    {I : Type t} (p : I → GeometricMorphism (Type w) (Sheaf J (Type w)))
    (s : ∀ i : I, RingedSitePoint R (p i))
    (hp : JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse))
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    K.Acyclic ↔ ∀ i : I,
      (((s i).modules.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  constructor
  · intro h i n
    have he := (exactFunctor_iff _).1 ((s i).exact)
    have : PreservesFiniteLimits (s i).modules := he.1
    have : PreservesFiniteColimits (s i).modules := he.2
    exact (h n).map (s i).modules
  · intro h n
    let H := (K.sc n).homology
    have hi (i : I) : IsIso ((s i).modules.map
        (0 : H ⟶ (0 : SheafOfModules.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)))) := by
      have he := (exactFunctor_iff _).1 ((s i).exact)
      have : PreservesFiniteLimits (s i).modules := he.1
      have : PreservesFiniteColimits (s i).modules := he.2
      have hh : ((K.sc n).map (s i).modules).Exact := h i n
      have hz : IsZero ((s i).modules.obj H) :=
        ((ShortComplex.exact_iff_isZero_homology _).1 hh).of_iso
          ((K.sc n).mapHomologyIso (s i).modules).symm
      rw [Functor.map_zero]
      exact (isIsoZero_iff_source_target_isZero _ _).2
        ⟨hz, (s i).modules.map_isZero (isZero_zero _)⟩
    have := (jointlyReflectModules p s hp).isIso
      (0 : H ⟶ (0 : SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)))
    exact (ShortComplex.exact_iff_isZero_homology _).2
      ((isIsoZero_iff_source_target_isZero _ _).1 this).1

end CategoryTheory.RingedSitePoint
