/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Exactness of module stalks at a topos point -/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedSitePoint

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
  {p : GeometricMorphism (Type w) (Sheaf J (Type w))}

/-- Module inverse image at a topos point is exact.
Source: Stacks Project, Modules on Sites, Tag 05V3.
(auxiliary; not a blueprint node)

Proof: underlying sheaves of sets detect finite limits of modules. The prescribed
underlying functor is inverse image composed with forgetting module structure, hence
preserves finite limits. A module-sheaf epimorphism is locally surjective on underlying
sets. It is therefore an epimorphism of set sheaves; the left adjoint inverse image
preserves it. Surjectivity of the resulting set map implies that the module map is
epi. An additive functor between abelian categories preserving kernels and epis is exact. -/
theorem exact (s : RingedSitePoint R p) : exactFunctor _ _ s.modules := by
  let := SheafOfModules.hasSheafify_coefficientUniverse (J := J)
  let := SheafOfModules.wEqualsLocallyBijective_coefficientUniverse (J := J)
  let U := SheafOfModules.toSheaf.{w} ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})
  have : PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
    have : PreservesFiniteLimits
        (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
    (moduleSheaves_colimits_forgetful _).2.2.1
  have : PreservesFiniteLimits U := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : PreservesFiniteLimits (U ⋙ p.inverse) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (s.modules ⋙ forget (ModuleCat.{w} s.ring)) :=
    preservesFiniteLimits_of_natIso s.moduleUnderlying.symm
  have : PreservesFiniteLimits s.modules :=
    preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{w} s.ring))
  have : PreservesColimits p.inverse := p.adj.leftAdjoint_preservesColimits
  have : s.modules.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map f) :=
      (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{w} _).2 inferInstance
    have : Sheaf.IsLocallySurjective (U.map f) := by
      dsimp [U]
      infer_instance
    have : Epi (U.map f) := Sheaf.epi_of_isLocallySurjective' _
    have : Epi ((U ⋙ p.inverse).map f) :=
      inferInstanceAs (Epi (p.inverse.map (U.map f)))
    have : Epi ((s.modules ⋙ forget (ModuleCat.{w} s.ring)).map f) := by
      rw [show (s.modules ⋙ forget (ModuleCat.{w} s.ring)).map f =
        s.moduleUnderlying.hom.app M ≫ (U ⋙ p.inverse).map f ≫
          s.moduleUnderlying.inv.app N by
            simpa [U] using
              s.moduleUnderlying.hom.naturality f =≫ s.moduleUnderlying.inv.app N]
      infer_instance
    exact (forget (ModuleCat.{w} s.ring)).epi_of_epi_map
      (show Epi ((s.modules ⋙ forget (ModuleCat.{w} s.ring)).map f) from inferInstance)
  have : s.modules.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology _⟩

end CategoryTheory.RingedSitePoint
