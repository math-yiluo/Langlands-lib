/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Coefficient-universe instances for K-flat complexes

Sheafification of abelian presheaves in a coefficient universe containing the site, as used
by the K-flatness predicates of `WeilConjectures.Algebra.Homology.KFlat`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits
open scoped ZeroObject
open Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [hsmall : EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

/-- Abelian sheafification exists and is left exact in any universe containing the site.
Source: Stacks Project, Modules on Sites, Section 03DA, and Cohomology on Sites,
Definition 06YN (blueprint: def-pc-kflat-complex).

Proof: choose the small model of the site in the coefficient universe, where the usual
abelian sheafification exists. Conjugate its adjunction by the equivalences of presheaf
and sheaf categories induced by the small-model equivalence. Equivalences preserve
finite limits, so the transported left adjoint remains left exact. The adjunction
determines sheafification up to unique natural isomorphism. -/
@[instance]
theorem hasSheafify_coefficientUniverse : HasSheafify J AddCommGrpCat.{w} := by
  have : PreservesFilteredColimitsOfSize.{w, w}
      (CategoryTheory.forget AddCommGrpCat.{w}) := preservesFilteredColimitsOfSize_shrink _
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := inferInstance
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- Locally bijective maps are exactly sheafification equivalences for abelian groups
in any coefficient universe relative to which the site is essentially small.
Source: Stacks Project, Modules on Sites, Section 03DA, and Cohomology on Sites,
Definition 06YN (blueprint: def-pc-kflat-complex).

Proof: replace the site by its small model in the coefficient universe. On that model,
apply the usual concrete sheafification criterion for abelian groups. Transport the
criterion back along the dense equivalence; local injectivity and surjectivity and
sheafification equivalences are invariant under this equivalence. -/
@[instance]
theorem wEqualsLocallyBijective_coefficientUniverse :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  have : PreservesFilteredColimitsOfSize.{w, w}
      (CategoryTheory.forget AddCommGrpCat.{w}) := preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})

end SheafOfModules
