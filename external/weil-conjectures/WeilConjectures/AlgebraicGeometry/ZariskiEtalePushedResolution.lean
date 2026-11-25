/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolutionFiniteLimits
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolutionQuasiIso

/-! # Injective resolutions for the Zariski-etale comparison

Source: Stacks Project, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-pushed-resolution)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- Local vanishing makes the direct image of an injective resolution a resolution.

Source: Stacks Project, Tags 072W and 0733(1); Etale Cohomology, Tag 09AX;
Modules on Sites, Tag 03DJ.
(blueprint: lem-weil-pbc-zariski-etale-pushed-resolution)

Proof: factor the
given open-restriction functor through the etale object i(top).
Its left adjoint is usual exact inverse image followed by exact extension by zero,
so it preserves finite limits. Its right adjoint therefore preserves injectives.
Compute positive cohomology of the pushed complex by the section complex of I.
The arbitrary-universe Ext description is naturally equivalent to this computation.
Local injectivity of zero says each cocycle class is locally zero. Sheafification
commutes with homology (072W), so the pushed complex is exact in positive degrees.
Left exactness identifies its degree-zero kernel with i_*F. The pushed augmentation
is the inverse of the single-complex comparison followed
by the image of I.ι. Its source has only degree-zero homology, and its degree-zero
map on homology is the identity under the kernel identification. Thus it is a
quasi-isomorphism. This assertion fixes the pushed complex and augmentation;
it chooses no resolution data. -/
theorem zariski_etale_pushed_resolution
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) ∧
    ∀ (I : InjectiveResolution F),
      QuasiIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
          (ComplexShape.up ℕ) 0).inv.app F ≫
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
              (ComplexShape.up ℕ)).map I.ι) := by
  constructor
  · exact zariski_etale_pushed_resolution_finite_limits i hi_inclusion hi
  · exact zariski_etale_pushed_resolution_quasi_iso i hi_inclusion hi F hvan
