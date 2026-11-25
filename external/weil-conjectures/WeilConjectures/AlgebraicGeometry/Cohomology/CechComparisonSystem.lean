/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import WeilConjectures.Topology.Sheaves.CechCohomology

/-! # Normalized Čech comparison systems

Source: Stacks Project, Tags 01EQ and 01FD. A system records the comparison as a
morphism of cohomological functors, including its normalization and connecting maps.
(blueprint: def-pc-cech-comparison-system)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- A normalized morphism from Čech cohomology to sheaf cohomology.
Source: Stacks Project, Tag 01EQ, the augmented double-complex comparison;
Tag 01FD, functoriality. This is data with laws, with no postponed data.
(blueprint: def-pc-cech-comparison-system) -/
structure CechComparisonSystem {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤) where
  comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
    Sheaf.functorH.{u} (Opens.grothendieckTopology X) q
  zero : comparison 0 =
    (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
      (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology X) isTerminalTop).inv
  connecting : ∀ (T : ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ),
    TopCat.Sheaf.cechδ U hT hg q ≫ (comparison (q + 1)).app T.X₁ =
      (comparison q).app T.X₃ ≫ Sheaf.functorHδ.{u} hT q

/-- The underlying abelian presheaf does not change on restricting scalars.
Source: the explicit sectionwise definition of scalar restriction.
(blueprint: def-pc-cech-comparison-system) -/
noncomputable def presheafOverForgetIso
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (M : X.Modules) :
    presheafOver f M ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Transport of scalar-restricted Čech homology to abelian Čech cohomology.
Source: the source library's `cechComplexFunctorHomologyIso`.
(blueprint: def-pc-cech-comparison-system) -/
noncomputable def cechOverHomologyAddEquiv
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) (q : ℕ) :
    (cechOver f U M).homology q ≃+
      (TopCat.Sheaf.cechCohomologyFunctor U q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  (TopCat.Presheaf.cechComplexFunctorHomologyIso U (presheafOver f M) q ≪≫
    HomologicalComplex.homologyMapIso ((TopCat.Presheaf.cechComplex U).mapIso
      (presheafOverForgetIso f M)) q).addCommGroupIsoToAddEquiv

/-- The additive comparison induced by a fixed normalized system.
Source: Stacks Project, Tag 01EQ. No existence theorem is used to choose this map.
(blueprint: def-pc-cech-comparison-system) -/
noncomputable def CechComparisonSystem.overMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    {U : ι → X.Opens} {hcover : iSup U = ⊤} (c : CechComparisonSystem U hcover)
    (f : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    (cechOver f U M).homology q →+ HOver f M q :=
  ((c.comparison q).app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).hom.comp
    (cechOverHomologyAddEquiv f U M q).toAddMonoidHom

end AlgebraicGeometry.Scheme.Modules
