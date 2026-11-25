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
import WeilConjectures.AlgebraicGeometry.PushedResolutionPositiveHomologyZero
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction
/-- Local cohomology vanishing makes the fixed pushed augmentation a quasi-isomorphism.

Source: Stacks Project, Cohomology on Sites, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso)

Proof: fix I. Sheafification adjunction, the free abelian group adjunction and
Yoneda identify Hom from the free abelian representable of an etale object to a
sheaf with its sections there. Apply this naturally degreewise to I. Computing
Ext by I identifies the resulting section-complex cohomology with the Ext-based
cohomology presheaf, including its restriction maps. This computation permits the
arbitrary Ext universe: only the Ext comparison changes universe, while the
section complex stays in the coefficient universe. After precomposition by i.op,
local injectivity of the zero map says that every positive cohomology class is
locally zero. The map of this presheaf to zero is consequently locally bijective
(local surjectivity is automatic), so its sheafification is zero. Exact
sheafification commutes with homology, and its counit is an isomorphism on the
complex of sheaves i_*I. Hence the latter has zero homology in positive degrees.
Continuous direct image is right adjoint, so preserves the kernel of I^0 -> I^1.
Thus degree-zero homology is i_*F, and the displayed augmentation induces this
kernel identification: the inverse single-complex comparison identifies its
component in degree zero with the image of I.ι. In positive degrees both its
source and target homology are zero. All homology maps are therefore isomorphisms,
which is exactly the displayed QuasiIso assertion. No comparison map is chosen. -/
theorem zariski_etale_pushed_resolution_quasi_iso
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    ∀ (I : InjectiveResolution F),
      QuasiIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
          (ComplexShape.up ℕ) 0).inv.app F ≫
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
              (ComplexShape.up ℕ)).map I.ι) := by
  intro I
  have _ := hi_inclusion
  let P := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let e := (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℕ) 0).inv.app F
  let f := (P.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  change QuasiIso (e ≫ f)
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    -- Incoming differentials are zero, so preservation of kernels suffices.
    have h₁ : P.PreservesLeftHomologyOf
        (((CochainComplex.single₀ _).obj F).sc 0) :=
      P.preservesLeftHomology_of_zero_f _ (by simp)
    have h₂ : P.PreservesLeftHomologyOf (I.cocomplex.sc 0) :=
      P.preservesLeftHomology_of_zero_f _ (by simp)
    have hf : QuasiIsoAt f 0 := by
      rw [quasiIsoAt_iff]
      have : ShortComplex.QuasiIso
          ((HomologicalComplex.shortComplexFunctor _ _ 0).map I.ι) :=
        (quasiIsoAt_iff I.ι 0).mp inferInstance
      exact ShortComplex.quasiIso_map_of_preservesLeftHomology P
        ((HomologicalComplex.shortComplexFunctor _ _ 0).map I.ι)
    infer_instance
  | succ n =>
    -- Both complexes have zero homology in positive degrees.
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact pushed_resolution_positive_homology_isZero i hi F hvan I
        (n + 1) (Nat.succ_pos n)
    · exact CochainComplex.exactAt_succ_single_obj _ n

