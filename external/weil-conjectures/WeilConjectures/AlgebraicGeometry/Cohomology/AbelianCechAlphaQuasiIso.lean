/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # The section augmentation is a quasi-isomorphism

Source: Stacks Project, Tag 01EQ, using Tags 01EP and 0133.
(blueprint: lem-pc-abelian-cech-alpha-quasi-iso)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The explicit restriction augmentation induces isomorphisms on homology.
Source: Stacks 01EQ, row augmentation argument.
(blueprint: lem-pc-abelian-cech-alpha-quasi-iso)

Proof: In each resolution degree use the restriction augmentation from global
sections concentrated at Čech degree zero. Its positive-degree exactness is
injective Čech acyclicity; in degree zero its map on homology is the gluing
isomorphism. Restrictions commute with the resolution differential, and the
Čech differential of a restriction family is zero. Apply the first-quadrant
column augmentation criterion to the double complex with Čech degree first.
Its finite-diagonal argument works for arbitrary covering index sets. -/
theorem abelianCechAlpha_quasiIso
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) : QuasiIso (abelianCechAlpha U I) := by
  let D := abelianCechDouble U I
  let A := abelianCechSections I
  let a : A ⟶ D.X 0 :=
    { f := fun n ↦ TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X n)
      comm' := by
        intro n m h
        ext s
        funext y
        exact NatTrans.naturality_apply (I.cocomplex.d n m).hom
          (homOfLE (le_top (a := ⨅ l, U (y l)))).op s }
  have ha : a ≫ D.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    exact TopCat.Sheaf.toCechCochainZero_d U (I.cocomplex.X n)
  apply HomologicalComplex₂.quasiIso_of_column_augmentation D A a ha
    (abelianCechAlpha U I) (fun _ ↦ rfl)
  intro n
  let K := (TopCat.Sheaf.cechComplexFunctor U).obj (I.cocomplex.X n)
  let e := (CochainComplex.fromSingle₀Equiv K (A.X n)).symm
    ⟨a.f n, TopCat.Sheaf.toCechCochainZero_d U (I.cocomplex.X n)⟩
  change QuasiIso e
  refine ⟨fun p ↦ ?_⟩
  cases p with
  | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by simp) (by simp) (by simp)]
      let S := K.sc' 0 0 1
      let f := S.liftCycles (a.f n)
        (TopCat.Sheaf.toCechCochainZero_d U (I.cocomplex.X n))
      change IsIso f
      let t := K.isoSc' 0 0 1 (by simp) (by simp)
      let g := ShortComplex.cyclesMap t.inv
      let k := K.liftCycles (TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X n))
        1 (by simp) (TopCat.Sheaf.toCechCochainZero_d U (I.cocomplex.X n))
      have hfg : f ≫ g = k := by
        apply (cancel_mono (K.iCycles 0)).1
        simp only [Iso.app_inv, ShortComplex.liftCycles_comp_cyclesMap,
          HomologicalComplex.natIsoSc'_inv_app_τ₂, HomologicalComplex.iCycles,
          ShortComplex.liftCycles_i, HomologicalComplex.liftCycles, f, g, t, k, a]
        exact Category.comp_id _
      have : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by simp)
      have : IsIso (k ≫ K.homologyπ 0) :=
        TopCat.Sheaf.isIso_toCechCohomologyZero_app hcover (I.cocomplex.X n)
      have : IsIso k := IsIso.of_isIso_comp_right k (K.homologyπ 0)
      have : IsIso g := by dsimp [g]; infer_instance
      have : IsIso (f ≫ g) := hfg.symm ▸ inferInstance
      exact IsIso.of_isIso_comp_right f g
  | succ p =>
      rw [quasiIsoAt_iff_exactAt e (p + 1)
        (CochainComplex.exactAt_succ_single_obj _ p)]
      exact TopCat.Presheaf.exactAt_cechComplex_of_injective U (I.cocomplex.X n) p
end AlgebraicGeometry.Scheme.Modules
