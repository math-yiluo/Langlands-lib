/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.FiniteFreeResidueLocalHomotopy
import WeilConjectures.AlgebraicGeometry.FiniteFreeSingleFieldFibre

/-! # Residue detection of pulled-back single cohomology

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: lem-pc-finite-free-pullback-residue-criterion)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem rank_map_eq_of_same_image {Y : Scheme.{u}}
    {m n : Type u} [Finite m] [Fintype n] (A : Matrix m n Γ(Y, ⊤))
    {R S : CommRingCat.{u}} (hR : IsField R) (hS : IsField S)
    (f : Spec R ⟶ Y) (g : Spec S ⟶ Y) (x : Spec R) (z : Spec S)
    (h : f.base x = g.base z) : (A.map f.appTop).rank = (A.map g.appTop).rank := by
  apply Nat.le_antisymm
  · obtain ⟨a, b, hab⟩ :=
      (le_rank_map_appTop_iff (isField_Γ_Spec hR) f x A _).mp le_rfl
    apply (le_rank_map_appTop_iff (isField_Γ_Spec hS) g z A _).mpr
    exact ⟨a, b, by simpa only [h] using hab⟩
  · obtain ⟨a, b, hab⟩ :=
      (le_rank_map_appTop_iff (isField_Γ_Spec hS) g z A _).mp le_rfl
    apply (le_rank_map_appTop_iff (isField_Γ_Spec hR) f x A _).mpr
    exact ⟨a, b, by simpa only [h] using hab⟩

private theorem finrank_homology_eq_of_same_image {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    {R S : CommRingCat.{u}} (hR : IsField R) (hS : IsField S)
    (f : Spec R ⟶ Y) (g : Spec S ⟶ Y) (x : Spec R) (z : Spec S)
    (h : f.base x = g.base z) (q : ℤ) :
    Module.finrank R ((moduleSpecΓFunctor (R := R)).obj
      ((((Modules.pullback f).mapHomologicalComplex _).obj P).homology q)) =
    Module.finrank S ((moduleSpecΓFunctor (R := S)).obj
      ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) := by
  classical
  choose ranks he using hfree
  let e (n : ℤ) := (he n).some
  have hf := finrank_homology_pullback_add_rank_add_rank e hR f q
  have hg := finrank_homology_pullback_add_rank_add_rank e hS g q
  have h₁ := rank_map_eq_of_same_image
    (freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)) hR hS f g x z h
  have h₂ := rank_map_eq_of_same_image
    (freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)) hR hS f g x z h
  omega

private theorem single_cohomology_of_homotopyEquiv {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ) (i r : ℕ)
    (e : HomotopyEquiv P ((CochainComplex.singleFunctor Y.Modules (i : ℤ)).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) :
    (∀ q : ℕ, q ≠ i → IsZero (P.homology q)) ∧
      (P.homology i).IsFiniteLocallyFreeOfRank r := by
  constructor
  · intro q hq
    exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (i : ℤ)
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) (q : ℤ)
      (by exact_mod_cast hq)).of_iso (e.toHomologyIso (q : ℤ))
  · exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (e.toHomologyIso (i : ℤ) ≪≫ HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (i : ℤ) _).symm

/-- Single finite locally free cohomology of a pulled-back bounded nonnegative finite
free complex is detected by the residue cohomology at all image points.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: lem-pc-finite-free-pullback-residue-criterion).

Proof: at any image point satisfying the residue condition, split unit entries over
its local ring as in lem-weil-pbc-free-complex-unit-entry-splits. The resulting minimal
complex has rank r in degree i and rank zero elsewhere. Spread the finite sequence
of cancellations to a neighbourhood. Pullback preserves the explicit homotopies and
contractible summands, so its cohomology on the inverse image neighbourhood vanishes
off i and is free of rank r in degree i. These neighbourhoods cover the source;
vanishing and finite local freeness glue.
Conversely, the pulled-back complex has zero cohomology off i and locally free rank-r
cohomology in degree i. Its negative cohomology is zero by nonnegative support.
Truncation identifies it locally with that flat sheaf in degree i. Its derived fibre
is thus the residue field to the r-th power in degree i. The terms of the original
complex are free, so termwise pullback computes both derived fibres. At a source
point z over y this fibre is the scalar extension from κ(y) to κ(z) of the fibre at y.
A field extension is faithfully flat and preserves finite-dimensional cohomology
ranks (lem-pc-finrank-field-base-change); hence the fibre at y has the same vanishing
and rank. This proves the criterion, also for the empty source and rank zero. -/
theorem finiteFree_pullback_single_iff_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    ((∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) ∧
      ((((Modules.pullback g).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) ↔
      ∀ y ∈ Set.range g.base, ((∀ q : ℕ, q ≠ i → IsZero
          ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
            P).homology q)) ∧
        ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
          P).homology i).IsFiniteLocallyFreeOfRank r) := by
  classical
  let Q : CochainComplex Y'.Modules ℤ :=
    ((Modules.pullback g).mapHomologicalComplex _).obj P
  constructor
  · intro h y hy
    obtain ⟨z, rfl⟩ := hy
    have hQge : Q.IsStrictlyGE 0 := by
      let := hge
      infer_instance
    have hQle : Q.IsStrictlyLE d := by
      let := hle
      infer_instance
    have hQfree (n : ℤ) : ∃ s : ℕ, Nonempty
        (Q.X n ≅ SheafOfModules.free (R := Y'.ringCatSheaf) (ULift.{u} (Fin s))) := by
      obtain ⟨s, ⟨e⟩⟩ := hfree n
      exact ⟨s, ⟨(Modules.pullback g).mapIso e ≪≫ pullbackFreeIso g _⟩⟩
    let f := Y'.fromSpecResidueField z
    have hR := Field.toIsField (Y'.residueField z)
    obtain ⟨e⟩ := nonempty_homotopyEquiv_single_field_fibre
      Q d hQge hQle hQfree i r h.1 h.2 hR f
    have he := single_cohomology_of_homotopyEquiv _ i r e
    let ecomp : ((Modules.pullback f).mapHomologicalComplex _).obj Q ≅
        ((Modules.pullback (f ≫ g)).mapHomologicalComplex _).obj P :=
      (Functor.mapHomologicalComplexCompIso
        (Modules.pullbackComp f g) (ComplexShape.up ℤ)).app P
    have hfg : (∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback (f ≫ g)).mapHomologicalComplex _).obj P).homology q)) ∧
      ((((Modules.pullback (f ≫ g)).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r := by
      constructor
      · intro q hq
        exact (he.1 q hq).of_iso
          ((HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso ecomp).symm
      · exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
          (((HomologicalComplex.homologyFunctor _ _ (i : ℤ)).mapIso ecomp).symm ≪≫
            e.toHomologyIso (i : ℤ) ≪≫ HomologicalComplex.singleObjHomologySelfIso
              (ComplexShape.up ℤ) (i : ℤ) _).symm
    let k := Y.fromSpecResidueField (g.base z)
    have hS := Field.toIsField (Y.residueField (g.base z))
    obtain ⟨x⟩ : Nonempty (Spec (Y'.residueField z)) := inferInstance
    obtain ⟨w⟩ : Nonempty (Spec (Y.residueField (g.base z))) := inferInstance
    have himage : (f ≫ g).base x = k.base w := by
      simp [f, k, Scheme.fromSpecResidueField_apply]
    have hdim (q : ℤ) := finrank_homology_eq_of_same_image
      P hfree hR hS (f ≫ g) k x w himage q
    have hfinR (q : ℤ) := finite_moduleSpecΓFunctor_obj_homology_pullback
      hfree hR (f ≫ g) q
    have hfinS (q : ℤ) := finite_moduleSpecΓFunctor_obj_homology_pullback
      hfree hS k q
    constructor
    · intro q hq
      apply (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hS _).mpr
      rw [← hdim q]
      exact (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hR _).mp (hfg.1 q hq)
    · apply (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hS _ r).mpr
      rw [← hdim i]
      exact (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hR _ r).mp hfg.2
  · intro h
    have hloc (z : Y') := exists_restrict_homotopyEquiv_single_of_residue
      P d hge hle hfree i r g z (h (g.base z) ⟨z, rfl⟩)
    choose U hU he using hloc
    have hcover : ⨆ z, U z = ⊤ :=
      eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hU z⟩
    have hlocal (z : Y') := single_cohomology_of_homotopyEquiv _ i r (he z).some
    have eH (z : Y') (q : ℤ) :
        (((restrictFunctor (U z).ι).mapHomologicalComplex _).obj Q).homology q ≅
          (Q.homology q).restrict (U z).ι :=
      (Q.sc q).mapHomologyIso (restrictFunctor (U z).ι)
    constructor
    · intro q hq
      exact isZero_of_iSup_eq_top _ U hcover fun z ↦
        (hlocal z |>.1 q hq).of_iso (eH z q).symm
    · have hfreeU (z : Y') : Nonempty
          ((Q.homology i).restrict (U z).ι ≅
            SheafOfModules.free (ULift.{u} (Fin r))) :=
        ⟨(eH z i).symm ≪≫ (he z).some.toHomologyIso (i : ℤ) ≪≫
          HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (i : ℤ) _⟩
      exact isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun z ↦ (U z).ι)
        (by simpa only [Scheme.Opens.opensRange_ι] using hcover) hfreeU

end AlgebraicGeometry.Scheme.Modules
