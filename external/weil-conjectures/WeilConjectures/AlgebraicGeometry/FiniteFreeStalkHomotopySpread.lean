/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapPairLift
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkHomotopyPairShrink

/-! # Spreading a finite free homotopy normal form from a stalk

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4 (finite matrix
identities). (blueprint: lem-pc-finite-free-stalk-homotopy-spread)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A homotopy equivalence with a single free complex over a local ring spreads.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4, finite matrix
extension argument. (blueprint: lem-pc-finite-free-stalk-homotopy-spread).

Proof: Work on an affine neighbourhood of y and choose finite bases of P's terms.
Both complexes have finite support. Under the affine quasicoherent module-sheaf
correspondence, the given maps and the two homotopies are finite lists of matrices
with entries in the local ring at y. Represent their finitely many entries by
sections on neighbourhoods of y, and intersect those neighbourhoods. Chain-map
commutativity and the two homotopy equations are finitely many entrywise equations
of sections. Each holds in the stalk, so after shrinking around y each holds as an
equation of sections; intersect this second finite list of neighbourhoods. All
components outside the bounded support are the unique maps from or to zero objects,
so there are no further equations to impose. The represented matrices now define
chain maps and homotopies on the resulting open V, proving that the composites are
homotopic to the identities. No residue cohomology or base change is used here. -/
theorem exists_restrict_homotopyEquiv_single_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (hy : Nonempty (HomotopyEquiv
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))) :
    ∃ V : Y.Opens, y ∈ V ∧ Nonempty (HomotopyEquiv
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))) := by
  obtain ⟨e⟩ := hy
  obtain ⟨V, hyV, eP, eQ, f, g, hf, hg⟩ :=
    exists_restrict_chainMap_pair_of_stalk P d hge hle hfree i r y e.hom e.inv
  let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hP : Nonempty (Homotopy (S.map (f ≫ g)) (S.map (𝟙 _))) := by
    refine ⟨?_⟩
    rw [S.map_comp, S.map_id, hf, hg]
    simpa only [Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      (e.homotopyHomInvId.compLeft eP.hom).compRight eP.inv
  have hQ : Nonempty (Homotopy (S.map (g ≫ f)) (S.map (𝟙 _))) := by
    refine ⟨?_⟩
    rw [S.map_comp, S.map_id, hf, hg]
    simpa only [Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      (e.homotopyInvHomId.compLeft eQ.hom).compRight eQ.inv
  obtain ⟨W, hWV, hyW, ⟨hPW⟩, ⟨hQW⟩⟩ :=
    exists_shrink_homotopy_pair_of_stalk P d hge hle hfree i r y V hyV
      (f ≫ g) (𝟙 _) (g ≫ f) (𝟙 _) hP hQ
  let R := (restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex (ComplexShape.up ℤ)
  let eW : HomotopyEquiv (R.obj (((restrictFunctor V.ι).mapHomologicalComplex _).obj P))
      (R.obj (((restrictFunctor V.ι).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))) :=
    { hom := R.map f
      inv := R.map g
      homotopyHomInvId := by
        change Homotopy (R.map (f ≫ g)) (R.map (𝟙 _)) at hPW
        rw [R.map_comp, R.map_id] at hPW
        exact hPW
      homotopyInvHomId := by
        change Homotopy (R.map (g ≫ f)) (R.map (𝟙 _)) at hQW
        rw [R.map_comp, R.map_id] at hQW
        exact hQW }
  let c := NatIso.mapHomologicalComplex
    ((restrictFunctorCongr (Y.homOfLE_ι hWV)).symm ≪≫
      restrictFunctorComp (Y.homOfLE hWV) V.ι) (ComplexShape.up ℤ)
  exact ⟨W, hyW, ⟨((HomotopyEquiv.ofIso (c.app P)).trans eW).trans
    (HomotopyEquiv.ofIso (c.app _).symm)⟩⟩

end AlgebraicGeometry.Scheme.Modules
