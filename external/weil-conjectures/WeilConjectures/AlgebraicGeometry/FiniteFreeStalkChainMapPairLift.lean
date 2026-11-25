/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapLift

/-! # Lifting a pair of finite free chain maps from a stalk

Source: lem-pc-finite-free-stalk-homotopy-spread, proof steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-chain-map-pair-lift)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A given pair of chain maps over the stalk lifts, without imposing inverse identities.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, finite matrix extension
argument, as expanded in lem-pc-finite-free-stalk-homotopy-spread, steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-chain-map-pair-lift).

Proof: Choose an affine neighbourhood and bases in every nonzero term. The source
complex has support [0,d] and the single complex has support {i}. The components
of the two prescribed chain maps are therefore finitely many matrices. Represent
each entry in the local ring by a section near y and intersect the neighbourhoods.
Each chain-map commutativity equation holds in the stalk. There are finitely many
such matrix equations; the equality criterion for germs makes each hold on a
smaller neighbourhood. Intersect these again and define all other components by
the unique maps involving zero objects. This constructs the two chain maps.
The canonical pullback-composition and restriction-pullback isomorphisms give eP
and eQ, and the represented entries give the stated exact equalities. No inverse
or homotopy identity is imposed, and no assumption of homotopy equivalence is used.
Ranks zero and i outside [0,d] cause only additional zero components. -/
theorem exists_restrict_chainMap_pair_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i : ℤ) (r : ℕ) (y : Y)
    (f : (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P) ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (g : (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)) :
    ∃ (V : Y.Opens) (hyV : y ∈ V),
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let T := (Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let Q := ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
      ∃ (eP : S.obj (R.obj P) ≅ T.obj P) (eQ : S.obj (R.obj Q) ≅ T.obj Q)
        (fV : R.obj P ⟶ R.obj Q) (gV : R.obj Q ⟶ R.obj P),
        S.map fV = eP.hom ≫ f ≫ eQ.inv ∧ S.map gV = eQ.hom ≫ g ≫ eP.inv := by
  let Q := (CochainComplex.singleFunctor Y.Modules i).obj
    (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))
  have hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))) :=
    fun n ↦ Or.inr (hfree n)
  have hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))) := by
    intro n
    by_cases hn : n = i
    · subst n
      exact Or.inr ⟨r, ⟨HomologicalComplex.singleObjXSelf _ _ _⟩⟩
    · exact Or.inl (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  obtain ⟨U, hyU, hf⟩ := exists_restrict_chainMap_of_stalk_eventually
    P Q 0 d i i hge hle (by infer_instance) (by infer_instance) hPfree hQfree y f
  obtain ⟨W, hyW, hg⟩ := exists_restrict_chainMap_of_stalk_eventually
    Q P i i 0 d (by infer_instance) (by infer_instance) hge hle hQfree hPfree y g
  let V := U ⊓ W
  have hyV : y ∈ V := ⟨hyU, hyW⟩
  obtain ⟨fV, hfV⟩ := hf V hyV inf_le_left
  obtain ⟨gV, hgV⟩ := hg V hyV inf_le_right
  exact ⟨V, hyV, (stalkRestrictionComplexIso V y hyV).app P,
    (stalkRestrictionComplexIso V y hyV).app Q, fV, gV, hfV, hgV⟩

end AlgebraicGeometry.Scheme.Modules
