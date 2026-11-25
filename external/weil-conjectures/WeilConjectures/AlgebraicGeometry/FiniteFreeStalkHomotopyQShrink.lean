/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Shrinking equality for a single finite free complex

Source: lemma-coherent-base-change-invertible-sheaves--3, extension of finite calculations near a
point. (blueprint: lem-pc-finite-free-stalk-homotopy-q-inside)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A stalk homotopy of single-complex maps spreads inside a prescribed neighbourhood.

Source: blueprint sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus,
proof, extension of the finite calculation to a neighbourhood; the single-complex
case of lem-pc-finite-free-stalk-homotopy-pair-shrink, steps 1--3.
(blueprint: lem-pc-finite-free-stalk-homotopy-q-inside).

Proof: The single complex Q has zero differentials, and its restrictions and
pullbacks still have zero differentials. Thus the equations of the homotopy hQ
say that the pullbacks of c and e agree in each degree. Outside degree i all
terms are zero, so only the degree-i equation is relevant. Identify the degree-i
term after restriction with the rank-r free sheaf, using restriction of the
standard basis. In this basis the difference of the degree-i maps is a finite
r by r matrix of sections on V. Pullback along V.fromSpecStalkOfMem evaluates
its entries at their germs in O_{Y,y}; the degree-i equation of hQ therefore
says that every entry has zero germ. For each of the finitely many entries,
the germ equality criterion gives a neighbourhood inside V on which it is zero.
Intersect them with U to get W containing y and contained in U. All degree-i
entries vanish on W, hence the restricted maps agree there; in other degrees
they agree since their source terms are zero. Homotopy.ofEq gives the asserted
homotopy. If r=0 there are no entries and W=U suffices. Negative or arbitrarily
large i do not matter: the complex is supported only in that one degree. -/
theorem exists_shrink_homotopy_Q_inside_of_stalk
    {Y : Scheme.{u}}
    (i : ℤ) (r : ℕ) (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (c e : (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj
      ((CochainComplex.singleFunctor Y.Modules i).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))))
    (hQ : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map c)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map e)))
    (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map c)
        (((restrictFunctor (Y.homOfLE (hWU.trans hUV))).mapHomologicalComplex _).map e)) := by
  obtain ⟨h⟩ := hQ
  have hi : (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (c.f i) =
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (e.f i) := by
    simpa [dNext, prevD,
      Functor.mapHomologicalComplex, HomologicalComplex.single_obj_d] using h.comm i
  obtain ⟨W, hWU, hyW, heq⟩ := exists_restrict_eq_of_pullback_eq
    r y V hyV _ _
    ⟨(restrictFunctor V.ι).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i _)⟩
    (c.f i) (e.f i) hi U hUV hyU
  refine ⟨W, hWU, hyW, ⟨Homotopy.ofEq ?_⟩⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = i
  · subst n
    exact heq
  · exact ((restrictFunctor (Y.homOfLE (hWU.trans hUV))).map_isZero
      ((restrictFunctor V.ι).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i _ n hn))).eq_of_src _ _


end AlgebraicGeometry.Scheme.Modules
