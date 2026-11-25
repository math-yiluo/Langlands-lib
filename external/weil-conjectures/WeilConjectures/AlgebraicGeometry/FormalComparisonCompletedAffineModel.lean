/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalAffineMorphismRealization
import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineRestrictionIso
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Coherent model of the affine formal comparison

Source: Stacks Project, Lemma 088B, base change to the completion and algebraization.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-model)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine limit comparison is conjugate, after restricting scalars, to global
sections of a map between coherent modules over the completed affine base. That map
is invertible away from the extended exceptional ideal. No annihilation is asserted.

Source: Stacks Project, Lemma 088B, second half of its proof, through the assertion
that the algebraized adjunction map is invertible over the complement of V(K).
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-model)

Proof: Restrict f, F, G, beta and the two comparison equations to the affine U.
Put B = Gamma(U,O) and R = its J(U)-adic completion. R is Noetherian and flat over
B, and B/J(U)^n = R/(J(U)R)^n. Base change X_U to Spec R. Flat base change identifies
pushforward of F and of its quotients with the corresponding pullbacks. Formal
functions and the affine formal-module equivalence identify the inverse limits
before and after this base change, naturally on morphisms. Algebraize G over R by
the affine equivalence, obtaining A. Pullback commutes with completion, so full
faithfulness of completion on coherent modules proper over R lifts beta, and its
inverse, to inverse coherent maps b and b^{-1}. Put D = f'_*F' and let c be the
adjunction unit followed by f'_*b. Proper coherent direct image gives coherence of
D. The quotient and adjunction equations, and uniqueness via formal functions,
identify the limit of alpha with the sections of c under the two limit isomorphisms.
The base change f' is an isomorphism off V(K(U)R); there the adjunction unit, and
hence c, is invertible. This gives the asserted restriction isomorphism. If U is
empty, R is the zero ring and both coherent modules and limits vanish. If J(U) is
the unit ideal, its completion and all the formal terms vanish as well.
-/
theorem formalComparison_completed_affine_model
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      let L := (K.ideal U).map (algebraMap B R)
      let Q := Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ∃ (A D : CoherentModules (Spec (CommRingCat.of R))) (c : A.obj ⟶ D.obj),
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι Q.support.compl)).map c) ∧
        ∃ eA : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj),
        ∃ eD : limit (((completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj),
          lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD.hom =
          eA.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c) := by
  intro U
  obtain ⟨A, D, c, eA, eD, hs⟩ :=
    formal_affine_morphism_realization J G
      ((completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩) α U
  have hc := formalComparison_completed_affine_restriction_isIso
    J K f hV adj G F β h κ α hκ hα U A D c eA eD hs
  exact ⟨A, D, c, hc, eA, eD, hs⟩

end AlgebraicGeometry
