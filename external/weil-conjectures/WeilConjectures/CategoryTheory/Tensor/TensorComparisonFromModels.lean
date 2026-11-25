/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorAssociatorRepresentatives

/-! # Associativity from four inverse tensor-model squares

Source: Stacks 06YU, 0FPT; pasting and cancellation of tensor-model comparisons.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- Four binary model squares and a localized chain square imply associativity.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-tensor-comparison-from-models).

Proof: use inverse tensorator naturality to paste the two left binary squares
and the two right binary squares. The inverse lax tensorators satisfy the
associativity equation. Substitute the native associator model and the chain
square, then cancel the two model isomorphisms. -/
theorem associativity_from_inverse_tensor_models
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory A]
    (F : C ⥤ D) (p : A ⥤ D) [p.LaxMonoidal]
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    {P Q N PQ QN L R : C} {P' Q' N' PQ' QN' L' R' : A}
    [IsIso (Functor.LaxMonoidal.μ p P' Q')]
    [IsIso (Functor.LaxMonoidal.μ p Q' N')]
    [IsIso (Functor.LaxMonoidal.μ p PQ' N')]
    [IsIso (Functor.LaxMonoidal.μ p P' QN')]
    [IsIso (Functor.LaxMonoidal.μ p (P' ⊗ Q') N')]
    [IsIso (Functor.LaxMonoidal.μ p P' (Q' ⊗ N'))]
    (bPQ : PQ ≅ P ⊗ Q) (bQN : QN ≅ Q ⊗ N)
    (bL : L ≅ PQ ⊗ N) (bR : R ≅ P ⊗ QN)
    (cPQ : PQ' ≅ P' ⊗ Q') (cQN : QN' ≅ Q' ⊗ N')
    (cL : L' ≅ PQ' ⊗ N') (cR : R' ≅ P' ⊗ QN')
    (eP : F.obj P ≅ p.obj P') (eQ : F.obj Q ≅ p.obj Q')
    (eN : F.obj N ≅ p.obj N') (ePQ : F.obj PQ ≅ p.obj PQ')
    (eQN : F.obj QN ≅ p.obj QN') (eL : F.obj L ≅ p.obj L')
    (eR : F.obj R ≅ p.obj R') (a : L ⟶ R)
    (hB : (bL ≪≫ whiskerRightIso bPQ N).hom ≫ (α_ P Q N).hom =
      a ≫ (bR ≪≫ whiskerLeftIso P bQN).hom)
    (hPQ : F.map bPQ.hom ≫ t.hom.app (P, Q) ≫ (eP.hom ⊗ₘ eQ.hom) =
      ePQ.hom ≫ p.map cPQ.hom ≫ inv (Functor.LaxMonoidal.μ p P' Q'))
    (hQN : F.map bQN.hom ≫ t.hom.app (Q, N) ≫ (eQ.hom ⊗ₘ eN.hom) =
      eQN.hom ≫ p.map cQN.hom ≫ inv (Functor.LaxMonoidal.μ p Q' N'))
    (hL₀ : F.map bL.hom ≫ t.hom.app (PQ, N) ≫ (ePQ.hom ⊗ₘ eN.hom) =
      eL.hom ≫ p.map cL.hom ≫ inv (Functor.LaxMonoidal.μ p PQ' N'))
    (hR₀ : F.map bR.hom ≫ t.hom.app (P, QN) ≫ (eP.hom ⊗ₘ eQN.hom) =
      eR.hom ≫ p.map cR.hom ≫ inv (Functor.LaxMonoidal.μ p P' QN'))
    (hC : F.map a ≫ eR.hom ≫ p.map (cR ≪≫ whiskerLeftIso P' cQN).hom =
      eL.hom ≫ p.map (cL ≪≫ whiskerRightIso cPQ N').hom ≫ p.map (α_ P' Q' N').hom) :
    F.map (α_ P Q N).hom ≫ t.hom.app (P, Q ⊗ N) ≫
        (F.obj P ◁ t.hom.app (Q, N)) =
      t.hom.app (P ⊗ Q, N) ≫ (t.hom.app (P, Q) ▷ F.obj N) ≫
        (α_ (F.obj P) (F.obj Q) (F.obj N)).hom := by
  let lB := bL ≪≫ whiskerRightIso bPQ N
  let rB := bR ≪≫ whiskerLeftIso P bQN
  let aPQ := (asIso (Functor.LaxMonoidal.μ p P' Q')).symm
  let aQN := (asIso (Functor.LaxMonoidal.μ p Q' N')).symm
  let aL := (asIso (Functor.LaxMonoidal.μ p (P' ⊗ Q') N')).symm
  let aR := (asIso (Functor.LaxMonoidal.μ p P' (Q' ⊗ N'))).symm
  let aL₀ := (asIso (Functor.LaxMonoidal.μ p PQ' N')).symm
  let aR₀ := (asIso (Functor.LaxMonoidal.μ p P' QN')).symm
  let lA := aL ≪≫ whiskerRightIso aPQ (p.obj N')
  let rA := aR ≪≫ whiskerLeftIso (p.obj P') aQN
  let l := cL ≪≫ whiskerRightIso cPQ N'
  let r := cR ≪≫ whiskerLeftIso P' cQN
  have hA : lA.hom ≫ (α_ (p.obj P') (p.obj Q') (p.obj N')).hom =
      p.map (α_ P' Q' N').hom ≫ rA.hom := by
    simpa only [lA, rA, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      aL, aR, aPQ, aQN, Iso.symm_hom, asIso_inv, Category.assoc] using
        RingedDerivedNative.inverse_associativity p P' Q' N'
  have hnL := RingedDerivedNative.inverse_naturality p cPQ.hom (𝟙 N')
  have hnR := RingedDerivedNative.inverse_naturality p (𝟙 P') cQN.hom
  simp only [p.map_id, tensorHom_id] at hnL
  simp only [p.map_id, id_tensorHom] at hnR
  have hL := tensorModel_left_square F p t bPQ.hom bL.hom eP.hom eQ.hom eN.hom
    ePQ.hom eL.hom cPQ.hom cL.hom aPQ.hom aL₀.hom aL.hom hPQ hL₀ hnL
  have hR := tensorModel_right_square F p t bQN.hom bR.hom eP.hom eQ.hom eN.hom
    eQN.hom eR.hom cQN.hom cR.hom aQN.hom aR₀.hom aR.hom hQN hR₀ hnR
  exact RingedForgetTensorTransposition.associativity_transport F t lB rB a
    lA.hom rA.hom (p.map (α_ P' Q' N').hom) eP eQ eN
    (eL.hom ≫ p.map l.hom) (eR.hom ≫ p.map r.hom) hB hA hL hR
    (by simpa only [Category.assoc] using hC)

end CategoryTheory
