/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Objectwise coefficient counit mates

Source: blueprint main-20261015, lem-coef-finite-dualizing.proof.md,
paragraph 3, the sentence beginning “The same adjoint calculation”.
(blueprint: lem-coef-dualizing-quotient-mates)
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆

namespace CategoryTheory.Adjunction

/-- Counit mates satisfy the coefficient cocycle using only the four specified
invertible comparison components. The associators and the identifications of the
three target objects are displayed explicitly. No mate is assumed invertible.

Source: blueprint main-20261015, lem-coef-finite-dualizing.proof.md,
paragraph 3, the sentence beginning “The same adjoint calculation”.
(blueprint: lem-coef-dualizing-quotient-mates)

Proof: (1) By lem-weil-pbc-adjunction-of-natural-bijection, the inverse Hom
bijection for aC sends w to FC(w) followed by its counit; it detects equality in
the whole Hom set. Each displayed Hom transpose is defined by the specified
inverse comparison, the transported counit, and the specified object identification.
(2) Put X = GA(NA), Y = GB(NB), and a = vAB. Naturality of cBC at a says
TD_BC(FB(a)) followed by cBC at Y equals cBC at TC_AB(X) followed by
FC(TC_BC(a)). Multiply by the two assumed inverse components to move them
across this square. No inverse natural transformation is needed.
(3) Transpose TC_BC(vAB) followed by vBC. Substitute the defining counit
equation for vBC, the square from (2), and then the defining counit equation for
vAB. Functoriality preserves inverses. The component cocycle hc identifies the
resulting composite inverse with the inverse cAC, after the associators. Naturality
of assocD at the A counit and the object-identification equation hN identify the
remaining factors with TD_AC of that counit followed by nAC. This is the transpose
of vAC, so injectivity from (1) proves the equality. This is steps 1--3 of the node.
-/
theorem coefficientCounitMate_cocycle
    {CA : Type u₁} {DA : Type u₂} {CB : Type u₃} {DB : Type u₄}
    {CC : Type u₅} {DC : Type u₆}
    [Category.{v₁} CA] [Category.{v₂} DA] [Category.{v₃} CB]
    [Category.{v₄} DB] [Category.{v₅} CC] [Category.{v₆} DC]
    {FA : CA ⥤ DA} {GA : DA ⥤ CA} {FB : CB ⥤ DB} {GB : DB ⥤ CB}
    {FC : CC ⥤ DC} {GC : DC ⥤ CC}
    (aA : FA ⊣ GA) (aB : FB ⊣ GB) (aC : FC ⊣ GC)
    (tcAB : CA ⥤ CB) (tdAB : DA ⥤ DB) (tcBC : CB ⥤ CC) (tdBC : DB ⥤ DC)
    (tcAC : CA ⥤ CC) (tdAC : DA ⥤ DC)
    (assocC : tcAB ⋙ tcBC ≅ tcAC) (assocD : tdAB ⋙ tdBC ≅ tdAC)
    (NA : DA) (NB : DB) (NC : DC)
    (nAB : tdAB.obj NA ≅ NB) (nBC : tdBC.obj NB ≅ NC) (nAC : tdAC.obj NA ≅ NC)
    (hN : tdBC.map nAB.hom ≫ nBC.hom = assocD.hom.app NA ≫ nAC.hom)
    (cAB : FA ⋙ tdAB ⟶ tcAB ⋙ FB) (cBC : FB ⋙ tdBC ⟶ tcBC ⋙ FC)
    (cAC : FA ⋙ tdAC ⟶ tcAC ⋙ FC)
    (hc : tdBC.map (cAB.app (GA.obj NA)) ≫ cBC.app (tcAB.obj (GA.obj NA)) ≫
        FC.map (assocC.hom.app (GA.obj NA)) =
      assocD.hom.app (FA.obj (GA.obj NA)) ≫ cAC.app (GA.obj NA))
    [IsIso (cAB.app (GA.obj NA))] [IsIso (cAC.app (GA.obj NA))]
    [IsIso (cBC.app (GB.obj NB))] [IsIso (cBC.app (tcAB.obj (GA.obj NA)))] :
    (aC.homEquiv (tcAC.obj (GA.obj NA)) NC)
        (inv (cAC.app (GA.obj NA)) ≫ tdAC.map (aA.counit.app NA) ≫ nAC.hom) =
      assocC.inv.app (GA.obj NA) ≫
        tcBC.map ((aB.homEquiv (tcAB.obj (GA.obj NA)) NB)
          (inv (cAB.app (GA.obj NA)) ≫ tdAB.map (aA.counit.app NA) ≫ nAB.hom)) ≫
        (aC.homEquiv (tcBC.obj (GB.obj NB)) NC)
          (inv (cBC.app (GB.obj NB)) ≫ tdBC.map (aB.counit.app NB) ≫ nBC.hom) := by
  let vAB := (aB.homEquiv (tcAB.obj (GA.obj NA)) NB)
    (inv (cAB.app (GA.obj NA)) ≫ tdAB.map (aA.counit.app NA) ≫ nAB.hom)
  have hAB : FB.map vAB ≫ aB.counit.app NB =
      inv (cAB.app (GA.obj NA)) ≫ tdAB.map (aA.counit.app NA) ≫ nAB.hom :=
    (aB.homEquiv _ _).symm_apply_apply _
  have hn : FC.map (tcBC.map vAB) ≫ inv (cBC.app (GB.obj NB)) =
      inv (cBC.app (tcAB.obj (GA.obj NA))) ≫ tdBC.map (FB.map vAB) := by
    apply (cancel_epi (cBC.app (tcAB.obj (GA.obj NA)))).1
    simpa [Category.assoc, ← cBC.naturality vAB] using
      congrArg (fun f => f ≫ inv (cBC.app (GB.obj NB))) (cBC.naturality vAB).symm
  have hi : FC.map (assocC.inv.app (GA.obj NA)) ≫
        inv (cBC.app (tcAB.obj (GA.obj NA))) ≫ tdBC.map (inv (cAB.app (GA.obj NA))) =
      inv (cAC.app (GA.obj NA)) ≫ assocD.inv.app (FA.obj (GA.obj NA)) := by
    have h := IsIso.inv_eq_inv.mpr hc
    simpa [IsIso.inv_comp, ← Functor.map_inv, Category.assoc] using h
  apply (aC.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, aC.homEquiv_naturality_left_symm,
    aC.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  change _ = FC.map (assocC.inv.app (GA.obj NA)) ≫
    FC.map (tcBC.map vAB) ≫ inv (cBC.app (GB.obj NB)) ≫
      tdBC.map (aB.counit.app NB) ≫ nBC.hom
  rw [← Category.assoc (FC.map (tcBC.map vAB)), hn]
  simp only [Category.assoc]
  rw [← tdBC.map_comp_assoc, hAB, tdBC.map_comp, tdBC.map_comp]
  simp only [Category.assoc]
  simp only [← Category.assoc] at hi ⊢
  rw [hi]
  simp only [Category.assoc]
  rw [hN]
  have hd : assocD.inv.app (FA.obj (GA.obj NA)) ≫
        tdBC.map (tdAB.map (aA.counit.app NA)) ≫ assocD.hom.app NA =
      tdAC.map (aA.counit.app NA) := NatIso.naturality_1 assocD (aA.counit.app NA)
  simpa only [Category.assoc] using
    congrArg (fun f => inv (cAC.app (GA.obj NA)) ≫ f ≫ nAC.hom) hd.symm

/-- The identity coefficient mate is the unit identification on the right-adjoint
object, hence is the identity after that identification. The invertibility needed
to take the comparison inverse is transported from its prescribed unit value.

Source: blueprint main-20261015, lem-coef-finite-dualizing.proof.md,
paragraph 3, the sentence beginning “The same adjoint calculation”.
(blueprint: lem-coef-dualizing-quotient-mates)

Proof: Step 4 of the node. Transpose the unit identification uC at G(N) under a.
The inverse Hom bijection is F of that map followed by the counit, by
lem-weil-pbc-adjunction-of-natural-bijection. The equality hc identifies the
comparison with uD at F(G(N)) followed by F of the inverse uC. Its inverse is
therefore F of uC followed by the inverse uD. Naturality of uD at the counit and
hN reduce the defining adjunct to F of uC followed by the counit. Injectivity of
the inverse Hom bijection gives the asserted equality. With identity coefficient
functors and identity unit identifications this reads vRR = 1, for arbitrary a.
-/
theorem coefficientCounitMate_identity
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (tc : C ⥤ C) (td : D ⥤ D) (uC : tc ≅ 𝟭 C) (uD : td ≅ 𝟭 D)
    (N : D) (n : td.obj N ≅ N) (hN : n.hom = uD.hom.app N)
    (c : F ⋙ td ⟶ tc ⋙ F)
    (hc : c.app (G.obj N) = uD.hom.app (F.obj (G.obj N)) ≫ F.map (uC.inv.app (G.obj N))) :
    (a.homEquiv (tc.obj (G.obj N)) N)
        ((@inv D _ _ _ (c.app (G.obj N))
          (hc.symm ▸ (inferInstance : IsIso
            (uD.hom.app (F.obj (G.obj N)) ≫ F.map (uC.inv.app (G.obj N)))))) ≫
          td.map (a.counit.app N) ≫ n.hom) =
      uC.hom.app (G.obj N) := by
  apply (a.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, a.homEquiv_counit]
  have : IsIso (c.app (G.obj N)) := hc.symm ▸ inferInstance
  have hi := IsIso.inv_eq_inv.mpr hc
  change inv (c.app (G.obj N)) ≫ _ = _
  rw [hi, IsIso.inv_comp, ← F.map_inv]
  simp only [NatIso.inv_inv_app, NatIso.inv_hom_app]
  rw [hN]
  have hd : uD.inv.app (F.obj (G.obj N)) ≫ td.map (a.counit.app N) ≫
      uD.hom.app N = a.counit.app N := NatIso.naturality_1 uD (a.counit.app N)
  simpa only [Category.assoc] using
    congrArg (fun f => F.map (uC.hom.app (G.obj N)) ≫ f) hd

end CategoryTheory.Adjunction
