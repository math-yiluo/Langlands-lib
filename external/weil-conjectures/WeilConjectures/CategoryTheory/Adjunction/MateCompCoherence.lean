/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-!
# Mates and composition isomorphisms of the horizontal functors

Let `L_Z ⊣ R_Z`, `L_Y ⊣ R_Y`, `L_X ⊣ R_X` be adjunctions ("vertical" functors, e.g. the
comparison `ν^* ⊣ Rν_*` over three schemes) and let `G_q`, `G_p`, `G_{pq}` and `H_q`, `H_p`,
`H_{pq}` be "horizontal" functors (e.g. pullbacks along `p : X ⟶ Y`, `q : Y ⟶ Z` and `p ≫ q`) with
composition isomorphisms `G_{pq} ≅ G_q ⋙ G_p` and `H_{pq} ≅ H_q ⋙ H_p`. If 2-squares
`a_q`, `a_p`, `a_{pq}` of left adjoints are compatible with the composition isomorphisms, then
so are their mates (`CategoryTheory.mateEquiv_app_comp_of_compCoherence`): this is the
compatibility of mates with pasting, `CategoryTheory.mateEquiv_vcomp`.

We also record how a mate changes when the second adjunction is transported along an
isomorphism of left adjoints (`CategoryTheory.mateEquiv_ofNatIsoLeft_right`), the companion of
`CategoryTheory.mateEquiv_ofNatIsoLeft`, and that transporting an adjunction along an isomorphism
and back gives the original adjunction (`CategoryTheory.Adjunction.ofNatIsoLeft_ofNatIsoLeft_symm`).
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

section OfNatIsoLeft

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- Transporting an adjunction along an isomorphism of left adjoints and back gives the original
adjunction. -/
lemma Adjunction.ofNatIsoLeft_ofNatIsoLeft_symm {L L' : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (e : L ≅ L') : (adj.ofNatIsoLeft e).ofNatIsoLeft e.symm = adj := by
  ext X
  simp [← Functor.map_comp]

/-- The mate under an adjunction `L₂' ⊣ R₂` transported along `e : L₂ ≅ L₂'` (as the second
adjunction) is the mate under `L₂ ⊣ R₂` of the square precomposed with `e`. -/
lemma mateEquiv_ofNatIsoLeft_right {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₂')
    (α : TwoSquare G L₁ L₂' H) :
    mateEquiv adj₁ (adj₂.ofNatIsoLeft e) α =
      mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ (Functor.whiskerLeft G e.hom ≫ α)) := by
  ext X
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit]

end OfNatIsoLeft

section CompCoherence

variable {AZ AY AX BZ BY BX : Type*} [Category* AZ] [Category* AY] [Category* AX]
  [Category* BZ] [Category* BY] [Category* BX]
  {LZ : AZ ⥤ BZ} {RZ : BZ ⥤ AZ} {LY : AY ⥤ BY} {RY : BY ⥤ AY} {LX : AX ⥤ BX} {RX : BX ⥤ AX}
  {Gq : AZ ⥤ AY} {Gp : AY ⥤ AX} {Gpq : AZ ⥤ AX} {Hq : BZ ⥤ BY} {Hp : BY ⥤ BX} {Hpq : BZ ⥤ BX}

/-- **Mates and composition isomorphisms.** Let `a_q : G_q ⋙ L_Y ⟶ L_Z ⋙ H_q`,
`a_p : G_p ⋙ L_X ⟶ L_Y ⋙ H_p` and `a_{pq} : G_{pq} ⋙ L_X ⟶ L_Z ⋙ H_{pq}` be 2-squares of left
adjoints compatible with composition isomorphisms `c_G : G_{pq} ≅ G_q ⋙ G_p` and
`c_H : H_{pq} ≅ H_q ⋙ H_p`. Then their mates `R ⋙ G ⟶ H ⋙ R` are compatible with `c_G` and
`c_H`. -/
lemma mateEquiv_app_comp_of_compCoherence (adjZ : LZ ⊣ RZ) (adjY : LY ⊣ RY) (adjX : LX ⊣ RX)
    (cG : Gpq ≅ Gq ⋙ Gp) (cH : Hpq ≅ Hq ⋙ Hp) (aq : TwoSquare Gq LZ LY Hq)
    (ap : TwoSquare Gp LY LX Hp) (apq : TwoSquare Gpq LZ LX Hpq)
    (h : ∀ M, apq.app M ≫ cH.hom.app (LZ.obj M) =
      LX.map (cG.hom.app M) ≫ ap.app (Gq.obj M) ≫ Hp.map (aq.app M))
    (K : BZ) :
    (mateEquiv adjZ adjX apq).app K ≫ RX.map (cH.hom.app K) =
      cG.hom.app (RZ.obj K) ≫ Gp.map ((mateEquiv adjZ adjY aq).app K) ≫
        (mateEquiv adjY adjX ap).app (Hq.obj K) := by
  have key : (mateEquiv adjZ adjX
      (TwoSquare.mk _ _ _ _ (apq ≫ Functor.whiskerLeft LZ cH.hom))) =
      (mateEquiv adjZ adjX (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight cG.hom LX ≫ (aq ≫ₕ ap)))) := by
    congr 2
    ext M
    simpa [TwoSquare.hComp] using h M
  rw [mateEquiv_comp_whiskerLeft, mateEquiv_whiskerRight_comp, mateEquiv_vcomp adjZ adjY adjX]
    at key
  simpa [TwoSquare.vComp] using NatTrans.congr_app key K

end CompCoherence

section Paste

variable {BX BY BZ CX CY CZ DX DY DZ : Type*} [Category* BX] [Category* BY] [Category* BZ]
  [Category* CX] [Category* CY] [Category* CZ] [Category* DX] [Category* DY] [Category* DZ]
  {GX : BX ⥤ CX} {GY : BY ⥤ CY} {GZ : BZ ⥤ CZ} {HX : CX ⥤ DX} {HY : CY ⥤ DY} {HZ : CZ ⥤ DZ}
  {up : BY ⥤ BX} {uq : BZ ⥤ BY} {upq : BZ ⥤ BX} {cp : CY ⥤ CX} {cq : CZ ⥤ CY}
  {cpq : CZ ⥤ CX} {wp : DY ⥤ DX} {wq : DZ ⥤ DY} {wpq : DZ ⥤ DX}

/-- **Pasting of 2-cells compatible with composition.** Let `γ_a : G ⋙ c_a ⟶ u_a ⋙ G` and
`δ_a : H ⋙ w_a ⟶ c_a ⋙ H` (for `a = p, q, pq`) be 2-cells compatible with composition
isomorphisms `C_u : u_{pq} ≅ u_q ⋙ u_p`, `C_c : c_{pq} ≅ c_q ⋙ c_p` and
`C_w : w_{pq} ≅ w_q ⋙ w_p`. Then their pastings `δ_a G ≫ H γ_a : (G ⋙ H) ⋙ w_a ⟶ u_a ⋙ G ⋙ H`
are compatible with `C_u` and `C_w`. -/
lemma app_comp_map_comp_of_compCoherence (Cu : upq ≅ uq ⋙ up) (Cc : cpq ≅ cq ⋙ cp)
    (Cw : wpq ≅ wq ⋙ wp) (γp : GY ⋙ cp ⟶ up ⋙ GX) (γq : GZ ⋙ cq ⟶ uq ⋙ GY)
    (γpq : GZ ⋙ cpq ⟶ upq ⋙ GX) (δp : HY ⋙ wp ⟶ cp ⋙ HX) (δq : HZ ⋙ wq ⟶ cq ⋙ HY)
    (δpq : HZ ⋙ wpq ⟶ cpq ⋙ HX)
    (hγ : ∀ M, γpq.app M ≫ GX.map (Cu.hom.app M) =
      Cc.hom.app (GZ.obj M) ≫ cp.map (γq.app M) ≫ γp.app (uq.obj M))
    (hδ : ∀ N, δpq.app N ≫ HX.map (Cc.hom.app N) =
      Cw.hom.app (HZ.obj N) ≫ wp.map (δq.app N) ≫ δp.app (cq.obj N)) (M : BZ) :
    (δpq.app (GZ.obj M) ≫ HX.map (γpq.app M)) ≫ HX.map (GX.map (Cu.hom.app M)) =
      Cw.hom.app (HZ.obj (GZ.obj M)) ≫ wp.map (δq.app (GZ.obj M) ≫ HY.map (γq.app M)) ≫
        δp.app (GY.obj (uq.obj M)) ≫ HX.map (γp.app (uq.obj M)) := by
  have hn := δp.naturality (γq.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Category.assoc, ← HX.map_comp, hγ, HX.map_comp, reassoc_of% (hδ (GZ.obj M)),
    wp.map_comp]
  rw [HX.map_comp, Category.assoc, reassoc_of% hn]

end Paste

end CategoryTheory
