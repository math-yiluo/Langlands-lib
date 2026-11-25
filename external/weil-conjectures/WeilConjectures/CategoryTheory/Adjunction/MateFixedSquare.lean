/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Exchange transformations across a base-change square

Consider a commutative square of "spaces" `F --ι--> C --c--> P` and `F --d--> X --Δ--> P`, with
`ι` and `Δ` proper, encoded on categories of sheaves `DC, DF, DX, DP` by

* adjunctions `c_! ⊣ c^!` and `d_! ⊣ d^!` (`cL ⊣ cR`, `dL ⊣ dR`);
* adjunctions `ι^* ⊣ ι_*` and `Δ^* ⊣ Δ_*` (`ιU ⊣ ιS`, `ΔU ⊣ ΔS`), together with functors
  `ι_!`, `Δ_!` (`ιL`, `ΔL`) and isomorphisms `ι_! ≅ ι_*`, `Δ_! ≅ Δ_*`;
* the composition isomorphism `Sq : ι_! ⋙ c_! ≅ d_! ⋙ Δ_!` and the base change isomorphism
  `BC : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`, assumed to be the mate of `Sq`;
* the exceptional base change `B : Δ_* ⋙ c^! ≅ d^! ⋙ ι_*`, the conjugate of `BC⁻¹`;

and the same data on a second row (primed). Let `Ψ_C, Ψ_F, Ψ_X, Ψ_P` be functors from the first
row to the second, with

* pullback exchanges `α_ι : Ψ_C ⋙ ι'^* ⟶ ι^* ⋙ Ψ_F` and `α_Δ : Ψ_P ⋙ Δ'^* ⟶ Δ^* ⋙ Ψ_X`, and
  their mates, the proper exchanges `χ_ι : ι_* ⋙ Ψ_C ⟶ Ψ_F ⋙ ι'_*` and
  `χ_Δ : Δ_* ⋙ Ψ_P ⟶ Ψ_X ⋙ Δ'_*`;
* compact-support exchanges `ν_c, ν_d, ν_ι, ν_Δ` (`ν_f : Ψ ⋙ f'_! ⟶ f_! ⋙ Ψ`), with `ν_ι`, `ν_Δ`
  inverse to `χ_ι`, `χ_Δ` under `ι_! ≅ ι_*`, `Δ_! ≅ Δ_*`, and compatible with the composition
  `cι = Δd`;
* the exceptional exchanges `β_c`, `β_d`, the mates of `ν_c`, `ν_d`.

Then the *fixed-square identity*

```
Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(Δ_*)
```

holds (`CategoryTheory.fixedSquare_of_compactSupportExchange`). This is the abstract form of
blueprint `sec-Base-change-for-nearby-cycles` (6), proved as in the blueprint: after taking
adjoints, both sides are the exchange of the composite `cι = Δd` followed by the counit of
`d_! ⊣ d^!`.

-/

@[expose] public section

namespace CategoryTheory

variable {DC DF DX DP DC' DF' DX' DP' : Type*} [Category DC] [Category DF] [Category DX]
  [Category DP] [Category DC'] [Category DF'] [Category DX'] [Category DP']
  {cL : DC ⥤ DP} {cR : DP ⥤ DC} {dL : DF ⥤ DX} {dR : DX ⥤ DF}
  {ιU : DC ⥤ DF} {ιS : DF ⥤ DC} {ιL : DF ⥤ DC} {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP} {ΔL : DX ⥤ DP}
  {cL' : DC' ⥤ DP'} {cR' : DP' ⥤ DC'} {dL' : DF' ⥤ DX'} {dR' : DX' ⥤ DF'}
  {ιU' : DC' ⥤ DF'} {ιS' : DF' ⥤ DC'} {ιL' : DF' ⥤ DC'} {ΔU' : DP' ⥤ DX'} {ΔS' : DX' ⥤ DP'}
  {ΔL' : DX' ⥤ DP'}
  (adjc : cL ⊣ cR) (adjd : dL ⊣ dR) (adjι : ιU ⊣ ιS) (adjΔ : ΔU ⊣ ΔS)
  (adjc' : cL' ⊣ cR') (adjd' : dL' ⊣ dR') (adjι' : ιU' ⊣ ιS') (adjΔ' : ΔU' ⊣ ΔS')
  (isoι : ιL ≅ ιS) (isoΔ : ΔL ≅ ΔS) (isoι' : ιL' ≅ ιS') (isoΔ' : ΔL' ≅ ΔS')
  (Sq : ιL ⋙ cL ≅ dL ⋙ ΔL) (Sq' : ιL' ⋙ cL' ≅ dL' ⋙ ΔL')
  (BC : cL ⋙ ΔU ≅ ιU ⋙ dL) (BC' : cL' ⋙ ΔU' ≅ ιU' ⋙ dL')
  {ΨC : DC ⥤ DC'} {ΨF : DF ⥤ DF'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
  (αι : ΨC ⋙ ιU' ⟶ ιU ⋙ ΨF) (αΔ : ΨP ⋙ ΔU' ⟶ ΔU ⋙ ΨX)
  (νc : ΨC ⋙ cL' ⟶ cL ⋙ ΨP) (νd : ΨF ⋙ dL' ⟶ dL ⋙ ΨX)
  (νι : ΨF ⋙ ιL' ⟶ ιL ⋙ ΨC) (νΔ : ΨX ⋙ ΔL' ⟶ ΔL ⋙ ΨP)

section

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- The components of the inverse mate, in terms of the unit and the counit. -/
private lemma mateEquiv_symm_app_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm β).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (β.app _) ≫ adj₂.counit.app _ := by
  simp

/-- The mate with respect to adjunctions transported along isomorphisms of right adjoints. -/
private lemma mateEquiv_ofNatIsoRight_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (i₁ : R₁ ≅ R₁')
    (i₂ : R₂ ≅ R₂') (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv (adj₁.ofNatIsoRight i₁) (adj₂.ofNatIsoRight i₂) α).app d =
      G.map (i₁.inv.app d) ≫ (mateEquiv adj₁ adj₂ α).app d ≫ i₂.hom.app _ := by
  have hα : α.app _ ≫ H.map (L₁.map (i₁.inv.app d)) =
      L₂.map (G.map (i₁.inv.app d)) ≫ α.app _ := (α.naturality _).symm
  simp only [Functor.comp_obj, mateEquiv_apply, Adjunction.ofNatIsoRight_unit,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_twice, Adjunction.ofNatIsoRight_counit,
    Functor.whiskerRight_comp, Functor.whiskerRight_twice, Category.assoc, Iso.inv_hom_id_assoc,
    NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    NatTrans.naturality, NatTrans.naturality_assoc]
  rw [← R₂'.map_comp_assoc, hα, R₂'.map_comp_assoc, ← i₂.hom.naturality_assoc,
    ← adj₂.unit_naturality_assoc]

end

/-- Step 1 of the fixed-square identity: the base change isomorphisms intertwine the
compact-support exchanges `ν_c`, `ν_d` with the pullback exchanges `α_ι`, `α_Δ`. -/
private lemma baseChange_exchange_comm
    (hBC : BC.hom = (mateEquiv (adjι.ofNatIsoRight isoι.symm)
      (adjΔ.ofNatIsoRight isoΔ.symm)).symm Sq.hom)
    (hBC' : BC'.hom = (mateEquiv (adjι'.ofNatIsoRight isoι'.symm)
      (adjΔ'.ofNatIsoRight isoΔ'.symm)).symm Sq'.hom)
    (hι : ∀ Q : DF, ΨC.map (isoι.hom.app Q) ≫ (mateEquiv adjι adjι' αι).app Q ≫
      isoι'.inv.app (ΨF.obj Q) ≫ νι.app Q = 𝟙 _)
    (hΔ : ∀ Q : DX, νΔ.app Q ≫ ΨP.map (isoΔ.hom.app Q) ≫ (mateEquiv adjΔ adjΔ' αΔ).app Q ≫
      isoΔ'.inv.app (ΨX.obj Q) = 𝟙 _)
    (hcomp : ∀ Q : DF, cL'.map (νι.app Q) ≫ νc.app (ιL.obj Q) ≫ ΨP.map (Sq.hom.app Q) =
      Sq'.hom.app (ΨF.obj Q) ≫ ΔL'.map (νd.app Q) ≫ νΔ.app (dL.obj Q))
    (N : DC) :
    BC'.hom.app (ΨC.obj N) ≫ dL'.map (αι.app N) ≫ νd.app (ιU.obj N) =
      ΔU'.map (νc.app N) ≫ αΔ.app (cL.obj N) ≫ ΨX.map (BC.hom.app N) := by
  set aι := adjι.ofNatIsoRight isoι.symm
  set aΔ := adjΔ.ofNatIsoRight isoΔ.symm
  set aι' := adjι'.ofNatIsoRight isoι'.symm
  set aΔ' := adjΔ'.ofNatIsoRight isoΔ'.symm
  have hSq {A B : DF'} (g : A ⟶ B) : Sq'.hom.app A ≫ ΔL'.map (dL'.map g) =
      cL'.map (ιL'.map g) ≫ Sq'.hom.app B := (Sq'.hom.naturality g).symm
  have hχΔ (Z : DX) : ΔU'.map ((mateEquiv aΔ aΔ' αΔ).app Z) ≫ aΔ'.counit.app (ΨX.obj Z) =
      αΔ.app (ΔL.obj Z) ≫ ΨX.map (aΔ.counit.app Z) := mateEquiv_counit aΔ aΔ' αΔ Z
  have hε {A B : DX'} (g : A ⟶ B) : aΔ'.counit.app A ≫ g =
      ΔU'.map (ΔL'.map g) ≫ aΔ'.counit.app B := (aΔ'.counit_naturality g).symm
  have hνc {A B : DC} (g : A ⟶ B) : cL'.map (ΨC.map g) ≫ νc.app B =
      νc.app A ≫ ΨP.map (cL.map g) := νc.naturality g
  have hαΔ {A B : DP} (g : A ⟶ B) : ΔU'.map (ΨP.map g) ≫ αΔ.app B =
      αΔ.app A ≫ ΨX.map (ΔU.map g) := αΔ.naturality g
  have hcomp' (Q : DF) : Sq'.hom.app (ΨF.obj Q) ≫ ΔL'.map (νd.app Q) =
      cL'.map (νι.app Q) ≫ νc.app (ιL.obj Q) ≫ ΨP.map (Sq.hom.app Q) ≫
        (mateEquiv aΔ aΔ' αΔ).app (dL.obj Q) := by
    rw [reassoc_of% hcomp Q, mateEquiv_ofNatIsoRight_app, Iso.symm_inv, Iso.symm_hom, hΔ]
    simp
  have hunit : aι'.unit.app (ΨC.obj N) ≫ ιL'.map (αι.app N) ≫ νι.app (ιU.obj N) =
      ΨC.map (aι.unit.app N) := by
    rw [← reassoc_of% unit_mateEquiv aι aι' αι N, mateEquiv_ofNatIsoRight_app, Iso.symm_inv,
      Iso.symm_hom]
    simp only [Category.assoc]
    rw [hι]
    simp
  have i1 : cL'.map (aι'.unit.app (ΨC.obj N)) ≫ Sq'.hom.app (ιU'.obj (ΨC.obj N)) ≫
      ΔL'.map (dL'.map (αι.app N) ≫ νd.app (ιU.obj N)) =
      cL'.map (ΨC.map (aι.unit.app N)) ≫ νc.app (ιL.obj (ιU.obj N)) ≫
        ΨP.map (Sq.hom.app (ιU.obj N)) ≫ (mateEquiv aΔ aΔ' αΔ).app (dL.obj (ιU.obj N)) := by
    rw [ΔL'.map_comp, reassoc_of% hSq (αι.app N), hcomp', ← cL'.map_comp_assoc,
      ← cL'.map_comp_assoc, Category.assoc, hunit]
  rw [hBC', hBC, mateEquiv_symm_app_eq, mateEquiv_symm_app_eq]
  simp only [Category.assoc]
  rw [hε, ← ΔU'.map_comp_assoc, ← ΔU'.map_comp_assoc, Category.assoc, i1]
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  rw [hχΔ, ← ΔU'.map_comp_assoc, hνc, ΔU'.map_comp_assoc, reassoc_of% hαΔ,
    reassoc_of% hαΔ]
  rfl

/-- **The fixed-square identity for exchange transformations** (the abstract form of blueprint
`sec-Base-change-for-nearby-cycles` (6)): if the base change isomorphisms `BC`, `BC'` are the mates
of the composition isomorphisms `Sq`, `Sq'`, if the compact-support exchanges `ν_ι`, `ν_Δ` of the
proper maps are inverse to the proper exchanges `χ_ι`, `χ_Δ` (the mates of `α_ι`, `α_Δ`), and if
the compact-support exchanges are compatible with the composition `cι = Δd`, then the mates
`β_c`, `β_d` of `ν_c`, `ν_d` satisfy
`Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(Δ_*)`, where `B` and `B'` are the conjugates
of `BC⁻¹` and `BC'⁻¹`. That is, for `M : DX` the square
```
Ψ_C c^! Δ_* M --Ψ_C(B)--> Ψ_C ι_* d^! M --χ_ι--> ι'_* Ψ_F d^! M
      |                                                 |
   β_c(Δ_* M)                                       ι'_* β_d
      v                                                 v
c'^! Ψ_P Δ_* M --c'^!(χ_Δ)--> c'^! Δ'_* Ψ_X M --B'--> ι'_* d'^! Ψ_X M
```
commutes. -/
theorem fixedSquare_of_compactSupportExchange
    (hBC : BC.hom = (mateEquiv (adjι.ofNatIsoRight isoι.symm)
      (adjΔ.ofNatIsoRight isoΔ.symm)).symm Sq.hom)
    (hBC' : BC'.hom = (mateEquiv (adjι'.ofNatIsoRight isoι'.symm)
      (adjΔ'.ofNatIsoRight isoΔ'.symm)).symm Sq'.hom)
    (hι : ∀ Q : DF, ΨC.map (isoι.hom.app Q) ≫ (mateEquiv adjι adjι' αι).app Q ≫
      isoι'.inv.app (ΨF.obj Q) ≫ νι.app Q = 𝟙 _)
    (hΔ : ∀ Q : DX, νΔ.app Q ≫ ΨP.map (isoΔ.hom.app Q) ≫ (mateEquiv adjΔ adjΔ' αΔ).app Q ≫
      isoΔ'.inv.app (ΨX.obj Q) = 𝟙 _)
    (hcomp₀ : Functor.whiskerRight νι cL' ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ιL νc ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight Sq.hom ΨP =
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ΨF Sq'.hom ≫
          (Functor.associator _ _ _).inv ≫ Functor.whiskerRight νd ΔL' ≫
            (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft dL νΔ ≫
              (Functor.associator _ _ _).inv)
    (M : DX) :
    ΨC.map ((conjugateIsoEquiv (adjc.comp adjΔ) (adjι.comp adjd) BC.symm).hom.app M) ≫
        (mateEquiv adjι adjι' αι).app (dR.obj M) ≫ ιS'.map ((mateEquiv adjd adjd' νd).app M) =
      (mateEquiv adjc adjc' νc).app (ΔS.obj M) ≫ cR'.map ((mateEquiv adjΔ adjΔ' αΔ).app M) ≫
        (conjugateIsoEquiv (adjc'.comp adjΔ') (adjι'.comp adjd') BC'.symm).hom.app
          (ΨX.obj M) := by
  have hcomp (Q : DF) : cL'.map (νι.app Q) ≫ νc.app (ιL.obj Q) ≫ ΨP.map (Sq.hom.app Q) =
      Sq'.hom.app (ΨF.obj Q) ≫ ΔL'.map (νd.app Q) ≫ νΔ.app (dL.obj Q) := by
    simpa using congr_app hcomp₀ Q
  have step2 (N : DC) : dL'.map (αι.app N) ≫ νd.app (ιU.obj N) ≫ ΨX.map (BC.inv.app N) =
      BC'.inv.app (ΨC.obj N) ≫ ΔU'.map (νc.app N) ≫ αΔ.app (cL.obj N) := by
    rw [← cancel_epi (BC'.hom.app (ΨC.obj N)), reassoc_of% (baseChange_exchange_comm (hBC := hBC)
      (hBC' := hBC') (hι := hι) (hΔ := hΔ) (hcomp := hcomp) (N := N)),
      Iso.hom_inv_id_app_assoc, ← ΨX.map_comp, Iso.hom_inv_id_app]
    simp
  have hB : dL.map (ιU.map ((conjugateIsoEquiv (adjc.comp adjΔ) (adjι.comp adjd) BC.symm).hom.app
      M)) ≫ dL.map (adjι.counit.app (dR.obj M)) ≫ adjd.counit.app M =
      BC.inv.app (cR.obj (ΔS.obj M)) ≫ ΔU.map (adjc.counit.app (ΔS.obj M)) ≫
        adjΔ.counit.app M := by
    rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    have h := conjugateEquiv_counit (adjc.comp adjΔ) (adjι.comp adjd) BC.inv M
    simp only [Functor.comp_map, Adjunction.comp_counit_app] at h
    exact h
  have hB' : dL'.map (ιU'.map ((conjugateIsoEquiv (adjc'.comp adjΔ') (adjι'.comp adjd')
      BC'.symm).hom.app (ΨX.obj M))) ≫ dL'.map (adjι'.counit.app (dR'.obj (ΨX.obj M))) ≫
        adjd'.counit.app (ΨX.obj M) =
      BC'.inv.app (cR'.obj (ΔS'.obj (ΨX.obj M))) ≫
        ΔU'.map (adjc'.counit.app (ΔS'.obj (ΨX.obj M))) ≫ adjΔ'.counit.app (ΨX.obj M) := by
    rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    have h := conjugateEquiv_counit (adjc'.comp adjΔ') (adjι'.comp adjd') BC'.inv (ΨX.obj M)
    simp only [Functor.comp_map, Adjunction.comp_counit_app] at h
    exact h
  have hιc' : ιU'.map (ιS'.map ((mateEquiv adjd adjd' νd).app M)) ≫
      adjι'.counit.app (dR'.obj (ΨX.obj M)) =
      adjι'.counit.app _ ≫ (mateEquiv adjd adjd' νd).app M := adjι'.counit_naturality _
  set Bh := (conjugateIsoEquiv (adjc.comp adjΔ) (adjι.comp adjd) BC.symm).hom
  set χΔ := mateEquiv adjΔ adjΔ' αΔ
  set βc := mateEquiv adjc adjc' νc
  have hcc' : cL'.map (cR'.map (χΔ.app M)) ≫ adjc'.counit.app (ΔS'.obj (ΨX.obj M)) =
      adjc'.counit.app _ ≫ χΔ.app M := adjc'.counit_naturality _
  have hχι (Z : DF) : ιU'.map ((mateEquiv adjι adjι' αι).app Z) ≫ adjι'.counit.app (ΨF.obj Z) =
      αι.app (ιS.obj Z) ≫ ΨF.map (adjι.counit.app Z) := mateEquiv_counit adjι adjι' αι Z
  have hχΔ : ΔU'.map (χΔ.app M) ≫ adjΔ'.counit.app (ΨX.obj M) =
      αΔ.app (ΔS.obj M) ≫ ΨX.map (adjΔ.counit.app M) := mateEquiv_counit adjΔ adjΔ' αΔ M
  have hβd : dL'.map ((mateEquiv adjd adjd' νd).app M) ≫ adjd'.counit.app (ΨX.obj M) =
      νd.app (dR.obj M) ≫ ΨX.map (adjd.counit.app M) := mateEquiv_counit adjd adjd' νd M
  have hβc : cL'.map (βc.app (ΔS.obj M)) ≫
      adjc'.counit.app (ΨP.obj (ΔS.obj M)) =
      νc.app (cR.obj (ΔS.obj M)) ≫ ΨP.map (adjc.counit.app (ΔS.obj M)) :=
    mateEquiv_counit adjc adjc' νc (ΔS.obj M)
  have hαι : ιU'.map (ΨC.map (Bh.app M)) ≫ αι.app (ιS.obj (dR.obj M)) =
      αι.app (cR.obj (ΔS.obj M)) ≫ ΨF.map (ιU.map (Bh.app M)) := αι.naturality _
  have hαΔ : ΔU'.map (ΨP.map (adjc.counit.app (ΔS.obj M))) ≫ αΔ.app (ΔS.obj M) =
      αΔ.app _ ≫ ΨX.map (ΔU.map (adjc.counit.app (ΔS.obj M))) := αΔ.naturality _
  have hνd1 : dL'.map (ΨF.map (adjι.counit.app (dR.obj M))) ≫ νd.app (dR.obj M) =
      νd.app _ ≫ ΨX.map (dL.map (adjι.counit.app (dR.obj M))) := νd.naturality _
  have hνd2 : dL'.map (ΨF.map (ιU.map (Bh.app M))) ≫ νd.app (ιU.obj (ιS.obj (dR.obj M))) =
      νd.app _ ≫ ΨX.map (dL.map (ιU.map (Bh.app M))) := νd.naturality _
  have hBCi'1 : dL'.map (ιU'.map (cR'.map (χΔ.app M))) ≫
      BC'.inv.app (cR'.obj (ΔS'.obj (ΨX.obj M))) =
      BC'.inv.app _ ≫ ΔU'.map (cL'.map (cR'.map (χΔ.app M))) := BC'.inv.naturality _
  have hBCi'2 : dL'.map (ιU'.map (βc.app (ΔS.obj M))) ≫
      BC'.inv.app (cR'.obj (ΨP.obj (ΔS.obj M))) =
      BC'.inv.app _ ≫ ΔU'.map (cL'.map (βc.app (ΔS.obj M))) := BC'.inv.naturality _
  apply ((adjι'.comp adjd').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.comp_map, Adjunction.comp_counit_app,
    Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [← dL'.map_comp, hιc', dL'.map_comp]
  slice_lhs 4 5 => rw [hβd]
  slice_lhs 2 3 => rw [← dL'.map_comp, hχι, dL'.map_comp]
  slice_lhs 1 2 => rw [← dL'.map_comp, hαι, dL'.map_comp]
  slice_lhs 3 4 => rw [hνd1]
  slice_lhs 2 3 => erw [hνd2]
  slice_lhs 3 5 => rw [← ΨX.map_comp, ← ΨX.map_comp, hB]
  slice_rhs 3 5 => rw [hB']
  slice_rhs 2 3 => rw [hBCi'1]
  slice_rhs 1 2 => erw [hBCi'2]
  slice_rhs 3 4 => rw [← ΔU'.map_comp, hcc', ΔU'.map_comp]
  slice_rhs 4 5 => rw [hχΔ]
  slice_rhs 2 3 => rw [← ΔU'.map_comp, hβc, ΔU'.map_comp]
  slice_rhs 3 4 => rw [hαΔ]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% step2]
  rfl

end CategoryTheory
