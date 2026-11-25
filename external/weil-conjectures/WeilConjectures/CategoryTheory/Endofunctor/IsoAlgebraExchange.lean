/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!

# Transport of algebras along a pushforward and a homology functor

Consider the following data, modelled on the derived pushforward `Rf_*` of bounded constructible
complexes, its restriction to full subcategories, and the homology functors:

- functors `ι_X : 𝒦_X ⥤ 𝒟_X` and `ι_Y : 𝒦_Y ⥤ 𝒟_Y` (the inclusions of the full subcategories of
  bounded constructible complexes), `H_X : 𝒟_X ⥤ 𝒮_X` and `H_Y : 𝒟_Y ⥤ 𝒮_Y` (homology);
- endofunctors `L_X`, `L_Y` of `𝒟_X`, `𝒟_Y` with restrictions `L'_X`, `L'_Y` to `𝒦_X`, `𝒦_Y`
  through `c_X : L'_X ⋙ ι_X ≅ ι_X ⋙ L_X`, `c_Y` (the derived Frobenius pullbacks), and
  endofunctors `p_X`, `p_Y` of `𝒮_X`, `𝒮_Y` commuting with homology through
  `μ_X : H_X ⋙ p_X ≅ L_X ⋙ H_X`, `μ_Y` (the Frobenius pullbacks of module objects);
- functors `R : 𝒟_X ⥤ 𝒟_Y` with a restriction `R' : 𝒦_X ⥤ 𝒦_Y` through
  `c_R : R' ⋙ ι_Y ≅ ι_X ⋙ R` (the derived pushforward), and `r : 𝒮_X ⥤ 𝒮_Y` commuting with
  homology through `ρ : H_X ⋙ r ≅ R ⋙ H_Y` (the pushforward of module objects, which is exact);
- comparisons `E : R ⋙ L_Y ⟶ L_X ⋙ R`, `E' : R' ⋙ L'_Y ⟶ L'_X ⋙ R'` and `b : r ⋙ p_Y ⟶ p_X ⋙ r`
  (the base-change morphisms of the Frobenius square).

If `E'` is the restriction of `E` and `E` induces `b` on homology, the transport of algebras for
`L'_X` along `E'` followed by homology is isomorphic to homology followed by the transport along
`b` (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoHomologyExchangeIso`). This is the
compatibility of the homology sheaves of the pushforward of Weil objects with the pushforward of
Weil sheaves.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {𝒟X 𝒟Y 𝒦X 𝒦Y 𝒮X 𝒮Y : Type*} [Category 𝒟X] [Category 𝒟Y] [Category 𝒦X]
  [Category 𝒦Y] [Category 𝒮X] [Category 𝒮Y]
  {ιX : 𝒦X ⥤ 𝒟X} {ιY : 𝒦Y ⥤ 𝒟Y} {HX : 𝒟X ⥤ 𝒮X} {HY : 𝒟Y ⥤ 𝒮Y}
  {LX : 𝒟X ⥤ 𝒟X} {LY : 𝒟Y ⥤ 𝒟Y} {LX' : 𝒦X ⥤ 𝒦X} {LY' : 𝒦Y ⥤ 𝒦Y}
  {pX : 𝒮X ⥤ 𝒮X} {pY : 𝒮Y ⥤ 𝒮Y} {R : 𝒟X ⥤ 𝒟Y} {R' : 𝒦X ⥤ 𝒦Y} {r : 𝒮X ⥤ 𝒮Y}

/-- The commutation `H ⋙ p ≅ L' ⋙ H` of the restriction `L'` of `L` with `ι ⋙ H`, from
`μ : H ⋙ p ≅ L ⋙ H` and `c : L' ⋙ ι ≅ ι ⋙ L`. -/
noncomputable def restrictHomologyComparison {𝒟 𝒦 𝒮 : Type*} [Category 𝒟] [Category 𝒦]
    [Category 𝒮] {ι : 𝒦 ⥤ 𝒟} {H : 𝒟 ⥤ 𝒮} {L : 𝒟 ⥤ 𝒟} {L' : 𝒦 ⥤ 𝒦} {p : 𝒮 ⥤ 𝒮}
    (μ : H ⋙ p ≅ L ⋙ H) (c : L' ⋙ ι ≅ ι ⋙ L) : (ι ⋙ H) ⋙ p ≅ L' ⋙ (ι ⋙ H) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ι μ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c.symm H ≪≫ Functor.associator _ _ _

@[simp]
lemma restrictHomologyComparison_hom_app {𝒟 𝒦 𝒮 : Type*} [Category 𝒟] [Category 𝒦]
    [Category 𝒮] {ι : 𝒦 ⥤ 𝒟} {H : 𝒟 ⥤ 𝒮} {L : 𝒟 ⥤ 𝒟} {L' : 𝒦 ⥤ 𝒦} {p : 𝒮 ⥤ 𝒮}
    (μ : H ⋙ p ≅ L ⋙ H) (c : L' ⋙ ι ≅ ι ⋙ L) (K : 𝒦) :
    (restrictHomologyComparison μ c).hom.app K = μ.hom.app (ι.obj K) ≫ H.map (c.inv.app K) := by
  simp [restrictHomologyComparison]

/-- The commutation `R' ⋙ (ι_Y ⋙ H_Y) ≅ (ι_X ⋙ H_X) ⋙ r` of the restriction `R'` of `R` with
homology, from `c_R : R' ⋙ ι_Y ≅ ι_X ⋙ R` and `ρ : H_X ⋙ r ≅ R ⋙ H_Y`. -/
noncomputable def restrictHomologyPushforwardIso (cR : R' ⋙ ιY ≅ ιX ⋙ R)
    (ρ : HX ⋙ r ≅ R ⋙ HY) : R' ⋙ (ιY ⋙ HY) ≅ (ιX ⋙ HX) ⋙ r :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight cR HY ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ιX ρ.symm ≪≫ (Functor.associator _ _ _).symm

@[simp]
lemma restrictHomologyPushforwardIso_hom_app (cR : R' ⋙ ιY ≅ ιX ⋙ R) (ρ : HX ⋙ r ≅ R ⋙ HY)
    (K : 𝒦X) :
    (restrictHomologyPushforwardIso cR ρ).hom.app K =
      HY.map (cR.hom.app K) ≫ ρ.inv.app (ιX.obj K) := by
  simp [restrictHomologyPushforwardIso]

variable {cX : LX' ⋙ ιX ≅ ιX ⋙ LX} {cY : LY' ⋙ ιY ≅ ιY ⋙ LY} {μX : HX ⋙ pX ≅ LX ⋙ HX}
  {μY : HY ⋙ pY ≅ LY ⋙ HY} {cR : R' ⋙ ιY ≅ ιX ⋙ R} {ρ : HX ⋙ r ≅ R ⋙ HY}
  {E : R ⋙ LY ⟶ LX ⋙ R} {B' : R' ⋙ LY' ≅ LX' ⋙ R'} {b : r ⋙ pY ≅ pX ⋙ r}

/-- **Transport of algebras along a pushforward and homology.** If the comparison `B'` of the
restricted pushforward is the restriction of `E` (`hT`), and `E` induces `b` on homology (`hE`),
then transporting along `B'` and then along the restricted homology comparison is isomorphic to
transporting along the restricted homology comparison and then along `b`, through the
commutation of `R'` with homology. -/
noncomputable def mapOfNatIsoHomologyExchangeIso
    (hT : ∀ K : 𝒦X, cY.inv.app (R'.obj K) ≫ ιY.map (B'.hom.app K) ≫ cR.hom.app (LX'.obj K) =
      LY.map (cR.hom.app K) ≫ E.app (ιX.obj K) ≫ R.map (cX.inv.app K))
    (hE : ∀ M : 𝒟X, μY.hom.app (R.obj M) ≫ HY.map (E.app M) ≫ ρ.inv.app (LX.obj M) =
      pY.map (ρ.inv.app M) ≫ b.hom.app (HX.obj M) ≫ r.map (μX.hom.app M)) :
    mapOfNatIso B' ⋙ mapOfNatIso (restrictHomologyComparison μY cY) ≅
      mapOfNatIso (restrictHomologyComparison μX cX) ⋙ mapOfNatIso b :=
  mapOfNatIsoCompIso _ _ ≪≫ mapOfNatIsoIsoOfIso (restrictHomologyPushforwardIso cR ρ) (by
    ext K
    have nμ := μY.hom.naturality (cR.hom.app K)
    have nρ := ρ.inv.naturality (cX.inv.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at nμ nρ
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      compCommIso_hom_app, restrictHomologyComparison_hom_app,
      restrictHomologyPushforwardIso_hom_app, Functor.map_comp, Category.assoc, Functor.comp_obj,
      Functor.comp_map]
    have h := HY.congr_map (hT K)
    simp only [Functor.map_comp] at h
    rw [reassoc_of% h, ← reassoc_of% nμ, nρ, reassoc_of% (hE (ιX.obj K))]) ≪≫
    (mapOfNatIsoCompIso _ _).symm

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {𝒟X 𝒟Y 𝒦X 𝒦Y 𝒮X 𝒮Y : Type*} [Category 𝒟X] [Category 𝒟Y] [Category 𝒦X]
  [Category 𝒦Y] [Category 𝒮X] [Category 𝒮Y]
  {ιX : 𝒦X ⥤ 𝒟X} {ιY : 𝒦Y ⥤ 𝒟Y} {HX : 𝒟X ⥤ 𝒮X} {HY : 𝒟Y ⥤ 𝒮Y}
  {LX : 𝒟X ⥤ 𝒟X} {LY : 𝒟Y ⥤ 𝒟Y} {LX' : 𝒦X ⥤ 𝒦X} {LY' : 𝒦Y ⥤ 𝒦Y}
  {pX : 𝒮X ⥤ 𝒮X} {pY : 𝒮Y ⥤ 𝒮Y} {R : 𝒟X ⥤ 𝒟Y} {R' : 𝒦X ⥤ 𝒦Y} {r : 𝒮X ⥤ 𝒮Y}
  {LfD : 𝒟Y ⥤ 𝒟X} {LfK : 𝒦Y ⥤ 𝒦X}
  {cX : LX' ⋙ ιX ≅ ιX ⋙ LX} {cY : LY' ⋙ ιY ≅ ιY ⋙ LY} {μX : HX ⋙ pX ≅ LX ⋙ HX}
  {μY : HY ⋙ pY ≅ LY ⋙ HY} {cR : R' ⋙ ιY ≅ ιX ⋙ R} {ρ : HX ⋙ r ≅ R ⋙ HY}
  {cF : LfK ⋙ ιX ≅ ιY ⋙ LfD} {θD : LY ⋙ LfD ≅ LfD ⋙ LX} {θK : LY' ⋙ LfK ≅ LfK ⋙ LX'}
  {B' : R' ⋙ LY' ≅ LX' ⋙ R'} {b : r ⋙ pY ≅ pX ⋙ r} {bc : r ⋙ pY ⟶ pX ⋙ r}

/-- **Transport of algebras along a restricted pushforward and homology.** Let `adj : L_f ⊣ R`
be an adjunction restricting along the fully faithful `ι_X`, `ι_Y` to `L'_f ⊣ R'`, and let `B'` be
the exchange morphism of a comparison `θ' : L'_Y ⋙ L'_f ≅ L'_f ⋙ L'_X` for the restricted
adjunction. If `θ'` is the restriction of `θ : L_Y ⋙ L_f ≅ L_f ⋙ L_X` (`hθ`), and the exchange
morphism of `θ` induces `b` on homology (`hE`), then transporting along `B'` and then along the
restricted homology comparison is isomorphic to transporting along the restricted homology
comparison and then along `b`. -/
noncomputable def mapOfNatIsoHomologyExchangeIsoOfRestrict (adj : LfD ⊣ R)
    (hιX : ιX.FullyFaithful) (hιY : ιY.FullyFaithful)
    (hθ : ∀ K, LfD.map (cY.inv.app K) ≫ cF.inv.app (LY'.obj K) ≫ ιX.map (θK.hom.app K) =
      θD.hom.app (ιY.obj K) ≫ LX.map (cF.inv.app K) ≫ cX.inv.app (LfK.obj K))
    (hB' : B'.hom = Adjunction.exchangeRight (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm)
      (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm) θK)
    (hb : b.hom = bc)
    (hE : ∀ M, pY.map (ρ.hom.app M) ≫ μY.hom.app (R.obj M) ≫
        HY.map ((Adjunction.exchangeRight adj adj θD).app M) =
      bc.app (HX.obj M) ≫ r.map (μX.hom.app M) ≫ ρ.hom.app (LX.obj M)) :
    mapOfNatIso B' ⋙ mapOfNatIso (restrictHomologyComparison μY cY) ≅
      mapOfNatIso (restrictHomologyComparison μX cX) ⋙ mapOfNatIso b :=
  mapOfNatIsoHomologyExchangeIso (E := Adjunction.exchangeRight adj adj θD) (ρ := ρ) (cR := cR)
    (B' := B') (b := b) (fun K ↦ by
      have h := Adjunction.map_exchangeRight_app_of_comm
        (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm)
        (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm) θK adj adj θD cF.symm cR.symm
        cF.symm cR.symm cY.symm cX.symm
        (fun K ↦ Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ K)
        (fun K ↦ by
          rw [Adjunction.map_restrictFullyFaithful_counit_app]
          simp only [Iso.symm_hom, Iso.symm_inv, Iso.inv_hom_id_app_assoc, Functor.comp_obj]
          rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
          exact (congrArg (· ≫ adj.counit.app (ιX.obj K)) (LfD.map_id _)).trans
            (Category.id_comp _)) hθ K
      simp only [Iso.symm_hom, ← hB'] at h
      rw [← cancel_epi (LY.map (cR.inv.app K)), reassoc_of% h]
      simp [← Functor.map_comp_assoc])
    (fun M ↦ by
      rw [← cancel_epi (pY.map (ρ.hom.app M)), reassoc_of% (hE M), hb]
      simp [← Functor.map_comp_assoc])

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {𝒟X 𝒟Y 𝒦X 𝒦Y 𝒮X 𝒮Y : Type*} [Category 𝒟X] [Category 𝒟Y] [Category 𝒦X]
  [Category 𝒦Y] [Category 𝒮X] [Category 𝒮Y]
  {ιX : 𝒦X ⥤ 𝒟X} {ιY : 𝒦Y ⥤ 𝒟Y} {HX : 𝒟X ⥤ 𝒮X} {HY : 𝒟Y ⥤ 𝒮Y}
  {LX : 𝒟X ⥤ 𝒟X} {LY : 𝒟Y ⥤ 𝒟Y} {LX' : 𝒦X ⥤ 𝒦X} {LY' : 𝒦Y ⥤ 𝒦Y}
  {pX : 𝒮X ⥤ 𝒮X} {pY : 𝒮Y ⥤ 𝒮Y} {R : 𝒟X ⥤ 𝒟Y} {R' : 𝒦X ⥤ 𝒦Y} {r : 𝒮X ⥤ 𝒮Y}
  {LfD : 𝒟Y ⥤ 𝒟X} {LfK : 𝒦Y ⥤ 𝒦X}
  {cX : LX' ⋙ ιX ≅ ιX ⋙ LX} {cY : LY' ⋙ ιY ≅ ιY ⋙ LY} {μX : HX ⋙ pX ≅ LX ⋙ HX}
  {μY : HY ⋙ pY ≅ LY ⋙ HY} {cR : R' ⋙ ιY ≅ ιX ⋙ R} {ρ : HX ⋙ r ≅ R ⋙ HY}
  {cF : LfK ⋙ ιX ≅ ιY ⋙ LfD} {θD : LY ⋙ LfD ≅ LfD ⋙ LX} {θK : LY' ⋙ LfK ≅ LfK ⋙ LX'}
  {B' : R' ⋙ LY' ≅ LX' ⋙ R'} {b : r ⋙ pY ≅ pX ⋙ r} {bc : r ⋙ pY ⟶ pX ⋙ r}

/-- `Endofunctor.IsoAlgebra.mapOfNatIsoHomologyExchangeIsoOfRestrict` at an object, for functors
given through equations, so that concrete instances can use their own functors.

Implementation note: the categories are passed as variables, with their category instances,
together with `Sigma`-type equations to the generic ones, and the functors through `HEq`
hypotheses, as in `Endofunctor.IsoAlgebra.nonempty_obj_obj_iso_of_eq`. -/
theorem nonempty_mapOfNatIso_obj_iso_of_restrict (adj : LfD ⊣ R)
    (hιX : ιX.FullyFaithful) (hιY : ιY.FullyFaithful)
    (hθ : ∀ K, LfD.map (cY.inv.app K) ≫ cF.inv.app (LY'.obj K) ≫ ιX.map (θK.hom.app K) =
      θD.hom.app (ιY.obj K) ≫ LX.map (cF.inv.app K) ≫ cX.inv.app (LfK.obj K))
    (hB' : B'.hom = Adjunction.exchangeRight (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm)
      (adj.restrictFullyFaithful hιY hιX cF.symm cR.symm) θK)
    (hb : b.hom = bc)
    (hE : ∀ M, pY.map (ρ.hom.app M) ≫ μY.hom.app (R.obj M) ≫
        HY.map ((Adjunction.exchangeRight adj adj θD).app M) =
      bc.app (HX.obj M) ≫ r.map (μX.hom.app M) ≫ ρ.hom.app (LX.obj M))
    (𝒜X 𝒜Y 𝒲X 𝒲Y : Type _) {i𝒜X : Category 𝒜X} {i𝒜Y : Category 𝒜Y} {i𝒲X : Category 𝒲X}
    {i𝒲Y : Category 𝒲Y} (K : 𝒜X) (W : 𝒜X ⥤ 𝒜Y) (HXa : 𝒜X ⥤ 𝒲X) (HYa : 𝒜Y ⥤ 𝒲Y)
    (V : 𝒲X ⥤ 𝒲Y)
    (h𝒜X : (⟨𝒜X, i𝒜X⟩ : Σ A : Type _, Category A) = ⟨IsoAlgebra LX', inferInstance⟩)
    (h𝒜Y : (⟨𝒜Y, i𝒜Y⟩ : Σ A : Type _, Category A) = ⟨IsoAlgebra LY', inferInstance⟩)
    (h𝒲X : (⟨𝒲X, i𝒲X⟩ : Σ A : Type _, Category A) = ⟨IsoAlgebra pX, inferInstance⟩)
    (h𝒲Y : (⟨𝒲Y, i𝒲Y⟩ : Σ A : Type _, Category A) = ⟨IsoAlgebra pY, inferInstance⟩)
    (hW : HEq W (mapOfNatIso B'))
    (hHX : HEq HXa (mapOfNatIso (restrictHomologyComparison μX cX)))
    (hHY : HEq HYa (mapOfNatIso (restrictHomologyComparison μY cY)))
    (hV : HEq V (mapOfNatIso b)) :
    Nonempty (HYa.obj (W.obj K) ≅ V.obj (HXa.obj K)) := by
  cases h𝒜X
  cases h𝒜Y
  cases h𝒲X
  cases h𝒲Y
  cases hW
  cases hHX
  cases hHY
  cases hV
  exact ⟨(mapOfNatIsoHomologyExchangeIsoOfRestrict adj hιX hιY hθ hB' hb hE).app K⟩

end CategoryTheory.Endofunctor.IsoAlgebra
