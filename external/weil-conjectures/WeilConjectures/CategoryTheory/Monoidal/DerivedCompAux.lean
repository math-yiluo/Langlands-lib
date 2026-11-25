/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidality of a composition isomorphism of derived functors, abstractly

An abstract form of the computation showing that the composition isomorphism `L(f ≫ g) ≅ Lg ⋙ Lf`
of total left derived functors is compatible with tensor comparisons: all the derived functors,
counits, comparison maps and localization functors are variables, and the inputs are the
compatibilities of the counits with the composition isomorphism and with the comparisons.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

variable {HZ HY HX DZ DY DX : Type*} [Category HZ] [Category HY] [Category HX] [Category DZ]
  [Category DY] [Category DX] [MonoidalCategory HZ] [MonoidalCategory HY] [MonoidalCategory HX]
  [MonoidalCategory DZ] [MonoidalCategory DY] [MonoidalCategory DX]
  {QZ : HZ ⥤ DZ} {QY : HY ⥤ DY} {QX : HX ⥤ DX} [QZ.LaxMonoidal] [QY.LaxMonoidal] [QX.LaxMonoidal]
  {Gh : HZ ⥤ HY} {Fh : HY ⥤ HX} {Eh : HZ ⥤ HX} {Lg : DZ ⥤ DY} {Lf : DY ⥤ DX} {Le : DZ ⥤ DX}
  (εg : QZ ⋙ Lg ⟶ Gh ⋙ QY) (εf : QY ⋙ Lf ⟶ Fh ⋙ QX) (εe : QZ ⋙ Le ⟶ Eh ⋙ QX)
  (c : Le ≅ Lg ⋙ Lf)
  (mg : ∀ K M : DZ, Lg.obj (K ⊗ M) ⟶ Lg.obj K ⊗ Lg.obj M)
  (mf : ∀ K M : DY, Lf.obj (K ⊗ M) ⟶ Lf.obj K ⊗ Lf.obj M)
  (me : ∀ K M : DZ, Le.obj (K ⊗ M) ⟶ Le.obj K ⊗ Le.obj M)
  (P Q : HZ) (eh : ∀ K : HZ, Eh.obj K ⟶ Fh.obj (Gh.obj K))
  (Tg : Gh.obj P ⊗ Gh.obj Q ⟶ Gh.obj (P ⊗ Q))
  (Tf : Fh.obj (Gh.obj P) ⊗ Fh.obj (Gh.obj Q) ⟶ Fh.obj (Gh.obj P ⊗ Gh.obj Q))
  (Te : Eh.obj P ⊗ Eh.obj Q ⟶ Eh.obj (P ⊗ Q))

include εg εf εe c mg mf me P Q eh Tg Tf Te in
/-- The pointwise compatibility of a composition isomorphism of derived functors with the tensor
comparisons, on the image of `(P, Q)`, composed with the counit of the bifunctor. -/
lemma derivedComp_tensor_aux
    (hc : ∀ K, c.hom.app (QZ.obj K) ≫ Lf.map (εg.app K) ≫ εf.app (Gh.obj K) =
      εe.app K ≫ QX.map (eh K))
    (hfe : me (QZ.obj P) (QZ.obj Q) ≫ (εe.app P ⊗ₘ εe.app Q) ≫ μ QX _ _ ≫ QX.map Te =
      Le.map (μ QZ P Q) ≫ εe.app (P ⊗ Q))
    (hfg : mg (QZ.obj P) (QZ.obj Q) ≫ (εg.app P ⊗ₘ εg.app Q) ≫ μ QY _ _ ≫ QY.map Tg =
      Lg.map (μ QZ P Q) ≫ εg.app (P ⊗ Q))
    (hff : mf (QY.obj (Gh.obj P)) (QY.obj (Gh.obj Q)) ≫
        (εf.app (Gh.obj P) ⊗ₘ εf.app (Gh.obj Q)) ≫ μ QX _ _ ≫ QX.map Tf =
      Lf.map (μ QY (Gh.obj P) (Gh.obj Q)) ≫ εf.app (Gh.obj P ⊗ Gh.obj Q))
    (hnf : mf (Lg.obj (QZ.obj P)) (Lg.obj (QZ.obj Q)) ≫
        (Lf.map (εg.app P) ⊗ₘ Lf.map (εg.app Q)) =
      Lf.map (εg.app P ⊗ₘ εg.app Q) ≫ mf (QY.obj (Gh.obj P)) (QY.obj (Gh.obj Q)))
    (hT : (eh P ⊗ₘ eh Q) ≫ Tf ≫ Fh.map Tg = Te ≫ eh (P ⊗ Q))
    [IsIso (QX.map (eh (P ⊗ Q)))] :
    me (QZ.obj P) (QZ.obj Q) ≫ (εe.app P ⊗ₘ εe.app Q) ≫ μ QX _ _ ≫ QX.map Te =
      (c.hom.app (QZ.obj P ⊗ QZ.obj Q) ≫ Lf.map (mg _ _) ≫ mf _ _ ≫
        (c.inv.app (QZ.obj P) ⊗ₘ c.inv.app (QZ.obj Q))) ≫
        (εe.app P ⊗ₘ εe.app Q) ≫ μ QX _ _ ≫ QX.map Te := by
  have hc' (K : HZ) : c.inv.app (QZ.obj K) ≫ εe.app K ≫ QX.map (eh K) =
      Lf.map (εg.app K) ≫ εf.app (Gh.obj K) := by
    rw [← hc, Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono (QX.map (eh (P ⊗ Q)))]
  simp only [Category.assoc]
  rw [reassoc_of% hfe, ← hc]
  have hcn := c.hom.naturality_assoc (μ QZ P Q)
    (Lf.map (εg.app (P ⊗ Q)) ≫ εf.app (Gh.obj (P ⊗ Q)))
  simp only [Functor.comp_map] at hcn
  rw [hcn, ← QX.map_comp, ← hT, QX.map_comp, ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc, hc', hc',
    ← tensorHom_comp_tensorHom_assoc, reassoc_of% hnf, QX.map_comp, reassoc_of% hff]
  have hεn := εf.naturality Tg
  simp only [Functor.comp_map] at hεn
  rw [← hεn, ← Lf.map_comp_assoc, ← Lf.map_comp_assoc, ← Lf.map_comp_assoc, ← Lf.map_comp_assoc]
  simp only [Category.assoc]
  rw [hfg]

lemma comp_tensorHom_hom_eq_of_eq_comp_tensorHom_inv {D : Type*} [Category D] [MonoidalCategory D]
    {W A B A' B' : D} {m : W ⟶ A ⊗ B} {x : W ⟶ A' ⊗ B'} (e : A ≅ A') (e' : B ≅ B')
    (h : m = x ≫ (e.inv ⊗ₘ e'.inv)) : m ≫ (e.hom ⊗ₘ e'.hom) = x := by
  rw [h, Category.assoc, tensorHom_comp_tensorHom, e.inv_hom_id, e'.inv_hom_id, id_tensorHom_id,
    Category.comp_id]

section Id

variable {HZ DZ : Type*} [Category HZ] [Category DZ] [MonoidalCategory HZ] [MonoidalCategory DZ]
  {QZ : HZ ⥤ DZ} [QZ.LaxMonoidal] {Eh : HZ ⥤ HZ} {Le : DZ ⥤ DZ}

/-- The identity isomorphism `L(I) ≅ 𝟭` of a derived functor, read through the tensor
comparisons, on the image of `(P, Q)` composed with the counit of the bifunctor. -/
lemma derivedId_tensor_aux (εe : QZ ⋙ Le ⟶ Eh ⋙ QZ) (ι : Le ≅ 𝟭 DZ) (P Q : HZ)
    (j : ∀ K : HZ, Eh.obj K ⟶ K) (Te : Eh.obj P ⊗ Eh.obj Q ⟶ Eh.obj (P ⊗ Q))
    (hι : ∀ K, ι.hom.app (QZ.obj K) = εe.app K ≫ QZ.map (j K))
    (hT : (j P ⊗ₘ j Q) = Te ≫ j (P ⊗ Q)) [IsIso (QZ.map (j (P ⊗ Q)))] :
    (ι.hom.app (QZ.obj P ⊗ QZ.obj Q) ≫ (ι.inv.app (QZ.obj P) ⊗ₘ ι.inv.app (QZ.obj Q))) ≫
        (εe.app P ⊗ₘ εe.app Q) ≫ μ QZ _ _ ≫ QZ.map Te =
      Le.map (μ QZ P Q) ≫ εe.app (P ⊗ Q) := by
  have hinv (K : HZ) : ι.inv.app (QZ.obj K) ≫ εe.app K ≫ QZ.map (j K) = 𝟙 _ := by
    rw [← hι, Iso.inv_hom_id_app]
  rw [← cancel_mono (QZ.map (j (P ⊗ Q)))]
  simp only [Category.assoc]
  rw [← QZ.map_comp, ← hT, ← μ_natural, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc, hinv, hinv]
  erw [id_tensorHom_id, Category.id_comp]
  rw [← hι]
  exact (ι.hom.naturality (μ QZ P Q)).symm

end Id

section Braided

variable {HY HX DY DX : Type*} [Category HY] [Category HX] [Category DY] [Category DX]
  [MonoidalCategory HY] [MonoidalCategory HX] [MonoidalCategory DY] [MonoidalCategory DX]
  [BraidedCategory HY] [BraidedCategory HX] [BraidedCategory DY] [BraidedCategory DX]
  {QY : HY ⥤ DY} {QX : HX ⥤ DX} [QY.LaxMonoidal] [QX.LaxMonoidal] {Fh : HY ⥤ HX} {L : DY ⥤ DX}

/-- The compatibility of a tensor comparison `m : L (K ⊗ M) ⟶ L K ⊗ L M` of a derived functor
with the braidings, on the image of `(P, Q)`. -/
lemma derived_map_braiding_aux (ε : QY ⋙ L ⟶ Fh ⋙ QX)
    (m : ∀ K M : DY, L.obj (K ⊗ M) ⟶ L.obj K ⊗ L.obj M) (P Q : HY)
    (T : ∀ P Q : HY, Fh.obj P ⊗ Fh.obj Q ⟶ Fh.obj (P ⊗ Q))
    (hfac : ∀ P Q : HY, m (QY.obj P) (QY.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫ μ QX _ _ ≫
      QX.map (T P Q) = L.map (μ QY P Q) ≫ ε.app (P ⊗ Q))
    (hβY : (β_ (QY.obj P) (QY.obj Q)).hom ≫ μ QY Q P = μ QY P Q ≫ QY.map (β_ P Q).hom)
    (hβX : (β_ (QX.obj (Fh.obj P)) (QX.obj (Fh.obj Q))).hom ≫ μ QX (Fh.obj Q) (Fh.obj P) =
      μ QX (Fh.obj P) (Fh.obj Q) ≫ QX.map (β_ (Fh.obj P) (Fh.obj Q)).hom)
    (hT : T P Q ≫ Fh.map (β_ P Q).hom = (β_ (Fh.obj P) (Fh.obj Q)).hom ≫ T Q P)
    [IsIso (ε.app P)] [IsIso (ε.app Q)] [IsIso (μ QX (Fh.obj Q) (Fh.obj P))]
    [IsIso (QX.map (T Q P))] :
    L.map (β_ (QY.obj P) (QY.obj Q)).hom ≫ m (QY.obj Q) (QY.obj P) =
      m (QY.obj P) (QY.obj Q) ≫ (β_ (L.obj (QY.obj P)) (L.obj (QY.obj Q))).hom := by
  rw [← cancel_mono ((ε.app Q ⊗ₘ ε.app P) ≫ μ QX _ _ ≫ QX.map (T Q P))]
  simp only [Category.assoc]
  rw [hfac, ← L.map_comp_assoc, hβY, L.map_comp_assoc]
  have hn := ε.naturality (β_ P Q).hom
  simp only [Functor.comp_map] at hn
  rw [hn, ← BraidedCategory.braiding_naturality_assoc]
  erw [reassoc_of% hβX]
  rw [← QX.map_comp, ← hT, QX.map_comp, reassoc_of% (hfac P Q)]

lemma map_braiding_comp_of_iso {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D] {L : C ⥤ D}
    (m : ∀ K M : C, L.obj (K ⊗ M) ⟶ L.obj K ⊗ L.obj M)
    (hnat : ∀ {K K' M M' : C} (a : K ⟶ K') (b : M ⟶ M'),
      m K M ≫ (L.map a ⊗ₘ L.map b) = L.map (a ⊗ₘ b) ≫ m K' M')
    {K M K' M' : C} (eK : K' ≅ K) (eM : M' ≅ M)
    (h : L.map (β_ K' M').hom ≫ m M' K' = m K' M' ≫ (β_ (L.obj K') (L.obj M')).hom) :
    L.map (β_ K M).hom ≫ m M K = m K M ≫ (β_ (L.obj K) (L.obj M)).hom := by
  rw [← cancel_epi (L.map (eK.hom ⊗ₘ eM.hom)), ← L.map_comp_assoc,
    BraidedCategory.braiding_naturality, L.map_comp_assoc, ← hnat, reassoc_of% h,
    ← BraidedCategory.braiding_naturality, reassoc_of% (hnat eK.hom eM.hom)]

end Braided

end CategoryTheory
