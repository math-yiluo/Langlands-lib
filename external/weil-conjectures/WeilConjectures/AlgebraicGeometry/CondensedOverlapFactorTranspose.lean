/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedLocalCoefficientAdjoints
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

/-!
# Transposing a fixed coefficient factor on an overlap

Source: archived `TwoColimit.lean`, overlap Hom descent, scalar adjunction calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] sheafMonoidalCategory sheafBraidedCategory

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  upperStarLowerStarAdjunction

section Comparison
variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}

/-- Forward component with its functor endpoints fixed.

Source: component formula for natural transformations, used in archived `TwoColimit.lean`.
(auxiliary; not a blueprint node). -/
def comparisonHom (e : F ≅ G) (M : C) : F.obj M ⟶ G.obj M := e.hom.app M

/-- Inverse component with its functor endpoints fixed.

Source: component formula for natural isomorphisms, used in archived `TwoColimit.lean`.
(auxiliary; not a blueprint node). -/
def comparisonInv (e : F ≅ G) (M : C) : G.obj M ⟶ F.obj M := e.inv.app M

/-- Component presentation of a natural isomorphism; its data is unchanged.

Source: the component presentation of natural isomorphisms in the overlap calculation
of archived `TwoColimit.lean`. The generic equality `componentComparison_eq` proves
that this representation is exactly the given isomorphism, with no chosen data.
(auxiliary; not a blueprint node). -/
def componentComparison (e : F ≅ G) : F ≅ G :=
  NatIso.ofComponents (fun M ↦
    { hom := comparisonHom e M
      inv := comparisonInv e M
      hom_inv_id := e.hom_inv_id_app M
      inv_hom_id := e.inv_hom_id_app M })
    (fun k ↦ e.hom.naturality k)

private theorem componentComparison_eq (e : F ≅ G) : componentComparison e = e := by
  rfl

/-- Component presentation of the specified commutative-square comparison.

Source: archived `TwoColimit.lean`, overlap comparison. The equality
`overlapComparison_eq_original` identifies this with `upperStarCompIso`.
(auxiliary; not a blueprint node). -/
noncomputable def overlapComparison
    {W U V X : Scheme.{u}} {p : W ⟶ U} {g : U ⟶ X}
    {q : W ⟶ V} {h : V ⟶ X} (w : p ≫ g = q ≫ h) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} p ≅
      upperStar Ab.{u + 1} h ⋙ upperStar Ab.{u + 1} q :=
  componentComparison (upperStarCompIso Ab.{u + 1} w)

private theorem overlapComparison_eq_original
    {W U V X : Scheme.{u}} {p : W ⟶ U} {g : U ⟶ X}
    {q : W ⟶ V} {h : V ⟶ X} (w : p ≫ g = q ≫ h) :
    overlapComparison w = upperStarCompIso Ab.{u + 1} w :=
  componentComparison_eq _

end Comparison

section LocalUnits
variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (Y : Scheme.{u}) (g : Y ⟶ X)
  (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
  (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
  (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)

private lemma localAdjoint_eq_mixed :
    (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF).hom =
      (Mod.mixedScalarMap
        ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
        ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
        ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
        ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
        ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
          padicSubfieldRingObjMap_comp_toPadicAlgCl])
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
          padicSubfieldRingObjMap_comp_toPadicAlgCl]) P).hom ≫ a.hom := by
  rfl

private lemma localAdjoint_unit :
    (Mod.extendUnit ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF))) P).hom ≫
        (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a F hEF).hom =
      (Mod.extendUnit ((upperStar Ab.{u + 1} g).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))) P).hom ≫
          a.hom := by
  let φ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF))
  let ψ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))
  let χ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))
  have he : φ ≫ ψ = χ := by
    dsimp only [φ, ψ, χ]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      padicSubfieldRingObjMap_comp_toPadicAlgCl]
  rw [localAdjoint_eq_mixed]
  change (Mod.extendUnit φ P).hom ≫
    ((Mod.mixedScalarMap φ χ (𝟙 _) ψ ψ he (by simp) P).hom ≫ a.hom) = _
  rw [← Category.assoc, mixedScalarMap_unit φ ψ he P]

end LocalUnits

section PulledScalarHom
open MonoidalCategory
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C]
  [HasCoequalizers C] [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] [G.LaxMonoidal]
  (adj : F ⊣ G) [adj.IsMonoidal]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
  (φ : R ⟶ S) [IsMonHom φ]

private noncomputable def pulledScalarRightIso :
    Mod.comap (F.map φ) ⋙
        (G.mapMod (F.obj R) ⋙
          Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙
          Mod.comap (adj.unitAlgHom S)) ⋙
        Mod.comap φ :=
  (Mod.comapMapModComapIso G
    (F.map φ) φ
    (adj.unitAlgHom R)
    (adj.unitAlgHom S)
    (adj.unit.naturality φ)).symm

private noncomputable def pulledScalarHomEquiv
    (P : Mod C R)
    (V : Mod D
      (F.obj S)) :
    (((F.mapMod S).obj ((Mod.extendScalars φ).obj P)) ⟶ V) ≃
      ((F.mapMod R).obj P ⟶
        (Mod.comap (F.map φ)).obj V) :=
  ((adj.mapModAdjunction S).homEquiv _ _).trans
    (((Mod.extendRestrictAdjunction φ).homEquiv _ _).trans
      ((Iso.homCongr (Iso.refl _) ((pulledScalarRightIso adj φ).app V).symm).trans
        ((adj.mapModAdjunction R).homEquiv _ _).symm))

omit [BraidedCategory C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] [IsCommMonObj R] in
private lemma mapMod_adj_hom
    (P : Mod C R) (V : Mod D (F.obj R)) (s : (F.mapMod R).obj P ⟶ V) :
    ((adj.mapModAdjunction R).homEquiv P V s).hom = adj.homEquiv _ _ s.hom := by
  simp only [Adjunction.mapModAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

omit [BraidedCategory C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] [IsCommMonObj R] in
private lemma mapMod_adj_symm_hom
    (P : Mod C R) (V : Mod D (F.obj R))
    (s : P ⟶ (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)).obj V) :
    (((adj.mapModAdjunction R).homEquiv P V).symm s).hom =
      (adj.homEquiv _ _).symm s.hom := by
  simp only [Adjunction.mapModAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private lemma pulledScalarHomEquiv_hom
    (P : Mod C R)
    (V : Mod D
      (F.obj S))
    (s : ((F.mapMod S).obj ((Mod.extendScalars φ).obj P)) ⟶ V) :
    (pulledScalarHomEquiv adj φ P V s).hom =
      F.map (Mod.extendUnit φ P).hom ≫ s.hom := by
  apply (adj.homEquiv _ _).injective
  dsimp only [pulledScalarHomEquiv, Equiv.trans_apply]
  erw [mapMod_adj_symm_hom, Equiv.apply_symm_apply]
  have he : ((pulledScalarRightIso adj φ).inv.app V).hom = 𝟙 _ :=
    Mod.comapMapModComapIso_hom_app_hom _ _ _ _ _ _ V
  dsimp only [Iso.homCongr]
  change 𝟙 _ ≫ (((Mod.extendRestrictAdjunction φ).homEquiv _ _
    ((adj.mapModAdjunction S).homEquiv _ _ s)).hom) ≫
      ((pulledScalarRightIso adj φ).inv.app V).hom = _
  rw [Adjunction.homEquiv_unit]
  simp only [Mod.comp_hom', Mod.comap_map_hom]
  rw [scalar_unit, mapMod_adj_hom]
  rw [he]
  erw [Category.comp_id, Category.id_comp]
  exact (adj.homEquiv_naturality_left
    (Mod.extendUnit φ P).hom s.hom).symm

include adj in
private lemma pulledScalar_lift (P : Mod C R) (V : Mod D (F.obj S))
    (b : (F.mapMod R).obj P ⟶ (Mod.comap (F.map φ)).obj V) :
    ∃ s : (F.mapMod S).obj ((Mod.extendScalars φ).obj P) ⟶ V,
      F.map (Mod.extendUnit φ P).hom ≫ s.hom = b.hom := by
  refine ⟨(pulledScalarHomEquiv adj φ P V).symm b, ?_⟩
  have h := congrArg Mod.Hom.hom ((pulledScalarHomEquiv adj φ P V).apply_symm_apply b)
  rw [pulledScalarHomEquiv_hom] at h
  exact h

include adj in
private lemma pulledScalar_hom_ext (P : Mod C R) (V : Mod D (F.obj S))
    (s t : (F.mapMod S).obj ((Mod.extendScalars φ).obj P) ⟶ V)
    (h : F.map (Mod.extendUnit φ P).hom ≫ s.hom =
      F.map (Mod.extendUnit φ P).hom ≫ t.hom) : s = t := by
  apply (pulledScalarHomEquiv adj φ P V).injective
  apply Mod.hom_ext
  simpa only [pulledScalarHomEquiv_hom] using h

end PulledScalarHom

section ModuleSquare
open MonoidalCategory
variable {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory A]
  (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ E) (K : E ⥤ A)
  [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [K.LaxMonoidal]
  (τ : F ⋙ G ≅ H ⋙ K) [NatTrans.IsMonoidal τ.hom]
  (R : C) [MonObj R]

private def squareRing : G.obj (F.obj R) ⟶ K.obj (H.obj R) := τ.hom.app R

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory A] [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    [K.LaxMonoidal] [NatTrans.IsMonoidal τ.hom] [MonObj R] in
private lemma squareRing_eq : squareRing F G H K τ R = τ.hom.app R := rfl

private instance squareRingIso : IsIso (squareRing F G H K τ R) := by
  rw [squareRing_eq]
  infer_instance

private instance squareRingHom : IsMonHom (squareRing F G H K τ R) :=
  IsMonHom.of_eq (h₁ := (F ⋙ G).monObjObj R) (h₂ := (H ⋙ K).monObjObj R)
    (τ.hom.app R) (CategoryTheory.Functor.monObjObj_comp F G R)
      (CategoryTheory.Functor.monObjObj_comp H K R)

private noncomputable def squareModIso (M : Mod C R) :
    (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
      (Mod.comap (squareRing F G H K τ R)).obj
        ((K.mapMod (H.obj R)).obj ((H.mapMod R).obj M)) :=
  Mod.isoMk (τ.app M.X) (by
    change (CategoryTheory.Functor.LaxMonoidal.μ G (F.obj R) (F.obj M.X) ≫
        G.map (CategoryTheory.Functor.LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X])) ≫
          τ.hom.app M.X =
      G.obj (F.obj R) ◁ τ.hom.app M.X ≫ τ.hom.app R ▷ K.obj (H.obj M.X) ≫
        CategoryTheory.Functor.LaxMonoidal.μ K (H.obj R) (H.obj M.X) ≫
          K.map (CategoryTheory.Functor.LaxMonoidal.μ H R M.X ≫ H.map γ[R,M.X])
    have h₁ := τ.hom.naturality γ[R,M.X]
    have h₂ := NatTrans.IsMonoidal.tensor (τ := τ.hom) R M.X
    rw [CategoryTheory.Functor.LaxMonoidal.comp_μ,
      CategoryTheory.Functor.LaxMonoidal.comp_μ] at h₂
    simp only [G.map_comp, K.map_comp, Category.assoc]
    change _ ≫ _ ≫ ((F ⋙ G).map γ[R,M.X] ≫ τ.hom.app M.X) = _
    rw [h₁]
    simp only [Category.assoc] at h₂
    calc
      _ = (CategoryTheory.Functor.LaxMonoidal.μ G (F.obj R) (F.obj M.X) ≫
          G.map (CategoryTheory.Functor.LaxMonoidal.μ F R M.X) ≫
            τ.hom.app (R ⊗ M.X)) ≫ (H ⋙ K).map γ[R,M.X] := by
        simp only [Category.assoc]
        rfl
      _ = _ := by
        rw [h₂]
        simp only [tensorHom_def', Category.assoc]
        rfl)

private noncomputable def squareRestrictIso
    (S : C) [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod E (H.obj S)) :
    (Mod.comap (squareRing F G H K τ R)).obj
      ((K.mapMod (H.obj R)).obj ((Mod.comap (H.map φ)).obj M)) ≅
    (Mod.comap (G.map (F.map φ))).obj
      ((Mod.comap (squareRing F G H K τ S)).obj
        ((K.mapMod (H.obj S)).obj M)) :=
  (Mod.comap (squareRing F G H K τ R)).mapIso
      ((K.mapModComapIso (H.map φ)).app M) ≪≫
    ((Mod.comapComp (squareRing F G H K τ R) (K.map (H.map φ))).app
      ((K.mapMod (H.obj S)).obj M)).symm ≪≫
    (Mod.comapCongr (show
      squareRing F G H K τ R ≫ K.map (H.map φ) =
        G.map (F.map φ) ≫ squareRing F G H K τ S from
          (τ.hom.naturality φ).symm)).app
      ((K.mapMod (H.obj S)).obj M) ≪≫
    (Mod.comapComp (G.map (F.map φ)) (squareRing F G H K τ S)).app
      ((K.mapMod (H.obj S)).obj M)

private lemma squareRestrictIso_hom
    (S : C) [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod E (H.obj S)) :
    (squareRestrictIso F G H K τ R S φ M).hom.hom = 𝟙 _ := by
  change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) = 𝟙 _
  simp only [Category.comp_id]

end ModuleSquare

section FactorSquare
open MonoidalCategory
variable {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory A]
  [BraidedCategory D] [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : D, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ E) (K : E ⥤ A)
  [F.LaxMonoidal] [G.Monoidal] [H.LaxMonoidal] [K.LaxMonoidal]
  {J : A ⥤ D} [J.LaxMonoidal] (adj : G ⊣ J) [adj.IsMonoidal]
  (τ : F ⋙ G ≅ H ⋙ K) [NatTrans.IsMonoidal τ.hom]
  (R S : C) [MonObj R] [MonObj S] [IsCommMonObj (F.obj R)]
  (φ : R ⟶ S) [IsMonHom φ]

include adj in
private theorem factorSquare
    (P : Mod D (F.obj R)) (Q : Mod E (H.obj S)) (M : Mod C S)
    (a : (Mod.extendScalars (F.map φ)).obj P ⟶ (F.mapMod S).obj M)
    (c : Q ⟶ (H.mapMod S).obj M)
    (rE : G.obj (F.obj R) ⟶ K.obj (H.obj R)) [IsMonHom rE]
    (hrE : rE = τ.hom.app R)
    (b : (G.mapMod (F.obj R)).obj P ⟶
      (Mod.comap rE).obj
        ((K.mapMod (H.obj R)).obj ((Mod.comap (H.map φ)).obj Q)))
    (hb : b.hom ≫ K.map c.hom =
      G.map ((Mod.extendUnit (F.map φ) P).hom ≫ a.hom) ≫ τ.hom.app M.X) :
    ∃ s : G.obj ((Mod.extendScalars (F.map φ)).obj P).X ⟶ K.obj Q.X,
      s ≫ K.map c.hom = G.map a.hom ≫ τ.hom.app M.X := by
  subst rE
  let χ := squareRing F G H K τ S
  let Z := (Mod.comap χ).obj ((K.mapMod (H.obj S)).obj Q)
  let ee := squareRestrictIso F G H K τ R S φ Q
  obtain ⟨ss, hs⟩ := pulledScalar_lift adj (F.map φ) P Z (b ≫ ee.hom)
  have hee : (b ≫ ee.hom).hom = b.hom := by
    simp only [Mod.comp_hom', ee, squareRestrictIso_hom]
    exact Category.comp_id _
  replace hs := hs.trans hee
  let v := (Mod.comap χ).map ((K.mapMod (H.obj S)).map c)
  let r := (G.mapMod (F.obj S)).map a ≫ (squareModIso F G H K τ S M).hom
  have he : ss ≫ v = r := by
    apply pulledScalar_hom_ext adj (F.map φ) P _
    change G.map (Mod.extendUnit (F.map φ) P).hom ≫ (ss.hom ≫ K.map c.hom) =
      G.map (Mod.extendUnit (F.map φ) P).hom ≫ (G.map a.hom ≫ τ.hom.app M.X)
    have hm := G.map_comp (Mod.extendUnit (F.map φ) P).hom a.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ K.map c.hom) hs).trans
        (hb.trans ((congrArg (· ≫ τ.hom.app M.X) hm).trans (Category.assoc _ _ _))))
  exact ⟨ss.hom, congrArg Mod.Hom.hom he⟩

end FactorSquare

private instance overlapComparisonMonoidal
    {W Y Z X : Scheme.{u}} {p : W ⟶ Y} {g : Y ⟶ X}
    {q : W ⟶ Z} {h : Z ⟶ X} (w : p ≫ g = q ≫ h) :
    NatTrans.IsMonoidal (overlapComparison w).hom := by
  have hc (a b : W ⟶ X) (e : a = b) :
      NatTrans.IsMonoidal (upperStarCongr Ab.{u + 1} e).hom := by
    subst b
    exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
  have := hc (p ≫ g) (q ≫ h) w
  rw [overlapComparison_eq_original, upperStarCompIso]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

attribute [local irreducible] finiteCoefficientLocalAdjoint finiteCoefficientLocalTensorMap
  Mod.extendScalarsComp Mod.extendScalarsIsoOfEq Mod.extendRestrictAdjunction

attribute [local irreducible] squareRing overlapComparison componentComparison

set_option backward.isDefEq.respectTransparency true in
/-- Transpose an already given E-linear factor at a fixed field F on one overlap.

Source: archived `TwoColimit.lean`, (Obj) overlap descent, adjunction calculation.
(auxiliary; not a blueprint node).

Proof: let S be the restriction of q*L_Q along the monoidal ring comparison at F.
Naturality of that comparison in E -> F identifies the target of b with the restriction
of S along p*g*(E -> F). Pullback commutes with extension of scalars: compose the two
module adjunctions and use naturality of the unit of p* adjoint p_* to identify their
right adjoints. Transpose b through this resulting Hom equivalence, obtaining an
F-linear map from p*L_P to S. Its underlying map is s. Under the same Hom equivalence,
s followed by q*q_Q transposes to b followed by q*q_Q. The hypothesis hb identifies
this with p* of the original E-to-Omega adjoint of a followed by the overlap comparison.
The transitivity comparison for scalar extension sends the composite of the E-to-F
and F-to-Omega units to the E-to-Omega unit. Consequently this is also the transpose
of p*q_P followed by the overlap comparison. Both composites are F-linear, by
monoidality and naturality of the comparison, so injectivity of the Hom equivalence
gives their equality. This uses no finite presentation, compactness, filteredness,
invertibility of a or c, or invertibility of the scalar adjoints; it also works for
zero modules and the empty overlap.
-/
theorem finiteCoefficient_overlap_factor_transpose
    (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U V W : Scheme.{u}) (g : U ⟶ X) (h : V ⟶ X)
    (p : W ⟶ U) (q : W ⟶ V) (w : p ≫ g = q ≫ h)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (Q : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((upperStar Ab.{u + 1} h).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ⟶
        ((upperStar Ab.{u + 1} g).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
    (c : (Mod.extendScalars ((upperStar Ab.{u + 1} h).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj Q ⟶
        ((upperStar Ab.{u + 1} h).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
    (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
    (rE : (upperStar Ab.{u + 1} p).obj ((upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) ⟶
      (upperStar Ab.{u + 1} q).obj ((upperStar Ab.{u + 1} h).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    [IsMonHom rE]
    (hrE : rE = (overlapComparison w).hom.app
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))
    (b : ((upperStar Ab.{u + 1} p).mapMod
      ((upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).obj P ⟶
      (Mod.comap rE).obj (((upperStar Ab.{u + 1} q).mapMod
        ((upperStar Ab.{u + 1} h).obj
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).obj
        ((Mod.comap ((upperStar Ab.{u + 1} h).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj
          (finiteCoefficientLocalModel T X f ℓ E V h Q F hEF))))
    (hb : b.hom ≫ (upperStar Ab.{u + 1} q).map
        (finiteCoefficientLocalAdjoint T X f ℓ E V h Q M c F hEF).hom =
      (upperStar Ab.{u + 1} p).map
        ((Mod.extendUnit ((upperStar Ab.{u + 1} g).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))) P).hom ≫
            a.hom) ≫ (overlapComparison w).hom.app M.X) :
    ∃ s : (upperStar Ab.{u + 1} p).obj
        (finiteCoefficientLocalModel T X f ℓ E U g P F hEF).X ⟶
      (upperStar Ab.{u + 1} q).obj
        (finiteCoefficientLocalModel T X f ℓ E V h Q F hEF).X,
      s ≫ (upperStar Ab.{u + 1} q).map
        (finiteCoefficientLocalAdjoint T X f ℓ E V h Q M c F hEF).hom =
      (upperStar Ab.{u + 1} p).map
        (finiteCoefficientLocalAdjoint T X f ℓ E U g P M a F hEF).hom ≫
          (overlapComparison w).hom.app M.X := by
  let R := (upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)
  let S := (upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)
  let φ := (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)
  let Bf := (Mod.comap ((upperStar Ab.{u + 1} f).map
    (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M
  set_option backward.isDefEq.respectTransparency false in
    have hf := factorSquare (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} p)
      (upperStar Ab.{u + 1} h) (upperStar Ab.{u + 1} q)
      (upperStarLowerStarAdjunction Ab.{u + 1} p)
      (overlapComparison w) R S φ P
      (finiteCoefficientLocalModel T X f ℓ E V h Q F hEF) Bf
      (finiteCoefficientLocalAdjoint T X f ℓ E U g P M a F hEF)
      (finiteCoefficientLocalAdjoint T X f ℓ E V h Q M c F hEF) rE
    apply hf hrE b
    exact hb.trans (congrArg
      (fun z ↦ (upperStar Ab.{u + 1} p).map z ≫
        (overlapComparison w).hom.app M.X)
      (localAdjoint_unit T X f ℓ E U g P M a F hEF).symm)

end AlgebraicGeometry.ProEtale
