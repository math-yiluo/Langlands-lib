/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarOpenTensorTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # The two pullback units under first-factor open base change

Source: Stacks Project, Tags 0096, 0097 and 0BED.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The open base change in the first factor, constructed by the pullback map.
Source: Stacks Project, Tag 0BED.
(blueprint: lem-sc-external-open-factor-units-left). -/
def externalOpenBaseChangeLeft (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (V : X.Opens) :
    Limits.pullback (V.ι ≫ f) g ⟶ Limits.pullback f g :=
  pullback.map (V.ι ≫ f) g f g V.ι (𝟙 Y) (𝟙 _) (by simp) (by simp)

/-- The cartesian open base change is an open immersion.
Source: Stacks Project, Tag 0BED.
(blueprint: lem-sc-external-open-factor-units-left). -/
instance externalOpenBaseChangeLeft_isOpenImmersion
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)) (V : X.Opens) :
    IsOpenImmersion (externalOpenBaseChangeLeft f g V) := by
  unfold externalOpenBaseChangeLeft
  infer_instance

private theorem scalarMapAlong {A B : Scheme.{w}}
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (a : B ⟶ A) (h : a ≫ fA = fB) (U : A.Opens) (r : k) :
    (a.app U).hom (scalarMap fA U r) = scalarMap fB (a ⁻¹ᵁ U) r := by
  have hn := a.naturality (homOfLE (le_top (a := U))).op
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ht
  simp only [scalarMap, RingHom.comp_apply]
  change (A.presheaf.map (homOfLE (le_top (a := U))).op ≫ a.app U)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fA.appTop) r) = _
  rw [hn]
  change (a.appTop ≫ B.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op)
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fA.appTop) r) = _
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fA.appTop ≫ a.appTop ≫
    B.presheaf.map (homOfLE (le_top (a := a ⁻¹ᵁ U))).op) r = _
  rw [← Category.assoc fA.appTop, ht]
  rfl

private def sectionUnitLinear {A B : Scheme.{w}}
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (a : B ⟶ A) (h : a ≫ fA = fB) (L : A.Modules ⥤ B.Modules)
    (adj : L ⊣ pushforward a) (M : A.Modules) (U : A.Opens)
    (hTop : ⊤ ≤ a ⁻¹ᵁ U) : scalarObj fA M (op U) →ₗ[k] scalarObj fB (L.obj M) (op ⊤) where
  toFun s := (L.obj M).val.map (homOfLE hTop).op ((adj.unit.app M).val.app (op U) s)
  map_add' s t := by simp only [map_add]
  map_smul' r s := by
    change (L.obj M).presheaf.map (homOfLE hTop).op
      ((adj.unit.app M).app U ((scalarMap fA U r) • (show Γ(M, U) from s))) = _
    rw [Hom.app_smul]
    change (L.obj M).val.map (homOfLE hTop).op
      ((a.app U).hom (scalarMap fA U r) •
        (show (L.obj M).val.obj (op (a ⁻¹ᵁ U)) from (adj.unit.app M).app U s)) = _
    rw [scalarMapAlong fA fB a h]
    exact scalarRestriction_linear fB (L.obj M) (homOfLE hTop).op r _

private theorem sectionUnitLinear_bijective {A B : Scheme.{w}}
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (a : B ⟶ A) [IsOpenImmersion a] (h : a ≫ fA = fB) (L : A.Modules ⥤ B.Modules)
    (adj : L ⊣ pushforward a) (M : A.Modules) (U : A.Opens)
    (hTop : ⊤ ≤ a ⁻¹ᵁ U) (hRange : U ≤ a.opensRange) :
    Function.Bijective (sectionUnitLinear fA fB a h L adj M U hTop) := by
  have hu := (pullbackPushforwardAdjunction a).unit_leftAdjointUniq_hom_app adj M
  have hu' := congrArg (fun φ ↦ φ.app U) hu
  have hbij : Function.Bijective ((adj.unit.app M).app U) := by
    rw [← hu', Hom.comp_app]
    exact (ConcreteCategory.bijective_of_isIso
      (((pushforward a).map
        (((pullbackPushforwardAdjunction a).leftAdjointUniq adj).hom.app M)).app U)).comp
      (bijective_pullbackUnit_app_of_isOpenImmersion a M hRange)
  have : IsIso (homOfLE hTop) :=
    ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact (ConcreteCategory.bijective_of_isIso
    ((L.obj M).presheaf.map (homOfLE hTop).op)).comp hbij

-- The two mate computations and their sectionwise transports elaborate large module functors.
/-- The factor comparisons carry the two unit sections to the local unit sections.
This statement contains no tensor product of coefficients or sections.
Source: Stacks Project, Tags 0096 and 0097; Tag 0BED, degree-zero restriction.
(blueprint: lem-sc-external-open-factor-units-left).

Proof: The pullback map b is the base change of the open immersion V into X.
Its image is p inverse-image V and the inverse image of this open is the
whole source. The restriction section isomorphism gives eF, with k-linearity
from the structure morphism V into X into Spec k. For the first factor,
compare b-star p-star with pV-star V-star by composition of adjunctions,
then compare V-star F with F restricted to V by uniqueness of left adjoints
to pushforward. For the second factor compare b-star q-star with qV-star
using b followed by q equals qV. These construct eM and eN. The unit equation
for each comparison identifies the composite units with the unit of the
composite morphism. For the first factor the open restriction unit is eF;
for the second factor the initial section is unchanged. Naturality of the
units commutes with the restrictions to the top open, giving the two
asserted formulas. This uses no nonemptiness or coherence hypotheses. -/
theorem exists_externalOpenFactorUnitsLeft
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : X.Opens) :
    ∃ hTop : ⊤ ≤ externalOpenBaseChangeLeft f g V ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ V),
    ∃ _hRange : pullback.fst f g ⁻¹ᵁ V ≤ (externalOpenBaseChangeLeft f g V).opensRange,
    ∃ eF : scalarObj f F (op V) ≅ scalarObj (V.ι ≫ f) (F.restrict V.ι) (op ⊤),
    ∃ eM : (tensorPullback (externalOpenBaseChangeLeft f g V)).obj
        ((tensorPullback (pullback.fst f g)).obj F) ≅
        (tensorPullback (pullback.fst (V.ι ≫ f) g)).obj (F.restrict V.ι),
    ∃ eN : (tensorPullback (externalOpenBaseChangeLeft f g V)).obj
        ((tensorPullback (pullback.snd f g)).obj G) ≅
        (tensorPullback (pullback.snd (V.ι ≫ f) g)).obj G,
      (∀ s : scalarObj f F (op V),
        eM.hom.app ⊤ (tensorPullbackOpenSection (externalOpenBaseChangeLeft f g V)
          ((tensorPullback (pullback.fst f g)).obj F) (pullback.fst f g ⁻¹ᵁ V) hTop
          (((Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app
            F).val.app (op V) s)) =
          tensorPullbackTopSection (pullback.fst (V.ι ≫ f) g) (F.restrict V.ι) (eF.hom s)) ∧
      (∀ t : scalarObj g G (op ⊤),
        eN.hom.app ⊤ (tensorPullbackOpenSection (externalOpenBaseChangeLeft f g V)
          ((tensorPullback (pullback.snd f g)).obj G) (pullback.fst f g ⁻¹ᵁ V) hTop
          (((tensorPullback (pullback.snd f g)).obj G).val.map
            (homOfLE (by simp : pullback.fst f g ⁻¹ᵁ V ≤ pullback.snd f g ⁻¹ᵁ ⊤)).op
            (((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
              G).val.app (op ⊤) t))) =
          tensorPullbackTopSection (pullback.snd (V.ι ≫ f) g) G t)  := by
  let b := externalOpenBaseChangeLeft f g V
  let p := pullback.fst f g
  let q := pullback.snd f g
  let pV := pullback.fst (V.ι ≫ f) g
  let qV := pullback.snd (V.ι ≫ f) g
  have hf : b ≫ p = pV ≫ V.ι := by simp [b, p, pV, externalOpenBaseChangeLeft]
  have hq : b ≫ q = qV := by simp [b, q, qV, externalOpenBaseChangeLeft]
  have hTop : ⊤ ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hf, Scheme.Hom.comp_preimage]
    simp
  have hRange : p ⁻¹ᵁ V ≤ b.opensRange := by
    have hr := (isPullback_pullback_map_left V.ι f g).flip.opensRange_fst
    simpa [b, p, externalOpenBaseChangeLeft] using hr.ge
  have hιTop : ⊤ ≤ V.ι ⁻¹ᵁ V := by simp
  have hιRange : V ≤ V.ι.opensRange := by simp
  let u := ModuleCat.ofHom (sectionUnitLinear f (V.ι ≫ f) V.ι rfl
    (restrictFunctor V.ι) (restrictAdjunction V.ι) F V hιTop)
  let : IsIso u := (ConcreteCategory.isIso_iff_bijective u).mpr
    (sectionUnitLinear_bijective f (V.ι ≫ f) V.ι rfl
      (restrictFunctor V.ι) (restrictAdjunction V.ι) F V hιTop hιRange)
  let eF := asIso u
  let adjM1 := (Classical.choose (exists_tensorPullbackAdjunction p)).comp
    (Classical.choose (exists_tensorPullbackAdjunction b))
  let adjM2 := (restrictAdjunction V.ι).comp
    (Classical.choose (exists_tensorPullbackAdjunction pV))
  let rightM := pushforwardComp pV V.ι ≪≫ pushforwardCongr hf.symm ≪≫
    (pushforwardComp b p).symm
  let eM := ((conjugateIsoEquiv adjM2 adjM1).symm rightM).app F
  let adjN1 := (Classical.choose (exists_tensorPullbackAdjunction q)).comp
    (Classical.choose (exists_tensorPullbackAdjunction b))
  let adjN2 := Classical.choose (exists_tensorPullbackAdjunction qV)
  let rightN := pushforwardCongr hq.symm ≪≫ (pushforwardComp b q).symm
  let eN := ((conjugateIsoEquiv adjN2 adjN1).symm rightN).app G
  refine ⟨hTop, hRange, eF, eM, eN, ?_, ?_⟩
  · intro s
    change (Γ(F, V) : Type w) at s
    have hu := unit_conjugateEquiv_symm adjM2 adjM1 rightM.hom F
    have hs := congrArg (fun φ ↦ φ.app V s) hu
    simp only [adjM1, adjM2, rightM, Adjunction.comp_unit_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Hom.comp_app, pushforward_map_app,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply,
      Functor.comp_map] at hs
    let H := (tensorPullback pV).obj (F.restrict V.ι)
    have hs' : H.presheaf.map _
        (((Classical.choose (exists_tensorPullbackAdjunction pV)).unit.app
          (F.restrict V.ι)).app (V.ι ⁻¹ᵁ V)
          (((restrictAdjunction V.ι).unit.app F).app V s)) =
      eM.hom.app (b ⁻¹ᵁ (p ⁻¹ᵁ V))
        (((Classical.choose (exists_tensorPullbackAdjunction b)).unit.app
          ((tensorPullback p).obj F)).app (p ⁻¹ᵁ V)
          (((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F).app V s)) := hs
    change eM.hom.app ⊤
      (((tensorPullback b).obj ((tensorPullback p).obj F)).presheaf.map
        (homOfLE hTop).op
        (((Classical.choose (exists_tensorPullbackAdjunction b)).unit.app
          ((tensorPullback p).obj F)).app (p ⁻¹ᵁ V)
          (((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F).app V s))) = _
    have hn := Hom.app_presheaf_map eM.hom (homOfLE hTop)
      (((Classical.choose (exists_tensorPullbackAdjunction b)).unit.app
        ((tensorPullback p).obj F)).app (p ⁻¹ᵁ V)
        (((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F).app V s))
    refine hn.trans ?_
    refine (congrArg (H.presheaf.map (homOfLE hTop).op) hs'.symm).trans ?_
    change H.presheaf.map _ (H.presheaf.map _ _) =
      H.presheaf.map _
        (((Classical.choose (exists_tensorPullbackAdjunction pV)).unit.app
          (F.restrict V.ι)).app ⊤
          ((F.restrict V.ι).presheaf.map (homOfLE hιTop).op
            (((restrictAdjunction V.ι).unit.app F).app V s)))
    have hnR := Hom.app_presheaf_map
      ((Classical.choose (exists_tensorPullbackAdjunction pV)).unit.app (F.restrict V.ι))
      (homOfLE hιTop) (((restrictAdjunction V.ι).unit.app F).app V s)
    have hOp : b ⁻¹ᵁ (p ⁻¹ᵁ V) = pV ⁻¹ᵁ (V.ι ⁻¹ᵁ V) :=
      congrArg (fun a ↦ a ⁻¹ᵁ V) hf
    have hPV : ⊤ ≤ pV ⁻¹ᵁ ⊤ := by simp
    have hR := congrArg (H.presheaf.map (homOfLE hPV).op) hnR
    refine Eq.trans ?_ hR.symm
    change (H.presheaf.map (eqToHom hOp).op ≫
      H.presheaf.map (homOfLE hTop).op) _ =
      (H.presheaf.map ((TopologicalSpace.Opens.map pV.base).map (homOfLE hιTop)).op ≫
        H.presheaf.map (homOfLE hPV).op) _
    have hcomp : H.presheaf.map (eqToHom hOp).op ≫
        H.presheaf.map (homOfLE hTop).op =
        H.presheaf.map ((TopologicalSpace.Opens.map pV.base).map (homOfLE hιTop)).op ≫
          H.presheaf.map (homOfLE hPV).op := by
      calc
        _ = H.presheaf.map ((eqToHom hOp).op ≫ (homOfLE hTop).op) :=
          (H.presheaf.map_comp _ _).symm
        _ = H.presheaf.map
            (((TopologicalSpace.Opens.map pV.base).map (homOfLE hιTop)).op ≫
              (homOfLE hPV).op) := congrArg H.presheaf.map (Subsingleton.elim _ _)
        _ = _ := H.presheaf.map_comp _ _
    exact ConcreteCategory.congr_hom hcomp _
  · intro t
    change (Γ(G, ⊤) : Type w) at t
    have hu := unit_conjugateEquiv_symm adjN2 adjN1 rightN.hom G
    have hs := congrArg (fun φ ↦ φ.app ⊤ t) hu
    simp only [adjN1, adjN2, rightN, Adjunction.comp_unit_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Hom.comp_app, pushforward_map_app,
      pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
      ConcreteCategory.comp_apply, Functor.comp_map] at hs
    let Q := (tensorPullback q).obj G
    let BQ := (tensorPullback b).obj Q
    let QV := (tensorPullback qV).obj G
    let ηb := (Classical.choose (exists_tensorPullbackAdjunction b)).unit.app Q
    let ηq := (Classical.choose (exists_tensorPullbackAdjunction q)).unit.app G
    have hIncl : p ⁻¹ᵁ V ≤ q ⁻¹ᵁ ⊤ := by simp
    have hn := Hom.app_presheaf_map ηb (homOfLE hIncl) (ηq.app ⊤ t)
    change eN.hom.app ⊤ (BQ.presheaf.map (homOfLE hTop).op
      (ηb.app (p ⁻¹ᵁ V) (Q.presheaf.map (homOfLE hIncl).op (ηq.app ⊤ t)))) = _
    refine (congrArg (fun z ↦ eN.hom.app ⊤
      (BQ.presheaf.map (homOfLE hTop).op z)) hn).trans ?_
    have hBQ : ⊤ ≤ b ⁻¹ᵁ (q ⁻¹ᵁ ⊤) := by simp
    change eN.hom.app ⊤
      ((BQ.presheaf.map ((TopologicalSpace.Opens.map b.base).map (homOfLE hIncl)).op ≫
        BQ.presheaf.map (homOfLE hTop).op) _) = _
    have hcomp : BQ.presheaf.map
        ((TopologicalSpace.Opens.map b.base).map (homOfLE hIncl)).op ≫
        BQ.presheaf.map (homOfLE hTop).op = BQ.presheaf.map (homOfLE hBQ).op :=
      (BQ.presheaf.map_comp _ _).symm.trans
        (congrArg BQ.presheaf.map (Subsingleton.elim _ _))
    refine (congrArg (eN.hom.app ⊤) (ConcreteCategory.congr_hom hcomp _)).trans ?_
    have hnE := Hom.app_presheaf_map eN.hom (homOfLE hBQ)
      (ηb.app (q ⁻¹ᵁ ⊤) (ηq.app ⊤ t))
    refine hnE.trans ?_
    have hs' : QV.presheaf.map _
        (((Classical.choose (exists_tensorPullbackAdjunction qV)).unit.app G).app ⊤ t) =
      eN.hom.app (b ⁻¹ᵁ (q ⁻¹ᵁ ⊤)) (ηb.app (q ⁻¹ᵁ ⊤) (ηq.app ⊤ t)) := hs
    refine (congrArg (QV.presheaf.map (homOfLE hBQ).op) hs'.symm).trans ?_
    have hOp : b ⁻¹ᵁ (q ⁻¹ᵁ ⊤) = qV ⁻¹ᵁ ⊤ := by
      rw [← Scheme.Hom.comp_preimage, hq]
    have hQV : ⊤ ≤ qV ⁻¹ᵁ ⊤ := by simp
    change (QV.presheaf.map (eqToHom hOp).op ≫
      QV.presheaf.map (homOfLE hBQ).op) _ = QV.presheaf.map (homOfLE hQV).op _
    have hcomp : QV.presheaf.map (eqToHom hOp).op ≫
        QV.presheaf.map (homOfLE hBQ).op = QV.presheaf.map (homOfLE hQV).op :=
      (QV.presheaf.map_comp _ _).symm.trans
        (congrArg QV.presheaf.map (Subsingleton.elim _ _))
    exact ConcreteCategory.congr_hom hcomp _

end
end AlgebraicGeometry.Scheme.Modules
