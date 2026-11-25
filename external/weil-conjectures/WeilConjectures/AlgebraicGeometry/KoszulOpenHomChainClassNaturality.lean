/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives


/-! # Naturality of the explicit Koszul stage class

Source: Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
(blueprint: lem-sc-koszul-open-hom-chain-class-naturality).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def homPostcomp {A : Type u} [CommRing A]
    (K M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N) :
    CochainComplex.moduleHomComplex K M ⟶ CochainComplex.moduleHomComplex K N where
  f n := ModuleCat.ofHom
    { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero n)
      map_add' := fun z z' ↦ CochainComplex.HomComplex.Cochain.add_comp z z' _ _
      map_smul' := fun a z ↦ CochainComplex.HomComplex.Cochain.smul_comp a z _ _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact CochainComplex.HomComplex.δ_comp_ofHom z g m

set_option backward.isDefEq.respectTransparency false in
private theorem homChainClass_postcomp {A : Type u} [CommRing A]
    (K M N : CochainComplex (ModuleCat.{u} A) ℤ) (s : K ⟶ M) (g : M ⟶ N) :
    HomologicalComplex.homologyMap (homPostcomp K M N g) 0 (koszulHomChainClass s) =
      koszulHomChainClass (s ≫ g) := by
  let S := (CochainComplex.moduleHomComplex K M).sc 0
  let T := (CochainComplex.moduleHomComplex K N).sc 0
  let z : S.moduleCatLeftHomologyData.K :=
    ⟨CochainComplex.HomComplex.Cochain.ofHom s,
      CochainComplex.HomComplex.δ_ofHom s⟩
  let z' : T.moduleCatLeftHomologyData.K :=
    ⟨CochainComplex.HomComplex.Cochain.ofHom (s ≫ g),
      CochainComplex.HomComplex.δ_ofHom (s ≫ g)⟩
  have hz : HomologicalComplex.cyclesMap (homPostcomp K M N g) 0
      (S.moduleCatCyclesIso.inv z) = T.moduleCatCyclesIso.inv z' := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun h ↦ h (S.moduleCatCyclesIso.inv z))
      (HomologicalComplex.cyclesMap_i (homPostcomp K M N g) 0)
    simp only [ModuleCat.comp_apply] at h
    refine h.trans ?_
    have hi := congrArg (fun h ↦ h z) S.moduleCatCyclesIso_inv_iCycles
    have hi' := congrArg (fun h ↦ h z') T.moduleCatCyclesIso_inv_iCycles
    simp only [ModuleCat.comp_apply] at hi hi'
    change (homPostcomp K M N g).f 0 (S.iCycles (S.moduleCatCyclesIso.inv z)) =
      T.iCycles (T.moduleCatCyclesIso.inv z')
    rw [hi, hi']
    change (CochainComplex.HomComplex.Cochain.ofHom s).comp
      (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero 0) =
        CochainComplex.HomComplex.Cochain.ofHom (s ≫ g)
    exact (CochainComplex.HomComplex.Cochain.ofHom_comp s g).symm
  have h := congrArg (fun h ↦ h (S.moduleCatCyclesIso.inv z))
    (HomologicalComplex.homologyπ_naturality (homPostcomp K M N g) 0)
  simp only [ModuleCat.comp_apply] at h
  change HomologicalComplex.homologyMap (homPostcomp K M N g) 0
    (S.homologyπ (S.moduleCatCyclesIso.inv z)) = T.homologyπ (T.moduleCatCyclesIso.inv z')
  exact h.trans (congrArg (fun x ↦ T.homologyπ x) hz)

set_option backward.isDefEq.respectTransparency false in
private theorem stageClass_postcomp
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (L F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (s : koszulOpenSheafComplex A r f e ⟶ L) (t : L ⟶ F) :
    let S := (affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)
    let K := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    H.map (DerivedCategory.Q.map
      ((koszulCechHomObjIso A r f (S.obj L) e).hom ≫
        homPostcomp K (S.obj L) (S.obj F) (S.map t) ≫
          (koszulCechHomObjIso A r f (S.obj F) e).inv))
      (koszulOpenHomStageClass A r f L e s) =
        koszulOpenHomStageClass A r f F e (s ≫ t) := by
  let S := (affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)
  let K := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let α := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
  let g := homPostcomp K (S.obj L) (S.obj F) (S.map t)
  have ht : koszulOpenHomTranspose A r f F e (s ≫ t) =
      koszulOpenHomTranspose A r f L e s ≫ S.map t := by
    let : (tilde.functor (.of A)).Additive :=
      ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
    let : (moduleSpecΓFunctor (R := .of A)).Additive :=
      ⟨fun {_ _} _ _ ↦ rfl⟩
    exact Adjunction.homEquiv_naturality_right
      ((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)) s t
  have hn := α.inv.naturality g
  change HomologicalComplex.homologyMap g 0 ≫
      (α.app (CochainComplex.moduleHomComplex K (S.obj F))).inv =
    (α.app (CochainComplex.moduleHomComplex K (S.obj L))).inv ≫
      H.map (DerivedCategory.Q.map g) at hn
  dsimp only
  simp only [koszulOpenHomStageClass, Functor.map_comp, ModuleCat.comp_apply]
  change H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj F) e).inv)
    (H.map (DerivedCategory.Q.map g)
      (H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj L) e).hom)
        (H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj L) e).inv)
          ((α.app _).inv (koszulHomChainClass (koszulOpenHomTranspose A r f L e s)))))) = _
  have hi (x) :
      H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj L) e).hom)
        (H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj L) e).inv) x) = x := by
    rw [← ModuleCat.comp_apply, ← H.map_comp, ← DerivedCategory.Q.map_comp,
      Iso.inv_hom_id]
    rw [DerivedCategory.Q.map_id, H.map_id]
    rfl
  rw [hi]
  have hn' := congrArg (fun h ↦ h
    (koszulHomChainClass (koszulOpenHomTranspose A r f L e s))) hn
  simp only [ModuleCat.comp_apply] at hn'
  apply congrArg (fun x ↦
    H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f (S.obj F) e).inv) x)
  refine hn'.symm.trans ?_
  apply congrArg (fun x ↦ (α.app (CochainComplex.moduleHomComplex K (S.obj F))).inv x)
  exact (homChainClass_postcomp K (S.obj L) (S.obj F)
    (koszulOpenHomTranspose A r f L e s) (S.map t)).trans (congrArg koszulHomChainClass ht.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem stageComparison_postcomp
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (L F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : L ⟶ F) :
    let S := (affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)
    let K := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
    (koszulCechHomObjIso A r f (S.obj L) e).inv ≫
      colimit.ι (koszulCechHomDiagram A r f (S.obj L)) e ≫
        koszulCechComparison A r f L ≫ (principalCechFunctor r f).map t =
    homPostcomp K (S.obj L) (S.obj F) (S.map t) ≫
      (koszulCechHomObjIso A r f (S.obj F) e).inv ≫
        colimit.ι (koszulCechHomDiagram A r f (S.obj F)) e ≫
          koszulCechComparison A r f F := by
  let S := (affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)
  let K := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
  let cL := koszulCechCocone A r f L
  let cF := koszulCechCocone A r f F
  let hL := (koszulCechCocone_exists A r f L).choose_spec.1
  let hF := (koszulCechCocone_exists A r f F).choose_spec.1
  dsimp only
  simp only [koszulCechComparison, Category.assoc, colimit.ι_desc_assoc]
  apply (cancel_mono (principalCechObjIso r f F).hom).mp
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext J
  let aL := (koszulCechHomObjIso A r f (S.obj L) e).inv ≫
    cL.ι.app e ≫ eqToHom hL ≫ (principalCechObjIso r f L).hom
  let aF := (koszulCechHomObjIso A r f (S.obj F) e).inv ≫
    cF.ι.app e ≫ eqToHom hF ≫ (principalCechObjIso r f F).hom
  have hmap (x : principalCechTerms r f L n) :
      (((principalCechObjIso r f L).inv ≫ (principalCechFunctor r f).map t ≫
        (principalCechObjIso r f F).hom).f n) x J =
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (t.f (n + 1 - (J.val.card : ℤ))) (x J) :=
    (principalCechFunctor_exists r f).choose_spec.2.2 L F t n x J
      ((principalCechFunctor_exists r f).choose_spec.2.1 L)
      ((principalCechFunctor_exists r f).choose_spec.2.1 F)
  have he : aL ≫ (principalCechObjIso r f L).inv ≫
      (principalCechFunctor r f).map t ≫ (principalCechObjIso r f F).hom =
      (koszulCechHomObjIso A r f (S.obj L) e).inv ≫
        cL.ι.app e ≫ eqToHom hL ≫ (principalCechFunctor r f).map t ≫
          (principalCechObjIso r f F).hom := by
    simp only [aL, Category.assoc, Iso.hom_inv_id_assoc]
  change (((koszulCechHomObjIso A r f (S.obj L) e).inv ≫
    cL.ι.app e ≫ eqToHom hL ≫ (principalCechFunctor r f).map t ≫
      (principalCechObjIso r f F).hom).f n) z J = _
  rw [← he]
  change (((principalCechObjIso r f L).inv ≫ (principalCechFunctor r f).map t ≫
    (principalCechObjIso r f F).hom).f n) (aL.f n z) J =
      aF.f n ((homPostcomp K (S.obj L) (S.obj F) (S.map t)).f n z) J
  rw [hmap]
  let N := (affineOpenSections A (principalCechIntersection r f J.val)).obj
    (F.X (n + 1 - (J.val.card : ℤ)))
  have hreg : IsSMulRegular (↑N) (∏ j ∈ J.val, f j) :=
    Scheme.Modules.isSMulRegular_of_le_basicOpen
      (M := F.X (n + 1 - (J.val.card : ℤ))) le_rfl
  apply hreg.pow (e + 1)
  dsimp only
  rw [← map_smul]
  have hl := (koszulCechCocone_exists A r f L).choose_spec.2 e n z J hL
  have hf := (koszulCechCocone_exists A r f F).choose_spec.2 e n
    ((homPostcomp K (S.obj L) (S.obj F) (S.map t)).f n z) J hF
  change (affineOpenSections A (principalCechIntersection r f J.val)).map
      (t.f (n + 1 - (J.val.card : ℤ)))
      ((∏ j ∈ J.val, f j) ^ (e + 1) • aL.f n z J) =
    (∏ j ∈ J.val, f j) ^ (e + 1) • aF.f n
      ((homPostcomp K (S.obj L) (S.obj F) (S.map t)).f n z) J
  erw [hl, hf]
  simp only [Units.smul_def, map_zsmul]
  apply congrArg (fun x ↦ ((Int.negOnePow
    ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
      ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) : ℤ) • x)
  have hn := (modulesSpecToSheaf.map (t.f (n + 1 - (J.val.card : ℤ)))).hom.naturality
    (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
  have hn' := ConcreteCategory.congr_hom hn
    ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
      (koszulCech_evaluation_degree r J.val n)) (koszulCechBasis A r f e J.val J.property))
  simp only [ModuleCat.comp_apply] at hn'
  change (affineOpenSections A (principalCechIntersection r f J.val)).map
      (t.f (n + 1 - (J.val.card : ℤ)))
      ((modulesSpecToSheaf.obj (L.X (n + 1 - (J.val.card : ℤ)))).obj.map
        (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
        ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
          (koszulCech_evaluation_degree r J.val n))
            (koszulCechBasis A r f e J.val J.property))) =
    (modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
      (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
      (((z.comp (CochainComplex.HomComplex.Cochain.ofHom (S.map t)) (add_zero n)).v
        (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
          (koszulCech_evaluation_degree r J.val n))
            (koszulCechBasis A r f e J.val J.property))
  simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, ModuleCat.comp_apply]
  exact hn'


set_option backward.isDefEq.respectTransparency false in
private theorem cechDerivedComparison_naturality
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (L F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (t : L ⟶ F) :
    principalCechDerivedComparison r f L ≫
      (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map
        (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map ((principalCechFunctor r f).map t) ≫
      principalCechDerivedComparison r f F := by
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := affineOpenSections A (koszulOpen A r f)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let T := S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let B := principalCechFunctor r f ⋙ DerivedCategory.Q
  let D := DerivedCategory.Q ⋙ S.rightDerivedFunctor
  let a : T ⟶ B := Functor.whiskerRight (principalCechAugmentation r f) DerivedCategory.Q
  let b : T ⟶ D :=
    (Functor.isoWhiskerLeft (S.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
      Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
        S.rightDerivedFunctorUnit ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
        S.rightDerivedFunctor).hom
  let ai := Functor.whiskerLeft I a
  let d := Functor.whiskerRight η D
  have hη (K : CochainComplex C ℤ) : QuasiIso (η.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
  have hai : IsIso ai := by
    have (K : CochainComplex C ℤ) : IsIso (ai.app K) := by
      change IsIso (DerivedCategory.Q.map ((principalCechAugmentation r f).app (I.obj K)))
      have := principalCechAugmentation_quasiIso r f (I.obj K)
      infer_instance
    exact NatIso.isIso_of_isIso_app ai
  have haI (K : CochainComplex C ℤ) : IsIso (a.app (I.obj K)) := by
    change IsIso (ai.app K)
    infer_instance
  have hd : IsIso d := by
    have (K : CochainComplex C ℤ) : IsIso (d.app K) := by
      have := hη K
      change IsIso (S.rightDerivedFunctor.map (DerivedCategory.Q.map (η.app K)))
      infer_instance
    exact NatIso.isIso_of_isIso_app d
  let β : B ⟶ D := Functor.whiskerRight η B ≫ inv ai ≫
    Functor.whiskerLeft I b ≫ inv d
  have hβ (K : CochainComplex C ℤ) :
      principalCechDerivedComparison r f K = β.app K := by
    have := hη K
    have := haI K
    apply (cancel_mono (d.app K ≫ (S.rightDerivedFunctorObjQIso (I.obj K)).hom ≫
      a.app (I.obj K))).mp
    have he := (principalCechDerivedComparison_exists r f K).choose_spec
      (I.obj K) (η.app K)
    change principalCechDerivedComparison r f K ≫
      d.app K ≫ (S.rightDerivedFunctorObjQIso (I.obj K)).hom ≫
        a.app (I.obj K) = B.map (η.app K) at he
    rw [he]
    have hb : b.app (I.obj K) = (S.rightDerivedFunctorObjQIso (I.obj K)).inv :=
      by
        simp [b, Functor.rightDerivedFunctorObjQIso]
        rfl
    simp only [β, NatTrans.comp_app, NatIso.isIso_inv_app]
    change B.map (η.app K) =
      (B.map (η.app K) ≫ inv (a.app (I.obj K)) ≫ b.app (I.obj K) ≫ inv (d.app K)) ≫
        d.app K ≫ (S.rightDerivedFunctorObjQIso (I.obj K)).hom ≫ a.app (I.obj K)
    rw [hb]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_assoc,
      IsIso.inv_hom_id, Category.comp_id]
  rw [hβ L, hβ F]
  exact (β.naturality t).symm

set_option backward.isDefEq.respectTransparency false in
/-- The explicit stage-to-derived-sections class commutes with postcomposition.
Source: Stacks Project, Tag 08D1, functoriality in the coefficient complex;
Tag 08DC, Equation 36.9.4.1, and Tag 08DD.
(blueprint: lem-sc-koszul-open-hom-chain-class-naturality).
Proof: The tilde/sections adjunction transpose of s followed by t is the transpose
of s postcomposed with the top-sections chain map of t. The Hom cycle of that
composite is postcomposition of the Hom cycle of s. Postcomposition commutes
with the signed Hom differential and hence with cycles, homology projections,
and homologyFunctorFactors. Transport through koszulCechHomObjIso gives the
same stage map. On each ordered wedge, t commutes with restriction to the
principal intersection and with division by the product of the f_j: the map
is A-linear and the localized denominator is invertible. It also commutes with
the integer totalization sign. Thus the explicit Cech cocones are natural.
The colimit injections commute with these stage maps by the colimit cocone law.
Finally the Cech-to-derived-sections comparison is natural (compute it after a
K-injective resolution and use its defining comparison equation). Apply Q and
H^0 and use preservation of composition to obtain the displayed equality.
No quasi-coherence is needed for naturality. Empty covers, zero rings, zero
maps and zero complexes yield the same equality of zero classes. -/
theorem koszulOpenHom_chain_class_naturality
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (L F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (s : koszulOpenSheafComplex A r f e ⟶ L) (t : L ⟶ F) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    H.map (G.map (DerivedCategory.Q.map t))
      (H.map (koszulCechDerivedComparison A r f L)
        (H.map (DerivedCategory.Q.map (colimit.ι
          (koszulCechHomDiagram A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj L)) e))
          (koszulOpenHomStageClass A r f L e s))) =
    H.map (koszulCechDerivedComparison A r f F)
      (H.map (DerivedCategory.Q.map (colimit.ι
        (koszulCechHomDiagram A r f
          (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)) e))
        (koszulOpenHomStageClass A r f F e (s ≫ t))) := by
  let S := (affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)
  let K := (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let iL := colimit.ι (koszulCechHomDiagram A r f (S.obj L)) e
  let iF := colimit.ι (koszulCechHomDiagram A r f (S.obj F)) e
  let jL := koszulCechHomObjIso A r f (S.obj L) e
  let jF := koszulCechHomObjIso A r f (S.obj F) e
  let p := homPostcomp K (S.obj L) (S.obj F) (S.map t)
  let g := jL.hom ≫ p ≫ jF.inv
  have hstage := stageComparison_postcomp A r f L F e t
  change jL.inv ≫ iL ≫ koszulCechComparison A r f L ≫
      (principalCechFunctor r f).map t =
    p ≫ jF.inv ≫ iF ≫ koszulCechComparison A r f F at hstage
  have hd := congrArg (fun h ↦ DerivedCategory.Q.map h ≫
    principalCechDerivedComparison r f F) hstage
  simp only [Functor.map_comp, Category.assoc] at hd
  have hb : DerivedCategory.Q.map jL.inv ≫ DerivedCategory.Q.map iL ≫
      koszulCechDerivedComparison A r f L ≫ G.map (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map p ≫ DerivedCategory.Q.map jF.inv ≫
      DerivedCategory.Q.map iF ≫ koszulCechDerivedComparison A r f F := by
    dsimp only [koszulCechDerivedComparison]
    simp only [Category.assoc]
    rw [cechDerivedComparison_naturality A r f L F t]
    exact hd
  have hc : DerivedCategory.Q.map iL ≫ koszulCechDerivedComparison A r f L ≫
      G.map (DerivedCategory.Q.map t) =
    DerivedCategory.Q.map g ≫ DerivedCategory.Q.map iF ≫
      koszulCechDerivedComparison A r f F := by
    apply (cancel_epi (DerivedCategory.Q.map jL.inv)).mp
    simp only [g, Functor.map_comp, Category.assoc]
    change _ = (DerivedCategory.Q.mapIso jL).inv ≫
      (DerivedCategory.Q.mapIso jL).hom ≫ DerivedCategory.Q.map p ≫
        DerivedCategory.Q.map jF.inv ≫ DerivedCategory.Q.map iF ≫
          koszulCechDerivedComparison A r f F
    rw [Iso.inv_hom_id_assoc]
    exact hb
  have hh := congrArg (fun k ↦ H.map k (koszulOpenHomStageClass A r f L e s)) hc
  simp only [Functor.map_comp, ModuleCat.comp_apply] at hh
  have hz := stageClass_postcomp A r f L F e s t
  change H.map (DerivedCategory.Q.map g) (koszulOpenHomStageClass A r f L e s) =
    koszulOpenHomStageClass A r f F e (s ≫ t) at hz
  dsimp only
  exact hh.trans (congrArg (fun x ↦ H.map (koszulCechDerivedComparison A r f F)
    (H.map (DerivedCategory.Q.map iF) x)) hz)

end AlgebraicGeometry
