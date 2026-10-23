import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackCoherenceStatements
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

noncomputable section
namespace Langlands.Scheme.Modules

private lemma pullback_square_identity {A B : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ B) (j : A ⟶ A) (hj : j = 𝟙 A) (h : j ≫ i = i ≫ 𝟙 B)
    (M : B.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp i (𝟙 B)).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr h.symm).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j i).inv.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hj).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId A).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M) =
    (AlgebraicGeometry.Scheme.Modules.pullback i).map
      ((AlgebraicGeometry.Scheme.Modules.pullbackId B).hom.app M) := by
  subst hj
  have hr := NatTrans.congr_app
    (AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality i) M
  have hl := NatTrans.congr_app
    (AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality i) M
  dsimp at hr hl
  simp only [Category.comp_id] at hr hl
  dsimp [AlgebraicGeometry.Scheme.Modules.pullbackCongr]
  simp only [Category.id_comp]
  rw [hr]
  rw [← cancel_epi ((AlgebraicGeometry.Scheme.Modules.pullbackComp i (𝟙 B)).inv.app M)]
  simp only [Iso.inv_hom_id_app_assoc, hl]
  rfl


private lemma pullback_restrict_square_identity {A B : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ B) (j : A ⟶ A) (hj : j = 𝟙 A) (h : j ≫ i = i ≫ 𝟙 B)
    (R : B.Modules ⥤ A.Modules) (q : R ≅ AlgebraicGeometry.Scheme.Modules.pullback i)
    (M : B.Modules) :
    q.hom.app ((AlgebraicGeometry.Scheme.Modules.pullback (𝟙 B)).obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp i (𝟙 B)).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr h.symm).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j i).inv.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullback j).map (q.inv.app M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hj).hom.app (R.obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId A).hom.app (R.obj M) =
    R.map ((AlgebraicGeometry.Scheme.Modules.pullbackId B).hom.app M) := by
  let e := AlgebraicGeometry.Scheme.Modules.pullbackCongr hj ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackId A
  have hn := e.hom.naturality (q.inv.app M)
  dsimp at hn
  change q.hom.app _ ≫ _ ≫ _ ≫ _ ≫
    (AlgebraicGeometry.Scheme.Modules.pullback j).map (q.inv.app M) ≫ e.hom.app _ = _
  rw [hn]
  have hs := pullback_square_identity i j hj h M
  change _ ≫ _ ≫ _ ≫ e.hom.app _ = _ at hs
  rw [← Category.assoc _ (e.hom.app _) (q.inv.app M),
    ← Category.assoc _ _ (q.inv.app M), ← Category.assoc _ _ (q.inv.app M), hs]
  rw [← Category.assoc, ← q.hom.naturality]
  simp

lemma restrictPullbackNatIso_identity (X : AlgebraicGeometry.Scheme.{u})
    (U : X.Opens) (M : X.Modules) :
    (restrictPullbackNatIso (𝟙 X) U).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_id U)).hom.app
        (M.restrict U.ι) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId U.toScheme).hom.app (M.restrict U.ι) =
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M) := by
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      (pullback_restrict_square_identity U.ι (𝟙 X ∣_ U) (morphismRestrict_id U)
        (morphismRestrict_ι (𝟙 X) U) _
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι) M))))

private lemma conjugate_functor_map_identity {C : Type*} [Category* C]
    (F : C ⥤ C) (e : F ≅ 𝟭 C) {A B A' B' : C}
    (rA : A' ≅ F.obj A) (rB : B' ≅ F.obj B) (iA : A' ≅ A) (iB : B' ≅ B)
    (hrA : rA.hom ≫ e.hom.app A = iA.hom)
    (hrB : rB.hom ≫ e.hom.app B = iB.hom) (k : A ⟶ B) :
    rA.hom ≫ F.map k ≫ rB.inv = iA.hom ≫ k ≫ iB.inv := by
  rw [← cancel_mono iB.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hrB, rB.inv_hom_id_assoc, e.hom.naturality,
    ← Category.assoc, hrA]
  rfl

lemma localHomPullbackIdentity : LocalHomPullbackIdentityStatement.{u} := by
  intro X M N U h
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback]
  change _ = internalHomSectionsEquiv _ _ U
    ((internalHomMap ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app N)).app U h)
  rw [internalHomSectionsEquiv_naturality]
  exact conjugate_functor_map_identity _
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_id U) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackId U.toScheme)
    ((restrictPullbackNatIso (𝟙 X) U).app M)
    ((restrictPullbackNatIso (𝟙 X) U).app N)
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).app M))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).app N))
    (restrictPullbackNatIso_identity X U M) (restrictPullbackNatIso_identity X U N)
    (internalHomSectionsEquiv M N U h)

private def pullbackSquareHom {A B X Y : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (a : A ⟶ B)
    (h : a ≫ j = i ≫ f) (M : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback i).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ⟶
    (AlgebraicGeometry.Scheme.Modules.pullback a).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback j).obj M) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp i f).hom.app M ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr h.symm).hom.app M ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp a j).inv.app M

open Langlands.SchemeModule.RigidifiedModule in
private lemma pullbackSquareHom_comp {A B X Y : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (a : A ⟶ B)
    (h : a ≫ j = i ≫ f) (M : Y.Modules) :
    pullbackSquareHom i j f a h M ≫ compHom a j (i ≫ f) h M =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp i f).hom.app M := by
  simp [pullbackSquareHom, compHom, AlgebraicGeometry.Scheme.Modules.pullbackCongr]

open Langlands.SchemeModule.RigidifiedModule in
private lemma pullbackSquareHom_composition {A B C X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : A ⟶ B) (b : B ⟶ C)
    (ha : a ≫ j = i ≫ f) (hb : b ≫ k = j ≫ g)
    (hc : (a ≫ b) ≫ k = i ≫ (f ≫ g)) (M : Z.Modules) :
    pullbackSquareHom i j f a ha ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackSquareHom j k g b hb M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback k).obj M) =
    (AlgebraicGeometry.Scheme.Modules.pullback i).map
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M) ≫
      pullbackSquareHom i k (f ≫ g) (a ≫ b) hc M := by
  have he : a ≫ (j ≫ g) = i ≫ (f ≫ g) := by
    rw [← Category.assoc, ha, Category.assoc]
  have e1 := compHom_assoc i f g (i ≫ f) (f ≫ g) (i ≫ (f ≫ g))
    rfl rfl (Category.assoc _ _ _) rfl M
  have e2 := compHom_assoc a j g (i ≫ f) (j ≫ g) (i ≫ (f ≫ g))
    ha rfl (Category.assoc _ _ _) he M
  have e3 := compHom_assoc a b k (a ≫ b) (j ≫ g) (i ≫ (f ≫ g))
    rfl hb hc he M
  simp only [compHom_rfl] at e1 e2 e3
  have : IsIso (compHom (a ≫ b) k (i ≫ (f ≫ g)) hc M) := by
    unfold compHom
    infer_instance
  rw [← cancel_mono (compHom (a ≫ b) k (i ≫ (f ≫ g)) hc M)]
  simp only [Category.assoc]
  rw [pullbackSquareHom_comp, e3]
  rw [← Category.assoc _ _ (compHom a (j ≫ g) (i ≫ (f ≫ g)) he M),
    ← Functor.map_comp, pullbackSquareHom_comp]
  rw [← e2, reassoc_of% (pullbackSquareHom_comp i j f a ha _), e1]

private def pullbackRestrictSquareHom {A B X Y : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (a : A ⟶ B)
    (h : a ≫ j = i ≫ f) (R : X.Modules ⥤ A.Modules) (S : Y.Modules ⥤ B.Modules)
    (q : R ≅ AlgebraicGeometry.Scheme.Modules.pullback i)
    (r : S ≅ AlgebraicGeometry.Scheme.Modules.pullback j) (M : Y.Modules) :
    R.obj ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback a).obj (S.obj M) :=
  q.hom.app _ ≫ pullbackSquareHom i j f a h M ≫
    (AlgebraicGeometry.Scheme.Modules.pullback a).map (r.inv.app M)

private lemma pullbackRestrictSquareHom_composition
    {A B C X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (ha : a ≫ j = i ≫ f) (hb : b ≫ k = j ≫ g)
    (hc : c ≫ k = i ≫ (f ≫ g)) (he : c = a ≫ b)
    (R : X.Modules ⥤ A.Modules) (S : Y.Modules ⥤ B.Modules) (T : Z.Modules ⥤ C.Modules)
    (q : R ≅ AlgebraicGeometry.Scheme.Modules.pullback i)
    (r : S ≅ AlgebraicGeometry.Scheme.Modules.pullback j)
    (s : T ≅ AlgebraicGeometry.Scheme.Modules.pullback k) (M : Z.Modules) :
    pullbackRestrictSquareHom i j f a ha R S q r
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback a).map
        (pullbackRestrictSquareHom j k g b hb S T r s M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.app (T.obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr he.symm).hom.app (T.obj M) =
    R.map ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M) ≫
      pullbackRestrictSquareHom i k (f ≫ g) c hc R T q s M := by
  subst he
  simp only [AlgebraicGeometry.Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  simp only [pullbackRestrictSquareHom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, r.inv_hom_id_app]
  erw [(AlgebraicGeometry.Scheme.Modules.pullback a).map_id]
  rw [Category.id_comp]
  have hn := (AlgebraicGeometry.Scheme.Modules.pullbackComp a b).hom.naturality (s.inv.app M)
  dsimp at hn
  rw [hn]
  have hs := pullbackSquareHom_composition i j k f g a b ha hb hc M
  rw [reassoc_of% hs]
  rw [← Category.assoc (q.hom.app _) _ _, ← q.hom.naturality]
  simp only [Category.assoc]

private lemma restrictPullbackNatIso_hom_app_eq
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (restrictPullbackNatIso f U).hom.app M =
      pullbackRestrictSquareHom (f ⁻¹ᵁ U).ι U.ι f (f ∣_ U) (morphismRestrict_ι f U)
        _ _ (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _)
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _) M := by
  dsimp only [restrictPullbackNatIso, pullbackRestrictSquareHom, pullbackSquareHom,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Iso.symm_hom]
  simp only [Category.assoc]

set_option maxHeartbeats 800000 in
lemma restrictPullbackNatIso_composition
    {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (M : Z.Modules) :
    (restrictPullbackNatIso f (g ⁻¹ᵁ U)).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ g ⁻¹ᵁ U)).map
        ((restrictPullbackNatIso g U).hom.app M) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ g ⁻¹ᵁ U) (g ∣_ U)).hom.app
        (M.restrict U.ι) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_comp f g U).symm).hom.app
        (M.restrict U.ι) =
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor ((f ≫ g) ⁻¹ᵁ U).ι).map
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M) ≫
      (restrictPullbackNatIso (f ≫ g) U).hom.app M := by
  rw [restrictPullbackNatIso_hom_app_eq, restrictPullbackNatIso_hom_app_eq,
    restrictPullbackNatIso_hom_app_eq]
  exact pullbackRestrictSquareHom_composition
    (f ⁻¹ᵁ g ⁻¹ᵁ U).ι (g ⁻¹ᵁ U).ι U.ι f g (f ∣_ g ⁻¹ᵁ U) (g ∣_ U) ((f ≫ g) ∣_ U)
    (morphismRestrict_ι f (g ⁻¹ᵁ U)) (morphismRestrict_ι g U)
    (morphismRestrict_ι (f ≫ g) U) (morphismRestrict_comp f g U)
    _ _ _ (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _)
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _)
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _) M

private lemma conjugate_functor_map {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (e : F ≅ G) {A B : C} {A' B' : D}
    (rA : A' ≅ F.obj A) (rB : B' ≅ F.obj B)
    (iA : A' ≅ G.obj A) (iB : B' ≅ G.obj B)
    (hrA : rA.hom ≫ e.hom.app A = iA.hom)
    (hrB : rB.hom ≫ e.hom.app B = iB.hom) (k : A ⟶ B) :
    rA.hom ≫ F.map k ≫ rB.inv = iA.hom ≫ G.map k ≫ iB.inv := by
  rw [← cancel_mono iB.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hrB, rB.inv_hom_id_assoc, e.hom.naturality,
    ← Category.assoc, hrA]

private lemma conjugate_functor_map_composition
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E) (e : G ⋙ F ≅ H)
    {A B : C} {A' B' : D} {A'' B'' A''' B''' : E}
    (rA : A' ≅ G.obj A) (rB : B' ≅ G.obj B)
    (sA : A'' ≅ F.obj A') (sB : B'' ≅ F.obj B')
    (tA : A''' ≅ H.obj A) (tB : B''' ≅ H.obj B)
    (iA : A'' ≅ A''') (iB : B'' ≅ B''')
    (hrA : sA.hom ≫ F.map rA.hom ≫ e.hom.app A = iA.hom ≫ tA.hom)
    (hrB : sB.hom ≫ F.map rB.hom ≫ e.hom.app B = iB.hom ≫ tB.hom) (k : A ⟶ B) :
    sA.hom ≫ F.map (rA.hom ≫ G.map k ≫ rB.inv) ≫ sB.inv =
      iA.hom ≫ (tA.hom ≫ H.map k ≫ tB.inv) ≫ iB.inv := by
  have h := conjugate_functor_map (G ⋙ F) H e
    (sA ≪≫ F.mapIso rA) (sB ≪≫ F.mapIso rB) (iA ≪≫ tA) (iB ≪≫ tB)
    ((Category.assoc _ _ _).trans hrA) ((Category.assoc _ _ _).trans hrB) k
  simpa only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc] using h

set_option maxHeartbeats 800000 in
lemma localHomPullbackComposition : LocalHomPullbackCompositionStatement.{u} := by
  intro X Y Z f g M N U h
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback, internalHomSectionsEquiv_localHomPullback]
  change _ = internalHomSectionsEquiv _ _ _
    ((internalHomMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app N)).app _
      (localHomPullback (f ≫ g) U h))
  rw [internalHomSectionsEquiv_naturality, internalHomSectionsEquiv_localHomPullback]
  exact conjugate_functor_map_composition
    (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ g ⁻¹ᵁ U))
    (AlgebraicGeometry.Scheme.Modules.pullback (g ∣_ U))
    (AlgebraicGeometry.Scheme.Modules.pullback ((f ≫ g) ∣_ U))
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (f ∣_ g ⁻¹ᵁ U) (g ∣_ U) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_comp f g U).symm)
    ((restrictPullbackNatIso g U).app M) ((restrictPullbackNatIso g U).app N)
    ((restrictPullbackNatIso f (g ⁻¹ᵁ U)).app ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M))
    ((restrictPullbackNatIso f (g ⁻¹ᵁ U)).app ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N))
    ((restrictPullbackNatIso (f ≫ g) U).app M) ((restrictPullbackNatIso (f ≫ g) U).app N)
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor ((f ≫ g) ⁻¹ᵁ U).ι).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor ((f ≫ g) ⁻¹ᵁ U).ι).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app N))
    (restrictPullbackNatIso_composition f g U M) (restrictPullbackNatIso_composition f g U N)
    (internalHomSectionsEquiv M N U h)

lemma localHomPullbackCoherence : LocalHomPullbackCoherenceStatement.{u} :=
  ⟨localHomPullbackIdentity, localHomPullbackComposition⟩

end Langlands.Scheme.Modules
