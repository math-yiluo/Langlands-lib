/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Naturality of the source-open comparison with respect to adjunction units

Source: Stacks Project, Tags 08HY and 0D5S, applied to the source-open comparison
of Tag 0DJ9. (blueprint: lem-pc-single-complex-open-unit-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem homEquiv_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (M : C) (N : D) (b : L₁.obj M ⟶ N) :
    a₁.homEquiv M N b ≫ (conjugateEquiv a₁ a₂ α).app N =
      a₂.homEquiv M N (α.app M ≫ b) := by
  rw [Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv a₁ a₂ α).naturality b, ← Category.assoc,
    unit_conjugateEquiv, Category.assoc, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit]

private theorem restriction_mate
    {C D E F H J : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* F] [Category* H] [Category* J]
    {L : C ⥤ D} {R : D ⥤ C} {G : C ⥤ E}
    {L' : E ⥤ F} {R' : F ⥤ E} {T : D ⥤ H} {RT : H ⥤ D}
    {P : F ⥤ J} {RP : J ⥤ F} {V : H ⥤ J} {B : D ⥤ F}
    {L₀ : C ⥤ H} {R₀ : H ⥤ C} {L₁ : E ⥤ J} {R₁ : J ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') (aT : T ⊣ RT) (ap : P ⊣ RP)
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁)
    (ct : L ⋙ T ≅ L₀) (cp : L' ⋙ P ≅ L₁)
    (q : G ⋙ L' ≅ L ⋙ B) (qU : G ⋙ L₁ ≅ L₀ ⋙ V)
    (r : T ⋙ V ≅ B ⋙ P)
    (hq : ∀ M : C,
      P.map (q.hom.app M) ≫ r.inv.app (L.obj M) =
        cp.hom.app (G.obj M) ≫ qU.hom.app M ≫ V.map (ct.inv.app M))
    (K : D) (K' : F) (φ : B.obj K ⟶ K') :
    let k := conjugateIsoEquiv a₀ (a.comp aT) ct
    let k' := conjugateIsoEquiv a₁ (a'.comp ap) cp
    G.map (R.map (aT.unit.app K) ≫ k.inv.app (T.obj K)) ≫
        a₁.homEquiv (G.obj (R₀.obj (T.obj K))) (V.obj (T.obj K))
          (qU.hom.app (R₀.obj (T.obj K)) ≫
          V.map (a₀.counit.app (T.obj K))) ≫
        R₁.map (r.hom.app K ≫ P.map φ) =
      (a'.homEquiv (G.obj (R.obj K)) (B.obj K) (q.hom.app (R.obj K) ≫ B.map (a.counit.app K)) ≫
        R'.map φ) ≫ (R'.map (ap.unit.app K') ≫ k'.inv.app (P.obj K')) := by
  intro k k'
  apply (cancel_mono (k'.hom.app (P.obj K'))).mp
  simp only [Category.assoc]
  rw [k'.hom.naturality (r.hom.app K ≫ P.map φ)]
  simp only [Functor.comp_map, Iso.inv_hom_id_app]
  conv_lhs => arg 2; rw [← Category.assoc]
  simp only [k', conjugateIsoEquiv_apply_hom]
  erw [homEquiv_conjugate]
  erw [← (a'.comp ap).homEquiv_naturality_right]
  erw [← (a'.comp ap).homEquiv_naturality_left]
  rw [Adjunction.comp_homEquiv]
  change (a').homEquiv _ _ ((ap.homEquiv _ _ _)) = _
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id]
  rw [← R'.map_comp, ← a'.homEquiv_naturality_right]
  apply congrArg (a'.homEquiv (G.obj (R.obj K)) (RP.obj (P.obj K')))
  rw [← ap.unit_naturality φ]
  rw [← Category.assoc]
  have hu (b : L'.obj (G.obj (R.obj K)) ⟶ B.obj K) :
      b ≫ ap.unit.app (B.obj K) = ap.homEquiv _ _ (P.map b) := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      (ap.homEquiv_naturality_left b (𝟙 _)).symm
  conv_rhs => rw [← Category.assoc]
  rw [hu]
  rw [← ap.homEquiv_naturality_right]
  apply congrArg (ap.homEquiv (L'.obj (G.obj (R.obj K))) (P.obj K'))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  have hk : L₀.map (k.inv.app (T.obj K)) ≫ a₀.counit.app (T.obj K) =
      ct.inv.app (R.obj (RT.obj (T.obj K))) ≫
        (T.map (a.counit.app (RT.obj (T.obj K))) ≫ aT.counit.app (T.obj K)) := by
    simpa only [k, conjugateIsoEquiv_apply_inv, Adjunction.comp_counit_app,
      Functor.comp_obj] using
      conjugateEquiv_counit (a.comp aT) a₀ ct.inv (T.obj K)
  rw [reassoc_of% cp.hom.naturality (G.map (k.inv.app (T.obj K)))]
  rw [reassoc_of% qU.hom.naturality (k.inv.app (T.obj K))]
  change _ ≫ _ ≫ _ ≫ V.map (L₀.map (k.inv.app (T.obj K))) ≫ _ = _
  rw [← V.map_comp_assoc, hk]
  simp only [V.map_comp, Category.assoc]
  rw [← reassoc_of% hq (R.obj (RT.obj (T.obj K)))]
  rw [← P.map_comp_assoc]
  erw [q.hom.naturality (R.map (aT.unit.app K))]
  simp only [Functor.comp_map, P.map_comp, Category.assoc]
  change _ ≫ P.map (B.map (L.map (R.map (aT.unit.app K)))) ≫ _ = _
  rw [← reassoc_of% r.inv.naturality (a.counit.app (RT.obj (T.obj K)))]
  rw [← P.map_comp_assoc (B.map (L.map (R.map (aT.unit.app K))))
    (B.map (a.counit.app (RT.obj (T.obj K)))), ← B.map_comp]
  erw [a.counit_naturality (aT.unit.app K)]
  simp only [B.map_comp, P.map_comp, Category.assoc]
  rw [reassoc_of% r.inv.naturality (aT.unit.app K)]
  rw [← V.map_comp_assoc, aT.left_triangle_components]
  simp

private theorem restriction_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (c : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
      derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t))
    (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f)
            (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
              (Category.assoc h f g)))
    {X X' S S' A B : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (t : A ⟶ X) (p : B ⟶ X') (v : B ⟶ A)
    (hv : v ≫ t = p ≫ g') (ht : v ≫ (t ≫ f) = (p ≫ f') ≫ g)
    (M : schemeDerivedCategory S) :
    (derivedPullback p).map ((c f' g).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) h.symm) ≫
        (c g' f).inv.app M) ≫
      (c p g').hom.app ((derivedPullback f).obj M) ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj
        ((derivedPullback f).obj M)) hv.symm) ≫
      (c v t).inv.app ((derivedPullback f).obj M) =
    (c p f').hom.app ((derivedPullback g).obj M) ≫
      (c (p ≫ f') g).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) ht.symm) ≫
      (c v (t ≫ f)).inv.app M ≫ (derivedPullback v).map ((c t f).inv.app M) := by
  have hp := congrArg (fun z ↦ z.hom.app M) (hc p f' g)
  have hg := congrArg (fun z ↦ z.hom.app M) (hc p g' f)
  have hvt := congrArg (fun z ↦ z.hom.app M) (hc v t f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app,
    Functor.comp_obj, Category.id_comp] at hp hg hvt
  apply (cancel_mono ((derivedPullback v).map ((c t f).hom.app M) ≫
    (c v (t ≫ f)).hom.app M)).mp
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc (derivedPullback v)
    ((c t f).inv.app M) ((c t f).hom.app M), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rw [hvt]
  simp only [Iso.inv_hom_id_app_assoc]
  have hn := eqToHom_naturality
    (fun s : B ⟶ X ↦ (c s f).hom.app M) hv.symm
  rw [← reassoc_of% hn]
  have hn' := eqToHom_iso_hom_naturality
    (fun s : X' ⟶ S ↦ (c p s).app M) h.symm
  have hg' : (c p g').hom.app ((derivedPullback f).obj M) ≫
      (c (p ≫ g') f).hom.app M =
      (derivedPullback p).map ((c g' f).hom.app M) ≫
        (c p (g' ≫ f)).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M)
          (Category.assoc p g' f).symm) := by
    apply (cancel_mono (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M)
      (Category.assoc p g' f)))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hg.symm
  rw [reassoc_of% hg']
  rw [← (derivedPullback p).map_comp_assoc ((c g' f).inv.app M)
    ((c g' f).hom.app M), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  simp only [eqToHom_trans]
  have hp' : (c p f').hom.app ((derivedPullback g).obj M) ≫
      (c (p ≫ f') g).hom.app M =
      (derivedPullback p).map ((c f' g).hom.app M) ≫
        (c p (f' ≫ g)).hom.app M ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M)
          (Category.assoc p f' g).symm) := by
    apply (cancel_mono (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M)
      (Category.assoc p f' g)))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hp.symm
  rw [reassoc_of% hp']
  simp only [eqToHom_trans]
  have mid : (c p (f' ≫ g)).hom.app M ≫
      eqToHom (congrArg (fun s ↦ (derivedPullback (p ≫ s)).obj M) h.symm) =
      (derivedPullback p).map
        (eqToHom (congrArg (fun s ↦ (derivedPullback s).obj M) h.symm)) ≫
        (c p (g' ≫ f)).hom.app M := by
    simpa only [Iso.app_hom, eqToHom_map] using hn'
  rw [← reassoc_of% mid]
  simp only [eqToHom_trans]

/-- The source-open comparison intertwines restriction units, including its given
coefficient morphism. This is an equality, without any invertibility hypothesis.
Source: Stacks Project, Tag 08HY, adjoint counit description, and Tag 0D5S,
composition of derived pullbacks; the restricted map in Tag 0DJ9.
(blueprint: lem-pc-single-complex-open-unit-naturality).

Proof: Write t = U.ι, p = pullback.fst g' t and v = pullback.snd g' t.
The right-adjoint comparisons k are the mates of the selected pullback
composition isomorphisms c. Transpose the equation under the composite
adjunction for p followed by f'. The definition of k converts transposition
under p ≫ f' into this composite transposition. The unit for p cancels with
its counit by the triangle identity. On the left, expand the counit formula
for base change and the definition of the restricted coefficient morphism.
Naturality of c moves the unit of t past its pullback, and associativity of c
for v,t,f and p,g',f identifies the two ways of composing pullbacks; the
pullback equation v ≫ t = p ≫ g' supplies the intervening equality transport.
The composite-adjunction counit formula for t ≫ f then cancels the unit of t.
The remaining composite on both sides is the transpose of the original
base-change map followed by φ. Naturality of the p-unit moves φ to the right
end. Injectivity of the composite Hom equivalence proves the equality.
All steps are natural transformation identities: zero coefficients, the empty
open and the whole open require no exceptions. -/
theorem singleComplexOpenComparison_unit_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (U : X.Opens) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    let p := pullback.fst g' U.ι
    let k := conjugateIsoEquiv (a (U.ι ≫ f)) ((a f).comp (a U.ι)) (c U.ι f)
    let k' := conjugateIsoEquiv (a (p ≫ f')) ((a f').comp (a p)) (c p f')
    (derivedPullback g).map
        ((schemeDerivedDirectImage f).map ((a U.ι).unit.app K) ≫
          k.inv.app ((derivedPullback U.ι).obj K)) ≫
      singleComplexOpenComparison f f' g g' h K K' φ U =
    (schemeDerivedBaseChangeMap f f' g g' h K ≫
        (schemeDerivedDirectImage f').map φ) ≫
      ((schemeDerivedDirectImage f').map ((a p).unit.app K') ≫
        k'.inv.app ((derivedPullback p).obj K')) := by
  classical
  intro c a p k k'
  let v := pullback.snd g' U.ι
  have hv : v ≫ U.ι = p ≫ g' := (pullback.condition (f := g') (g := U.ι)).symm
  have ht : v ≫ (U.ι ≫ f) = (p ≫ f') ≫ g := by
    rw [← Category.assoc, hv, Category.assoc, h, ← Category.assoc]
  let q : derivedPullback g ⋙ derivedPullback f' ≅
      derivedPullback f ⋙ derivedPullback g' :=
    c f' g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) h.symm) ≪≫ (c g' f).symm
  let qU : derivedPullback g ⋙ derivedPullback (p ≫ f') ≅
      derivedPullback (U.ι ≫ f) ⋙ derivedPullback v :=
    c (p ≫ f') g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) ht.symm) ≪≫
      (c v (U.ι ≫ f)).symm
  let r : derivedPullback U.ι ⋙ derivedPullback v ≅
      derivedPullback g' ⋙ derivedPullback p :=
    c v U.ι ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) hv) ≪≫ (c p g').symm
  have hc := fun {A B C D : Scheme.{u}}
      (s : A ⟶ B) (t : B ⟶ C) (v : C ⟶ D) ↦
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 s t v
  have hq : ∀ M : schemeDerivedCategory S,
      (derivedPullback p).map (q.hom.app M) ≫ r.inv.app ((derivedPullback f).obj M) =
        (c p f').hom.app ((derivedPullback g).obj M) ≫
          qU.hom.app M ≫ (derivedPullback v).map ((c U.ι f).inv.app M) := by
    intro M
    dsimp only [q, qU, r, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
      Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
    simpa only [eqToHom_app, Category.assoc] using
      restriction_square c hc f f' g g' h U.ι p v hv ht M
  have hb : schemeDerivedBaseChangeMap f f' g g' h K =
      (a f').homEquiv ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K))
        ((derivedPullback g').obj K)
        (q.hom.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((a f).counit.app K)) := by
    change (a f').homEquiv _ _
      ((c f' g).hom.app _ ≫ eqToHom _ ≫ (c g' f).inv.app _ ≫
        (derivedPullback g').map ((a f).counit.app K)) = _
    apply congrArg ((a f').homEquiv
      ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K))
      ((derivedPullback g').obj K))
    simp only [q, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  have hbU : schemeDerivedBaseChangeMap (U.ι ≫ f) (p ≫ f') g v ht
      ((derivedPullback U.ι).obj K) =
      (a (p ≫ f')).homEquiv
        ((derivedPullback g).obj ((schemeDerivedDirectImage (U.ι ≫ f)).obj
          ((derivedPullback U.ι).obj K)))
        ((derivedPullback v).obj ((derivedPullback U.ι).obj K))
        (qU.hom.app ((schemeDerivedDirectImage (U.ι ≫ f)).obj
            ((derivedPullback U.ι).obj K)) ≫
          (derivedPullback v).map ((a (U.ι ≫ f)).counit.app ((derivedPullback U.ι).obj K))) := by
    change (a (p ≫ f')).homEquiv _ _
      ((c (p ≫ f') g).hom.app _ ≫ eqToHom _ ≫ (c v (U.ι ≫ f)).inv.app _ ≫
        (derivedPullback v).map ((a (U.ι ≫ f)).counit.app ((derivedPullback U.ι).obj K))) = _
    apply congrArg ((a (p ≫ f')).homEquiv
      ((derivedPullback g).obj ((schemeDerivedDirectImage (U.ι ≫ f)).obj
        ((derivedPullback U.ι).obj K)))
      ((derivedPullback v).obj ((derivedPullback U.ι).obj K)))
    simp only [qU, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  have hs : singleComplexOpenComparison f f' g g' h K K' φ U =
      schemeDerivedBaseChangeMap (U.ι ≫ f) (p ≫ f') g v ht
        ((derivedPullback U.ι).obj K) ≫
      (schemeDerivedDirectImage (p ≫ f')).map (r.hom.app K ≫ (derivedPullback p).map φ) := by
    change schemeDerivedBaseChangeMap (U.ι ≫ f) (p ≫ f') g v ht
      ((derivedPullback U.ι).obj K) ≫ (schemeDerivedDirectImage (p ≫ f')).map
      ((c v U.ι).hom.app K ≫ eqToHom _ ≫ (c p g').inv.app K ≫
        (derivedPullback p).map φ) = _
    apply congrArg (fun b ↦ schemeDerivedBaseChangeMap (U.ι ≫ f) (p ≫ f') g v ht
      ((derivedPullback U.ι).obj K) ≫ (schemeDerivedDirectImage (p ≫ f')).map b)
    simp only [r, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  rw [hs, hb, hbU]
  have hm := restriction_mate (a f) (a f') (a U.ι) (a p)
    (a (U.ι ≫ f)) (a (p ≫ f')) (c U.ι f) (c p f') q qU r hq K K' φ
  simpa only [Category.assoc] using hm

end AlgebraicGeometry
