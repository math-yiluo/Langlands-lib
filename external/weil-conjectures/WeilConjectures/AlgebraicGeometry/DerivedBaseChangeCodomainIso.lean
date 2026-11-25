/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Changing the common codomain of a derived base-change square

Source: Stacks Project, Remark 20.28.3 (08HY), Lemmas 20.27.2 (0D5S)
and 20.28.2 (0D5T).
(blueprint: lem-pc-derived-base-change-codomain-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem common_equivalence_transport
    {A C D B F : Type*} [Category A] [Category C] [Category D] [Category B] [Category F]
    {V : A ⥤ C} {W : C ⥤ A} {L : C ⥤ D} {R : D ⥤ C}
    {L₀ : A ⥤ D} {R₀ : D ⥤ A} {K : C ⥤ B} {K₀ : A ⥤ B} {H : D ⥤ F} {M : B ⥤ F}
    (adjV : V ⊣ W) [IsIso adjV.counit] (adj : L ⊣ R) (adj₀ : L₀ ⊣ R₀)
    (cf : V ⋙ L ≅ L₀) (cg : V ⋙ K ≅ K₀)
    (q : K ⋙ M ≅ L ⋙ H) (q₀ : K₀ ⋙ M ≅ L₀ ⋙ H)
    (hq : ∀ Z : A, M.map (cg.hom.app Z) ≫ q₀.hom.app Z =
      q.hom.app (V.obj Z) ≫ H.map (cf.hom.app Z)) :
    ∃ a : R ⋙ K ≅ R₀ ⋙ K₀, ∀ E : D,
      M.map (a.hom.app E) ≫ q₀.hom.app (R₀.obj E) ≫ H.map (adj₀.counit.app E) =
        q.hom.app (R.obj E) ≫ H.map (adj.counit.app E) := by
  let d : R₀ ≅ R ⋙ W := (conjugateIsoEquiv adj₀ (adjV.comp adj)) cf
  let t : K ≅ W ⋙ K₀ :=
    (Functor.leftUnitor K).symm ≪≫
      Functor.isoWhiskerRight (asIso adjV.counit).symm K ≪≫
      Functor.associator W V K ≪≫ Functor.isoWhiskerLeft W cg
  let a : R ⋙ K ≅ R₀ ⋙ K₀ := Functor.isoWhiskerLeft R t ≪≫
    (Functor.associator R W K₀).symm ≪≫ Functor.isoWhiskerRight d.symm K₀
  refine ⟨a, ?_⟩
  intro E
  have hd : L₀.map (d.inv.app E) ≫ adj₀.counit.app E =
      cf.inv.app (W.obj (R.obj E)) ≫
        (L.map (adjV.counit.app (R.obj E)) ≫ adj.counit.app E) := by
    simpa only [d, conjugateIsoEquiv_apply_inv, Adjunction.comp_counit_app,
      Functor.comp_obj] using
      conjugateEquiv_counit (adjV.comp adj) adj₀ cf.inv E
  have ha : a.hom.app E = K.map (inv adjV.counit |>.app (R.obj E)) ≫
      cg.hom.app (W.obj (R.obj E)) ≫ K₀.map (d.inv.app E) := by
    simp only [a, t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, asIso_inv, Category.id_comp,
      Category.assoc]
  rw [ha, M.map_comp, M.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% q₀.hom.naturality (d.inv.app E)]
  change _ ≫ _ ≫ _ ≫ H.map (L₀.map (d.inv.app E)) ≫ _ = _
  rw [← H.map_comp, hd, H.map_comp, H.map_comp]
  rw [reassoc_of% hq (W.obj (R.obj E))]
  rw [← H.map_comp_assoc, cf.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  erw [H.map_id, Category.id_comp]
  rw [reassoc_of% q.hom.naturality ((inv adjV.counit).app (R.obj E))]
  change _ ≫ H.map (L.map ((inv adjV.counit).app _)) ≫ _ ≫ _ = _
  rw [← H.map_comp_assoc, ← L.map_comp]
  simp

private theorem pullback_square_postcomp
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l))
    (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f)
            (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
              (Category.assoc h f g)))
    {X S X' S' A : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    (e : S ⟶ A) (hA : g' ≫ (f ≫ e) = f' ≫ (g ≫ e))
    (Z : schemeDerivedCategory A) :
    (derivedPullback f').map ((c g e).hom.app Z) ≫
        (c f' (g ≫ e)).hom.app Z ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj Z) hA.symm) ≫
        (c g' (f ≫ e)).inv.app Z =
      (c f' g).hom.app ((derivedPullback e).obj Z) ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
          ((derivedPullback e).obj Z)) h.symm) ≫
        (c g' f).inv.app ((derivedPullback e).obj Z) ≫
        (derivedPullback g').map ((c f e).hom.app Z) := by
  have hg := congrArg (fun t ↦ t.hom.app Z) (hc f' g e)
  have hf := congrArg (fun t ↦ t.hom.app Z) (hc g' f e)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp] at hg hf
  apply (cancel_mono ((c g' (f ≫ e)).hom.app Z)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% hg, hf]
  simp only [Iso.inv_hom_id_app_assoc]
  apply (cancel_epi ((c f' g).hom.app ((derivedPullback e).obj Z))).mpr
  have hn := eqToHom_naturality
    (fun k : X' ⟶ S ↦ (c k e).hom.app Z) h.symm
  rw [← reassoc_of% hn]
  simp only [eqToHom_trans]



/-- Postcompose both morphisms into the common base with a scheme isomorphism.
Source: Stacks Project, Remark 20.28.3 (08HY), Lemmas 20.27.2 (0D5S)
and 20.28.2 (0D5T).
(blueprint: lem-pc-derived-base-change-codomain-iso).

Proof: Write Lk and Rk for the recorded derived pullback and direct image. Use the
pullback comparisons c and identity comparisons i selected in
exists_derivedPullbackComposition. Their comparisons for e.hom and e.inv, composed
with i, exhibit L(e.hom) and L(e.inv) as inverse equivalences. Adjointify this
explicit equivalence without changing these functors, obtaining adjV with an
invertible counit. Use the adjunctions for f, f e.hom and fprime pinned to the
selected left-derived counits in schemeDerivedBaseChangeMap. Conjugate c f e.hom
under the adjunction for f e.hom and the composite of adjV with the adjunction for f:
this gives d : R(f e.hom) ≅ Rf followed by L(e.inv). Insert the inverse counit of
adjV after Rf and before Lg, then use c g e.hom and d.inv to construct a.
The pullback square comparisons q and qA satisfy Lfprime of c g e.hom followed by
qA = q at L(e.hom) followed by Lgprime of c f e.hom. This is the associativity
law of c applied to fprime,g,e.hom and gprime,f,e.hom; naturality in the equality
of the original square and equality transports identify the remaining factors.
Transpose the required mate equation under the unchanged adjunction for fprime.
Naturality of qA moves d.inv next to the counit for f e.hom. The conjugate-counit
identity replaces their composite by c f e.hom inverse followed by the composite
adjunction counit. The square comparison identity cancels c f e.hom. Naturality of
q then moves the inverse counit of adjV next to its counit; these cancel and leave
q followed by Lgprime of the counit for f, exactly the original transpose.
Injectivity and naturality of the Hom equivalence prove the mate equation for every E.
No cartesian condition is used; identity coordinates, empty schemes and zero E are
included by the same equivalence and associativity identities. -/
theorem exists_derivedBaseChange_codomain_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {A : Scheme.{u}} (e : S ≅ A)
    (hA : g' ≫ (f ≫ e.hom) = f' ≫ (g ≫ e.hom)) :
    ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
        schemeDerivedDirectImage (f ≫ e.hom) ⋙ derivedPullback (g ≫ e.hom),
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h E =
          a.hom.app E ≫
            schemeDerivedBaseChangeMap (f ≫ e.hom) f' (g ≫ e.hom) g' hA E := by
  classical
  let : ∀ {P Q : Scheme.{u}} (k : P ⟶ Q),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun k ↦ (Classical.choose exists_derivedPullbackComposition) k
  let ε : ∀ {P Q : Scheme.{u}} (k : P ⟶ Q),
      DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Q.toRingedSpace)) ⋙
        derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings P.toRingedSpace)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  have hε : ∀ {P Q : Scheme.{u}} (k : P ⟶ Q),
      (derivedPullback k).IsLeftDerivedFunctor (ε k)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Q.toRingedSpace)) (.up ℤ)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let adj : ∀ {P Q : Scheme.{u}} (k : P ⟶ Q),
      derivedPullback k ⊣ schemeDerivedDirectImage k := fun k ↦
    Classical.choose (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k) (ε k) (hε k))
  obtain ⟨i, _, _, hc⟩ :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2
  let ev := CategoryTheory.Equivalence.mk (derivedPullback e.hom) (derivedPullback e.inv)
    (c e.inv e.hom ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e.inv_hom_id) ≪≫
      i A).symm
    (c e.hom e.inv ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e.hom_inv_id) ≪≫ i S)
  have hv : IsIso ev.toAdjunction.counit := by
    change IsIso ev.counitIso.hom
    infer_instance
  let q : derivedPullback g ⋙ derivedPullback f' ≅
      derivedPullback f ⋙ derivedPullback g' :=
    c f' g ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (c g' f).symm
  let qA : derivedPullback (g ≫ e.hom) ⋙ derivedPullback f' ≅
      derivedPullback (f ≫ e.hom) ⋙ derivedPullback g' :=
    c f' (g ≫ e.hom) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) hA.symm) ≪≫ (c g' (f ≫ e.hom)).symm
  have hq : ∀ Z : schemeDerivedCategory A,
      (derivedPullback f').map ((c g e.hom).hom.app Z) ≫ qA.hom.app Z =
        q.hom.app ((derivedPullback e.hom).obj Z) ≫
          (derivedPullback g').map ((c f e.hom).hom.app Z) := by
    intro Z
    simpa only [q, qA, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      eqToIso.hom, eqToHom_app, Category.assoc] using
      pullback_square_postcomp c hc f g g' f' h e.hom hA Z
  obtain ⟨a, ha⟩ := common_equivalence_transport ev.toAdjunction (adj f) (adj (f ≫ e.hom))
    (c f e.hom) (c g e.hom) q qA hq
  refine ⟨a, ?_⟩
  intro E
  have hb : schemeDerivedBaseChangeMap f f' g g' h E =
      (adj f').homEquiv _ _ (q.hom.app _ ≫
        (derivedPullback g').map ((adj f).counit.app E)) := by
    dsimp only [schemeDerivedBaseChangeMap, adj, q, c, ε]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Functor.id_obj, Category.assoc]
  have hbA : schemeDerivedBaseChangeMap (f ≫ e.hom) f' (g ≫ e.hom) g' hA E =
      (adj f').homEquiv _ _ (qA.hom.app _ ≫
        (derivedPullback g').map ((adj (f ≫ e.hom)).counit.app E)) := by
    dsimp only [schemeDerivedBaseChangeMap, adj, qA, c, ε]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Functor.id_obj, Category.assoc]
  rw [hb, hbA]
  have ht := (ha E).symm
  exact (congrArg ((adj f').homEquiv _ _) ht).trans
    ((adj f').homEquiv_naturality_left (a.hom.app E) _)

end AlgebraicGeometry
