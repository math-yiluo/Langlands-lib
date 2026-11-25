/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Changing the lower-left base of a derived base-change square

Source: Stacks Project, Remark 20.28.3 (08HY), Lemmas 20.27.2 (0D5S)
and 20.28.2 (0D5T).
(blueprint: lem-pc-derived-base-change-domain-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem domain_equivalence_transport
    {C D B B₀ F : Type*} [Category C] [Category D] [Category B] [Category B₀] [Category F]
    {V : B ⥤ B₀} {T : B₀ ⥤ B} {L : C ⥤ D} {R : D ⥤ C}
    {M : B ⥤ F} {N : F ⥤ B} {M₀ : B₀ ⥤ F} {N₀ : F ⥤ B₀}
    {K : C ⥤ B} {K₀ : C ⥤ B₀} {H : D ⥤ F}
    (adjV : V ⊣ T) [IsIso adjV.unit] (adj : L ⊣ R)
    (adjM : M ⊣ N) (adjM₀ : M₀ ⊣ N₀)
    (cf : V ⋙ M₀ ≅ M) (cg : K ⋙ V ≅ K₀)
    (q : K ⋙ M ≅ L ⋙ H) (q₀ : K₀ ⋙ M₀ ≅ L ⋙ H)
    (hq : ∀ Z : C, M₀.map (cg.hom.app Z) ≫ q₀.hom.app Z =
      cf.hom.app (K.obj Z) ≫ q.hom.app Z) :
    ∃ b : N ≅ N₀ ⋙ T,
    ∃ a : R ⋙ K ≅ R ⋙ K₀ ⋙ T,
      ∀ E : D,
        adjM.homEquiv _ _ (q.hom.app (R.obj E) ≫ H.map (adj.counit.app E)) ≫
            b.hom.app (H.obj E) =
          a.hom.app E ≫ T.map
            (adjM₀.homEquiv _ _ (q₀.hom.app (R.obj E) ≫ H.map (adj.counit.app E))) := by
  let b : N ≅ N₀ ⋙ T := (conjugateIsoEquiv adjM (adjV.comp adjM₀)) cf
  let t : K ≅ K₀ ⋙ T := (Functor.rightUnitor K).symm ≪≫
    Functor.isoWhiskerLeft K (asIso adjV.unit) ≪≫ (Functor.associator K V T).symm ≪≫
    Functor.isoWhiskerRight cg T
  let a : R ⋙ K ≅ R ⋙ K₀ ⋙ T := Functor.isoWhiskerLeft R t ≪≫
    (Functor.associator R K₀ T).symm
  refine ⟨b, a, ?_⟩
  intro E
  let β := adjM.homEquiv _ _ (q.hom.app (R.obj E) ≫ H.map (adj.counit.app E))
  let β₀ := adjM₀.homEquiv _ _ (q₀.hom.app (R.obj E) ≫ H.map (adj.counit.app E))
  have ha : a.hom.app E = adjV.unit.app (K.obj (R.obj E)) ≫
      T.map (cg.hom.app (R.obj E)) := by
    simp only [a, t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_inv_app, Functor.associator_inv_app, Iso.symm_hom, asIso_hom,
      Category.id_comp, Category.comp_id]
  have hb : b.hom.app (H.obj E) =
      (adjV.comp adjM₀).homEquiv _ _
        (cf.hom.app (N.obj (H.obj E)) ≫ adjM.counit.app (H.obj E)) := by
    simp only [b, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
      Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp]
  change β ≫ b.hom.app (H.obj E) = a.hom.app E ≫ T.map β₀
  rw [hb]
  calc
    _ = (adjV.comp adjM₀).homEquiv _ _
        (cf.hom.app (K.obj (R.obj E)) ≫
          (q.hom.app (R.obj E) ≫ H.map (adj.counit.app E))) := by
      have hβ : M.map β ≫ adjM.counit.app (H.obj E) =
          q.hom.app (R.obj E) ≫ H.map (adj.counit.app E) := by
        simpa only [β, Adjunction.homEquiv_symm_apply, Functor.id_obj] using
          (adjM.homEquiv _ _).symm_apply_apply
            (q.hom.app (R.obj E) ≫ H.map (adj.counit.app E))
      have hγ : (V ⋙ M₀).map β ≫
          (cf.hom.app (N.obj (H.obj E)) ≫ adjM.counit.app (H.obj E)) =
            cf.hom.app (K.obj (R.obj E)) ≫
              (q.hom.app (R.obj E) ≫ H.map (adj.counit.app E)) := by
        erw [reassoc_of% cf.hom.naturality β, hβ]
      exact ((adjV.comp adjM₀).homEquiv_naturality_left β _).symm.trans
        (congrArg ((adjV.comp adjM₀).homEquiv _ _) hγ)
    _ = adjV.homEquiv _ _
        (adjM₀.homEquiv _ _
          (M₀.map (cg.hom.app (R.obj E)) ≫
            (q₀.hom.app (R.obj E) ≫ H.map (adj.counit.app E)))) := by
      rw [Adjunction.comp_homEquiv]
      dsimp only [Equiv.trans_apply]
      rw [← Category.assoc, ← hq]
      simp only [Category.assoc]
      rfl
    _ = adjV.homEquiv _ _ (cg.hom.app (R.obj E) ≫ β₀) := by
      rw [adjM₀.homEquiv_naturality_left]
    _ = _ := by
      rw [Adjunction.homEquiv_unit, T.map_comp, ha, Category.assoc]

private theorem pullback_square_precomp
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
    {X S X' S' B : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    (k : B ⟶ S') (fB : X' ⟶ B) (hk : fB ≫ k = f')
    (hB : g' ≫ f = fB ≫ (k ≫ g)) (Z : schemeDerivedCategory S) :
    (derivedPullback fB).map ((c k g).hom.app Z) ≫
        (c fB (k ≫ g)).hom.app Z ≫
        eqToHom (congrArg (fun l ↦ (derivedPullback l).obj Z) hB.symm) ≫
        (c g' f).inv.app Z =
      (c fB k).hom.app ((derivedPullback g).obj Z) ≫
        eqToHom (congrArg (fun l ↦ (derivedPullback l).obj
          ((derivedPullback g).obj Z)) hk) ≫
        (c f' g).hom.app Z ≫
        eqToHom (congrArg (fun l ↦ (derivedPullback l).obj Z) h.symm) ≫
        (c g' f).inv.app Z := by
  have hcomp := congrArg (fun t ↦ t.hom.app Z) (hc fB k g)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp] at hcomp
  apply (cancel_mono ((c g' f).hom.app Z)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% hcomp]
  have hn := eqToHom_naturality (fun l : X' ⟶ S' ↦ (c l g).hom.app Z) hk
  rw [← reassoc_of% hn]
  simp only [eqToHom_trans]


/-- Replace the source of the base morphism by an isomorphic scheme.
Source: Stacks Project, Remark 20.28.3 (08HY), Lemmas 20.27.2 (0D5S)
and 20.28.2 (0D5T).
(blueprint: lem-pc-derived-base-change-domain-iso).

Proof: Write Lk and Rk for the recorded derived pullback and direct image. Use the
pullback comparisons c and identity comparisons i selected in
exists_derivedPullbackComposition, and the adjunctions adj k pinned to these counits
in schemeDerivedBaseChangeMap. The two comparisons c e.hom e.inv and c e.inv e.hom,
composed with i, exhibit L(e.inv) as an equivalence. Hence the unit of its pinned
adjunction adj e.inv is an isomorphism. Put fB = fprime followed by e.hom and
T = R(e.inv). The isomorphism cf : L(e.inv) followed by LfB ≅ Lfprime is
c fB e.inv followed by the equality fB e.inv = fprime. Conjugating cf under
adj fprime and the composite of adj e.inv with adj fB gives b : Rfprime ≅ RfB T.
Take a by applying Rf to the comparison Lg ≅ L(e.inv g) T obtained by inserting
the unit of adj e.inv after Lg, then applying c e.inv g, and reassociating.
For the square comparisons q and qB, associativity of c on fB, e.inv, g gives
LfB of c e.inv g followed by qB = cf at Lg followed by q. The equality transports
agree by naturality of c in fB e.inv = fprime and proof irrelevance.
To prove the mate equation, the component of b is the Hom transpose, under the
composite adjunction, of cf followed by the counit of adj fprime. Naturality of cf
and of that Hom equivalence identify the original mate followed by b with the
composite-adjunction transpose of cf followed by q and Lgprime of the counit of f.
Substitute the square comparison identity. The Hom equivalence of a composite
adjunction is the composite of the two Hom equivalences, so naturality under adj fB
turns this into the Hom transpose, under adj e.inv, of c e.inv g followed by the
new mate. Expanding that Hom transpose as the unit followed by T of the morphism
gives exactly a followed by T of the new mate. All comparisons are natural in E.
No cartesian condition is used; identity coordinates, empty schemes and zero E are
included by the same adjunction and associativity identities. -/
theorem exists_derivedBaseChange_domain_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {B : Scheme.{u}} (e : S' ≅ B)
    (hB : g' ≫ f = (f' ≫ e.hom) ≫ (e.inv ≫ g)) :
    let T := schemeDerivedDirectImage e.inv
    ∃ b : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage (f' ≫ e.hom) ⋙ T,
    ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
        schemeDerivedDirectImage f ⋙ derivedPullback (e.inv ≫ g) ⋙ T,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h E ≫
            b.hom.app ((derivedPullback g').obj E) =
          a.hom.app E ≫ T.map
            (schemeDerivedBaseChangeMap f (f' ≫ e.hom) (e.inv ≫ g) g' hB E) := by
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
  let ev := CategoryTheory.Equivalence.mk (derivedPullback e.inv) (derivedPullback e.hom)
    (c e.hom e.inv ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e.hom_inv_id) ≪≫
      i S').symm
    (c e.inv e.hom ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e.inv_hom_id) ≪≫ i B)
  have : (derivedPullback e.inv).IsEquivalence := ev.isEquivalence_functor
  have : IsIso (adj e.inv).unit := inferInstance
  have hk : (f' ≫ e.hom) ≫ e.inv = f' := by simp only [Category.assoc, e.hom_inv_id,
    Category.comp_id]
  let cf : derivedPullback e.inv ⋙ derivedPullback (f' ≫ e.hom) ≅ derivedPullback f' :=
    c (f' ≫ e.hom) e.inv ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) hk)
  let q : derivedPullback g ⋙ derivedPullback f' ≅
      derivedPullback f ⋙ derivedPullback g' :=
    c f' g ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (c g' f).symm
  let qB : derivedPullback (e.inv ≫ g) ⋙ derivedPullback (f' ≫ e.hom) ≅
      derivedPullback f ⋙ derivedPullback g' :=
    c (f' ≫ e.hom) (e.inv ≫ g) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) hB.symm) ≪≫ (c g' f).symm
  have hq : ∀ Z : schemeDerivedCategory S,
      (derivedPullback (f' ≫ e.hom)).map ((c e.inv g).hom.app Z) ≫ qB.hom.app Z =
        cf.hom.app ((derivedPullback g).obj Z) ≫ q.hom.app Z := by
    intro Z
    simpa only [cf, q, qB, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      eqToIso.hom, eqToHom_app, Category.assoc] using
      pullback_square_precomp c hc f g g' f' h e.inv (f' ≫ e.hom) hk hB Z
  obtain ⟨b, a, ha⟩ := domain_equivalence_transport (adj e.inv) (adj f) (adj f')
    (adj (f' ≫ e.hom)) cf (c e.inv g) q qB hq
  refine ⟨b, a, ?_⟩
  intro E
  have hb : schemeDerivedBaseChangeMap f f' g g' h E =
      (adj f').homEquiv _ _ (q.hom.app _ ≫
        (derivedPullback g').map ((adj f).counit.app E)) := by
    dsimp only [schemeDerivedBaseChangeMap, adj, q, c, ε]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Functor.id_obj, Category.assoc]
  have hbB : schemeDerivedBaseChangeMap f (f' ≫ e.hom) (e.inv ≫ g) g' hB E =
      (adj (f' ≫ e.hom)).homEquiv _ _ (qB.hom.app _ ≫
        (derivedPullback g').map ((adj f).counit.app E)) := by
    dsimp only [schemeDerivedBaseChangeMap, adj, qB, c, ε]
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Functor.id_obj, Category.assoc]
  rw [hb, hbB]
  exact ha E

end AlgebraicGeometry
