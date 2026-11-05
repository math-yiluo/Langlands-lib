import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Finite fields of definition of actual group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteStage

open Langlands.AlgebraicGeometry.Picard

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

private def overPullbackTowerIso {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b') :
    Over.pullback b' ≅ Over.pullback b ⋙ Over.pullback c := by
  subst b'
  exact Over.pullbackComp c b

private def baseChangeTowerIso {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : GroupScheme S) : (baseChange b').obj G ≅
      (baseChange c).obj ((baseChange b).obj G) :=
  (Functor.mapGrpNatIso (overPullbackTowerIso b c b' h)).app G ≪≫
    Functor.mapGrpCompIso.app G

private theorem overPullbackTowerIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : Over S) :
    ((overPullbackTowerIso b c b' h).hom.app G).left ≫
        pullback.fst (pullback.snd G.hom b) c =
      pullback.map G.hom b' G.hom b (𝟙 _) c (𝟙 _)
        (by simp) (by simp [h]) := by
  subst b'
  apply (cancel_epi ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).left).mp
  have hi : ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).left ≫
      ((overPullbackTowerIso b c (c ≫ b) rfl).hom.app G).left = 𝟙 _ :=
    congrArg (fun f => f.left) ((overPullbackTowerIso b c (c ≫ b) rfl).app G).inv_hom_id
  rw [← Category.assoc, hi, Category.id_comp]
  apply pullback.hom_ext
  · simp [overPullbackTowerIso, Over.pullbackComp, conjugateIsoEquiv,
      Adjunction.comp_counit_app, Category.assoc]
  · have wi := ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).w
    simp only [Category.assoc, pullback.lift_snd]
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun z => z ≫ c) wi.symm

private theorem baseChangeTowerIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : GroupScheme S) :
    (baseChangeTowerIso b c b' h G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) c =
      pullback.map G.X.hom b' G.X.hom b (𝟙 _) c (𝟙 _)
        (by simp) (by simp [h]) := by
  change ((overPullbackTowerIso b c b' h).hom.app G.X).left ≫ _ = _
  exact overPullbackTowerIso_hom_fst b c b' h G.X

/-- Compare direct extension to Ω with extension through a finite intermediate field. -/
def comparison
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k))) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G) :=
  baseChangeTowerIso (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))
    (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (by rw [← Spec.map_comp, algebraMap_comp_algebraMap]) G

/-- The tower comparison recovers the canonical finite-stage projection. -/
@[reassoc]
theorem comparison_hom_fst
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k))) :
    (comparison k Ω E G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
            (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω))) =
      (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) :=
  baseChangeTowerIso_hom_fst _ _ _ _ G



/-- A finite field of definition includes an actual homomorphism at that field
and an equation recovering the original homomorphism after actual pullback. -/
structure HomModel {G H : GroupScheme (Spec (CommRingCat.of k))}
    (f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H) where
  fieldOfDefinition : FinIntermediateField k Ω
  hom : (baseChange (algebraBaseMap k fieldOfDefinition.1)).obj G ⟶
    (baseChange (algebraBaseMap k fieldOfDefinition.1)).obj H
  recovery : (comparison k Ω fieldOfDefinition G).hom ≫
      (baseChange (algebraBaseMap fieldOfDefinition.1 Ω)).map hom =
    f ≫ (comparison k Ω fieldOfDefinition H).hom

private theorem exists_scheme_map [Algebra.IsAlgebraic k Ω]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : ((baseChange (algebraBaseMap k Ω)).obj G).X ⟶
      ((baseChange (algebraBaseMap k Ω)).obj H).X) :
    ∃ E : FinIntermediateField k Ω,
      ∃ g : ((baseChange (algebraBaseMap k E.1)).obj G).X ⟶
        ((baseChange (algebraBaseMap k E.1)).obj H).X,
        (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫ g.left =
          f.left ≫ (baseChangeCone (Ω := Ω) H.X.left H.X.hom).π.app (op E) := by
  let D := baseChangeDiagram (Ω := Ω) G.X.left G.X.hom
  let c := baseChangeCone (Ω := Ω) G.X.left G.X.hom
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) :=
    { app E := pullback.fst _ _ ≫ G.X.hom
      naturality E E' a := by simp [D, baseChangeDiagram] }
  let a : c.pt ⟶ H.X.left := f.left ≫ pullback.fst _ _
  have fw : f.left ≫ pullback.snd H.X.hom (algebraBaseMap k Ω) =
      pullback.snd G.X.hom (algebraBaseMap k Ω) := f.w
  have aw : a ≫ H.X.hom = pullback.fst G.X.hom (algebraBaseMap k Ω) ≫ G.X.hom := by
    dsimp [a]
    calc
      _ = (f.left ≫ pullback.snd _ _) ≫ algebraBaseMap k Ω := by
        simp only [Category.assoc, pullback.condition]
      _ = pullback.snd _ _ ≫ algebraBaseMap k Ω := by rw [fw]
      _ = _ := pullback.condition.symm
  have ha : c.π ≫ t = (Functor.const _).map (a ≫ H.X.hom) := by
    rw [aw]
    ext E
    simp [c, t, baseChangeCone]
  obtain ⟨E, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t H.X.hom c (isLimitBaseChangeCone G.X.left G.X.hom) a ha
  have hg'' : g ≫ H.X.hom = pullback.snd _ _ ≫ algebraBaseMap k E.unop.1 := by
    simpa [t, pullback.condition] using hg'
  let gE : ((baseChange (algebraBaseMap k E.unop.1)).obj G).X ⟶
      ((baseChange (algebraBaseMap k E.unop.1)).obj H).X :=
    Over.homMk (pullback.lift g (pullback.snd _ _) hg'') (by simp)
  refine ⟨E.unop, gE, ?_⟩
  apply pullback.hom_ext
  · simpa [gE, c, a, baseChangeCone] using hg
  · simp only [gE, Over.homMk_left, Category.assoc, pullback.lift_snd,
      baseChangeCone_π_app]
    rw [← Category.assoc, fw]


private theorem pullback_comm_of_fst
    {S S' : Scheme.{u}} (b : S' ⟶ S) {X Y : Over S} {X' Y' : Over S'}
    (a : X' ⟶ (Over.pullback b).obj X) (c : Y' ⟶ (Over.pullback b).obj Y)
    (f : X' ⟶ Y') (g : X ⟶ Y)
    (h : a.left ≫ pullback.fst X.hom b ≫ g.left =
      f.left ≫ c.left ≫ pullback.fst Y.hom b) :
    a ≫ (Over.pullback b).map g = f ≫ c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_fst] using h
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    calc
      _ = X'.hom := a.w
      _ = f.left ≫ Y'.hom := f.w.symm
      _ = f.left ≫ c.left ≫ pullback.snd Y.hom b :=
        congrArg (fun z => f.left ≫ z) c.w.symm

private theorem pullback_comm_of_fst_factors
    {S S' : Scheme.{u}} (b : S' ⟶ S) {X Y : Over S} {X' Y' : Over S'}
    (a : X' ⟶ (Over.pullback b).obj X) (c : Y' ⟶ (Over.pullback b).obj Y)
    (f : X' ⟶ Y') (g : X ⟶ Y)
    (p : X'.left ⟶ X.left) (q : Y'.left ⟶ Y.left)
    (ha : a.left ≫ pullback.fst X.hom b = p)
    (hc : c.left ≫ pullback.fst Y.hom b = q)
    (h : p ≫ g.left = f.left ≫ q) :
    a ≫ (Over.pullback b).map g = f ≫ c := by
  apply pullback_comm_of_fst
  rw [← Category.assoc, ha, hc]
  exact h

open scoped CategoryTheory.Obj in
private theorem group_hom_of_fpqc_pullback_compat
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b]
    (G H : GroupScheme S) (G' H' : GroupScheme S')
    (a : G' ≅ (baseChange b).obj G) (c : H' ≅ (baseChange b).obj H)
    (f : G' ⟶ H') (g : G.X ⟶ H.X)
    (p : G'.X.left ⟶ G.X.left) (q : H'.X.left ⟶ H.X.left)
    (ha : a.hom.hom.hom.left ≫ pullback.fst G.X.hom b = p)
    (hc : c.hom.hom.hom.left ≫ pullback.fst H.X.hom b = q)
    (hg : p ≫ g.left = f.hom.hom.left ≫ q) :
    ∃ g' : G ⟶ H, a.hom ≫ (baseChange b).map g' = f ≫ c.hom := by
  have hcomm : a.hom.hom.hom ≫ (Over.pullback b).map g =
      f.hom.hom ≫ c.hom.hom.hom :=
    pullback_comm_of_fst_factors b a.hom.hom.hom c.hom.hom.hom
      f.hom.hom g p q ha hc hg
  have hmap : (Over.pullback b).map g = (a.inv ≫ f ≫ c.hom).hom.hom := by
    let aX := (Grp.forget _).mapIso a
    let cX := (Grp.forget _).mapIso c
    let fX := (Grp.forget _).map f
    change (Over.pullback b).map g = aX.inv ≫ fX ≫ cX.hom
    apply (cancel_epi aX.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact hcomm
  have : IsMonHom ((Over.pullback b).map g) := by rw [hmap]; infer_instance
  have : IsMonHom g := GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback b) g
  refine ⟨Grp.homMk g, ?_⟩
  apply Grp.hom_ext
  exact hcomm

/-- Homomorphisms from a quasi-compact, quasi-separated group to a locally
finitely presented group over an algebraic extension have finite models. -/
theorem nonempty_homModel [Algebra.IsAlgebraic k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H) : Nonempty (HomModel k Ω f) := by
  obtain ⟨E, g, hg⟩ := exists_scheme_map k Ω G H f.hom.hom
  obtain ⟨g', hg'⟩ := group_hom_of_fpqc_pullback_compat
    (algebraBaseMap E.1 Ω)
    ((baseChange (algebraBaseMap k E.1)).obj G)
    ((baseChange (algebraBaseMap k E.1)).obj H)
    ((baseChange (algebraBaseMap k Ω)).obj G)
    ((baseChange (algebraBaseMap k Ω)).obj H)
    (comparison k Ω E G) (comparison k Ω E H) f g _ _
    (comparison_hom_fst k Ω E G) (comparison_hom_fst k Ω E H) hg
  exact ⟨⟨E, g', hg'⟩⟩

/-- Choose a finite field of definition together with the actual group
homomorphism there and its exact recovery equation. -/
def homModel [Algebra.IsAlgebraic k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H) : HomModel k Ω f :=
  Classical.choice (nonempty_homModel k Ω f)

variable {k Ω}

/-- A model of a closed subgroup is itself a closed subgroup at its finite
field of definition, when the original source and target are affine. -/
theorem HomModel.isClosedSubgroup
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [IsAffine H.X.left]
    {f : (baseChange (algebraBaseMap k Ω)).obj G ⟶
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : HomModel k Ω f) (hf : IsClosedSubgroup f) : IsClosedSubgroup D.hom := by
  let E := D.fieldOfDefinition
  let q := algebraBaseMap E.1 Ω
  let : Flat q := (fieldExtension_fpqc E.1 Ω).2.1
  let : Surjective q := (fieldExtension_fpqc E.1 Ω).1
  let : IsAffine ((baseChange (algebraBaseMap k E.1)).obj G).X.left := by
    change IsAffine (pullback G.X.hom (algebraBaseMap k E.1))
    infer_instance
  let : IsAffine ((baseChange (algebraBaseMap k E.1)).obj H).X.left := by
    change IsAffine (pullback H.X.hom (algebraBaseMap k E.1))
    infer_instance
  apply IsClosedSubgroup.of_baseChange_of_isAffine q
  have hmap : (baseChange q).map D.hom =
      (comparison k Ω E G).inv ≫ f ≫ (comparison k Ω E H).hom := by
    apply (cancel_epi (comparison k Ω E G).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using D.recovery
  rw [hmap]
  exact (hf.comp_iso (comparison k Ω E H)).iso_comp (comparison k Ω E G).symm

end Langlands.GroupScheme.Descent.FiniteStage
