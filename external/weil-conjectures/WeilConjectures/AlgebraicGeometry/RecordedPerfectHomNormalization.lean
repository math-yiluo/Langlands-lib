/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.RecordedPerfectHomTransport
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension

/-! # Change of the counit normalization in perfect Hom transport

Source: Stacks Project, Cohomology, Tags 06YJ and 0D5S.
(blueprint: lem-pc-recorded-perfect-hom-normalization).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem composition_change
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (Hf : C₁ ⥤ C₀) (Hg : C₂ ⥤ C₁) (Hfg : C₂ ⥤ C₀)
    (Lf : D₁ ⥤ D₀) (Lg : D₂ ⥤ D₁) (Lfg : D₂ ⥤ D₀)
    (ε₀f ε₁f : Q₁ ⋙ Lf ⟶ Hf ⋙ Q₀)
    (ε₀g ε₁g : Q₂ ⋙ Lg ⟶ Hg ⋙ Q₁)
    (ε₀fg ε₁fg : Q₂ ⋙ Lfg ⟶ Hfg ⋙ Q₀)
    (δ : (Hg ⋙ Hf) ⋙ Q₀ ⟶ Hfg ⋙ Q₀)
    (ef : Lf ≅ Lf) (eg : Lg ≅ Lg) (efg : Lfg ≅ Lfg)
    (hf : ∀ K, ef.hom.app (Q₁.obj K) ≫ ε₀f.app K = ε₁f.app K)
    (hg : ∀ K, eg.hom.app (Q₂.obj K) ≫ ε₀g.app K = ε₁g.app K)
    (hfg : ∀ K, efg.hom.app (Q₂.obj K) ≫ ε₀fg.app K = ε₁fg.app K)
    (c₀ c₁ : Lg ⋙ Lf ≅ Lfg)
    (hc₀ : ∀ K, c₀.hom.app (Q₂.obj K) ≫ ε₀fg.app K =
      Lf.map (ε₀g.app K) ≫ ε₀f.app (Hg.obj K) ≫ δ.app K)
    (hc₁ : ∀ K, c₁.hom.app (Q₂.obj K) ≫ ε₁fg.app K =
      Lf.map (ε₁g.app K) ≫ ε₁f.app (Hg.obj K) ≫ δ.app K)
    (hext : ∀ (a b : Lg ⋙ Lf ⟶ Lfg),
      (∀ K, a.app (Q₂.obj K) ≫ ε₀fg.app K =
        b.app (Q₂.obj K) ≫ ε₀fg.app K) → a = b) :
    c₁ ≪≫ efg = Functor.isoWhiskerRight eg Lf ≪≫
      Functor.isoWhiskerLeft Lg ef ≪≫ c₀ := by
  apply Iso.ext
  apply hext
  intro K
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [hfg, hc₁, hc₀, ← hf, ← hg, Functor.map_comp]
  simp only [Category.assoc]
  have hn := ef.hom.naturality (ε₀g.app K)
  dsimp only [Functor.comp_obj] at hn
  rw [← Category.assoc (Lf.map (ε₀g.app K)), hn, Category.assoc]

private theorem conjugated_transport
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (G : A ⥤ B) (F : B ⥤ C) (K : A ⥤ C)
    (c₁ c₀ : K ≅ G ⋙ F) (eG : G ≅ G) (eF : F ≅ F) (eK : K ≅ K)
    (h : c₁ = eK ≪≫ c₀ ≪≫ Functor.isoWhiskerLeft G eF.symm ≪≫
      Functor.isoWhiskerRight eG.symm F)
    {P Q : A} (a : G.obj P ⟶ G.obj Q) :
    c₁.hom.app P ≫ F.map a ≫ c₁.inv.app Q =
      eK.hom.app P ≫ c₀.hom.app P ≫
        F.map (eG.inv.app P ≫ a ≫ eG.hom.app Q) ≫ c₀.inv.app Q ≫ eK.inv.app Q := by
  rw [h]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← eF.inv.naturality_assoc, ← eF.inv.naturality_assoc,
    ← eF.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]


-- Recover the very same counit family already selected by perfectHomComposition.
private noncomputable abbrev oldAdditive :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive :=
  fun f ↦ Classical.choose exists_derivedPullbackComposition f

private noncomputable abbrev oldCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := oldAdditive f
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choose (Classical.choose_spec exists_derivedPullbackComposition) f

private theorem oldUniversal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := oldAdditive f
    (derivedPullback f).IsLeftDerivedFunctor (oldCounit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)) f

-- The universal property determines this isomorphism by its counit factorization.
private noncomputable def normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ≅ derivedPullback f := by
  letI := oldAdditive f
  have := oldUniversal f
  have := recordedDerivedPullbackCounit_universal f
  exact Functor.leftDerivedUnique (derivedPullback f) (derivedPullback f)
    (recordedDerivedPullbackCounit f) (oldCounit f)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))

private theorem normalization_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ)) :
    letI := oldAdditive f
    (normalization f).hom.app (DerivedCategory.Qh.obj K) ≫ (oldCounit f).app K =
      (recordedDerivedPullbackCounit f).app K := by
  let := oldAdditive f
  have := oldUniversal f
  have := recordedDerivedPullbackCounit_universal f
  simp [normalization, Functor.leftDerivedUnique]

private theorem normalization_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    recordedPerfectHomComposition f g ≪≫ normalization (f ≫ g) =
      Functor.isoWhiskerRight (normalization g) (derivedPullback f) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (normalization f) ≪≫
          perfectHomComposition f g := by
  let : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (Scheme.Modules.tensorPullback k).Additive := fun k ↦ oldAdditive k
  have := oldUniversal (f ≫ g)
  let α := Functor.mapHomotopyCategoryCompIso
    ((conjugateIsoEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
      (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)
  apply composition_change
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
    ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ))
    ((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ))
    ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ))
    (derivedPullback f) (derivedPullback g) (derivedPullback (f ≫ g))
    (oldCounit f) (recordedDerivedPullbackCounit f)
    (oldCounit g) (recordedDerivedPullbackCounit g)
    (oldCounit (f ≫ g)) (recordedDerivedPullbackCounit (f ≫ g))
    (Functor.whiskerRight α.hom
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))))
    (normalization f) (normalization g) (normalization (f ≫ g))
    (normalization_fac f) (normalization_fac g) (normalization_fac (f ≫ g))
    (perfectHomComposition f g) (recordedPerfectHomComposition f g)
  · intro K
    have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).1 f g
    change (perfectHomComposition f g).hom = _ at hc
    rw [hc]
    simp only [Functor.leftDerived_fac_app, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp]
    rfl
  · intro K
    change (recordedDerivedPullbackCompositionLift f g).app
      (DerivedCategory.Qh.obj K) ≫ _ = _
    unfold recordedDerivedPullbackCompositionLift
    simp only [Functor.leftDerived_fac_app, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp]
    rfl
  · intro a b hab
    apply (derivedPullback (f ≫ g)).leftDerived_ext (oldCounit (f ≫ g))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
    ext K
    exact hab K

private theorem normalization_composition_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (recordedPerfectHomComposition f g).symm = normalization (f ≫ g) ≪≫
      (perfectHomComposition f g).symm ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (normalization f).symm ≪≫
          Functor.isoWhiskerRight (normalization g).symm (derivedPullback f) := by
  have hi := congrArg (fun e ↦ e.inv) (normalization_composition f g)
  apply Iso.ext
  apply (cancel_epi (normalization (f ≫ g)).inv).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.inv_hom_id_assoc]
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Category.assoc] using hi

private theorem normalization_transport {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g) :
    eqToIso (congrArg (fun k ↦ derivedPullback k) h) ≪≫ normalization g =
      normalization f ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) h) := by
  cases h
  simp

private theorem normalization_comparison {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) :
    recordedPerfectHomComparison s g =
      normalization (pullback.fst s T'.hom) ≪≫ perfectHomComparison s g ≪≫
        Functor.isoWhiskerLeft (derivedPullback (pullback.fst s T.hom))
          (normalization (baseChangeMap s g)).symm ≪≫
        Functor.isoWhiskerRight (normalization (pullback.fst s T.hom)).symm
          (derivedPullback (baseChangeMap s g)) := by
  unfold recordedPerfectHomComparison perfectHomComparison
  rw [normalization_composition_inv]
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, ← Iso.trans_assoc,
    normalization_transport _ _ (baseChangeMap_fst s g).symm]
  simp only [Iso.trans_assoc]

/-- Two composition systems for the same derived pullbacks differ by conjugation
with the universal change-of-counit automorphisms of the direct pullbacks.
No perfectness, finite presentation or filtered diagram is involved.
Source: Stacks Project, Cohomology, Tags 06YJ and 0D5S; uniqueness of the
left-derived universal functor and its composition comparison.
(blueprint: lem-pc-recorded-perfect-hom-normalization).

Proof: write ε₀ for the counits selected with the old composition family and ε₁
for the retained original counits. For every arrow p use leftDerivedUnique to
construct e_p with Qh(e_p.hom) followed by ε₀(p) equal to ε₁(p). Its inverse
satisfies the inverse equation by cancellation. Substitute these equations into
the defining composite-counit expressions for both composition lifts. Naturality
of e_f at ε₀(g) and the functor associators identifies the two expressions.
The left-derived uniqueness property implies
c₁(f,g) = (e_g whiskered by Lf) followed by (Lg whiskered by e_f), then
c₀(f,g), then e_(fg) inverse. Transport through baseChangeMap_fst gives the
corresponding formula for the inverse composition comparison. In its conjugation
on Hom, the two components of e_(baseChangeMap) cancel by naturality at a.
The remaining expression is exactly the equation below. Equality transport is
compatible with e by equality induction. Zero objects and identity arrows use the
same cancellation; no representatives or arbitrary geometric witnesses are chosen. -/
theorem exists_recordedPerfectHom_normalization :
    ∃ e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), derivedPullback f ≅ derivedPullback f,
      ∀ {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
        (P Q : schemeDerivedCategory X)
        (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
          (derivedPullback (pullback.fst s T.hom)).obj Q),
        recordedPerfectHomMap s g a =
          (e (pullback.fst s T'.hom)).hom.app P ≫
            perfectHomMap s g ((e (pullback.fst s T.hom)).inv.app P ≫ a ≫
              (e (pullback.fst s T.hom)).hom.app Q) ≫
                (e (pullback.fst s T'.hom)).inv.app Q := by
  refine ⟨fun f ↦ normalization f, ?_⟩
  intro X S s T T' g P Q a
  simpa only [recordedPerfectHomMap, perfectHomMap, Category.assoc] using
    conjugated_transport
      (derivedPullback (pullback.fst s T.hom)) (derivedPullback (baseChangeMap s g))
      (derivedPullback (pullback.fst s T'.hom))
      (recordedPerfectHomComparison s g) (perfectHomComparison s g)
      (normalization (pullback.fst s T.hom)) (normalization (baseChangeMap s g))
      (normalization (pullback.fst s T'.hom)) (normalization_comparison s g) a

end AlgebraicGeometry
