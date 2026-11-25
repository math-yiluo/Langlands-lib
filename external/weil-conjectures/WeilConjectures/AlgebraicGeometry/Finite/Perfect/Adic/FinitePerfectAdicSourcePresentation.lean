/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantChart
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentationCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantSliceCoherence

/-! # Presentation and scalar-forgetting identities for chart constants

Source: Stacks Project, Tags 093J and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing
  directCoefficientMap overDirectMap

private def sourceDirectIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
      directFinite X d n ⋙ SheafOfModules.overFunctor (completedAdicRing X d) W := by
  have := ProEt.sliceDense X W
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let α := ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n)
  have : Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α) :=
    finitePerfectAdicSliceScalar_injective X d W n
  have : Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α) :=
    finitePerfectAdicSliceScalar_surjective X d W n
  let P := SheafOfModules.restrictScalars
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicProjection X d n))
  let e₀ := isoWhiskerRight (chartConstantsIso X V U W f B)
    (finitePerfectAdicSliceModules X d W n ⋙ P)
  let e₁ := isoWhiskerRight
    (constantAssociatedIso (R := (completedAdicFiniteRing X d n).over W)
      (finitePerfectAdicSliceScalar X d W n)).symm P
  let e₂ := isoWhiskerRight (overDirectIso α W) P
  exact isoWhiskerLeft (finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1)))
    (e₀ ≪≫ e₁ ≪≫ e₂)

attribute [local irreducible] sourceDirectIso
  chartConstantsIso constantAssociatedIso overDirectIso
  directConstant directCoefficientIso finitePerfectAdicAssociatedCoherence

section
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
  {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} D)]
  {R S : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)

private lemma constantAssociatedIso_coefficient_inv (N : ModuleCat.{t + 1} D) :
    (constantAssociatedIso α).inv.app ((ModuleCat.restrictScalars q).obj N) ≫
      (directCoefficientIso α β q p h).hom.app N =
    (finitePerfectAdicAssociated α).map
        ((constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (finitePerfectAdicAssociatedCoherence α β q p h).hom.app
        ((constantSheaf J (ModuleCat.{t + 1} D)).obj N) ≫
      (SheafOfModules.restrictScalars p).map ((constantAssociatedIso β).inv.app N) := by
  apply (cancel_mono ((SheafOfModules.restrictScalars p).map
    ((constantAssociatedIso β).hom.app N))).1
  rw [Category.assoc, constantAssociatedIso_coefficient α β q p h N]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc]
  erw [(SheafOfModules.restrictScalars p).map_id _, Category.comp_id]

private lemma associatedChart_coefficient (N : ModuleCat.{t + 1} D)
    {YB : Sheaf J (ModuleCat.{t + 1} B)} {YD : Sheaf J (ModuleCat.{t + 1} D)}
    (eB : YB ≅ (constantSheaf J (ModuleCat.{t + 1} B)).obj
      ((ModuleCat.restrictScalars q).obj N))
    (eD : YD ≅ (constantSheaf J (ModuleCat.{t + 1} D)).obj N)
    (v : YB ⟶ (sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).obj YD)
    (hv : v ≫ (sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).map eD.hom =
      eB.hom ≫ (constantCommuteCompose J
        (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) :
    (finitePerfectAdicAssociated α).map eB.hom ≫
      (constantAssociatedIso α).inv.app ((ModuleCat.restrictScalars q).obj N) ≫
      (directCoefficientIso α β q p h).hom.app N =
    (finitePerfectAdicAssociated α).map v ≫
      (finitePerfectAdicAssociatedCoherence α β q p h).hom.app YD ≫
      (SheafOfModules.restrictScalars p).map
        ((finitePerfectAdicAssociated β).map eD.hom ≫ (constantAssociatedIso β).inv.app N) := by
  rw [constantAssociatedIso_coefficient_inv α β q p h N,
    ← Category.assoc, ← Functor.map_comp, ← hv, Functor.map_comp]
  simp only [Category.assoc, Functor.map_comp]
  erw [← (finitePerfectAdicAssociatedCoherence α β q p h).hom.naturality_assoc eD.hom]
  rfl

end
private lemma forget_restrict
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (p : R ⟶ S)
    {M N : SheafOfModules.{t + 1} S} (g : M ⟶ N) :
    (SheafOfModules.toSheaf R).map ((SheafOfModules.restrictScalars p).map g) =
      (SheafOfModules.toSheaf S).map g := rfl

private abbrev SourceRestrictionFormula
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{t + 1}}
    (a : T ⟶ R) (b : R ⟶ S) (c : T ⟶ S)
    (M : SheafOfModules.{t + 1} R) (N : SheafOfModules.{t + 1} S)
    (f : (SheafOfModules.restrictScalars a).obj M ⟶
      (SheafOfModules.restrictScalars c).obj N)
    (g : M ⟶ (SheafOfModules.restrictScalars b).obj N) : Prop :=
  (SheafOfModules.toSheaf T).map f = (SheafOfModules.toSheaf R).map g

/-- The scalar-restriction compositor acts identically on the underlying abelian sheaf.

Source: Stacks Project, Tag 06YY.
(blueprint: new-s3-finite-perfect-adic-source-presentation)

Proof: evaluate on an object and a section. The restriction compositor is the
identity linear map on the underlying group, so its image is the identity sheaf map. -/
theorem finitePerfectAdicRestriction_forget_compositor
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (N : SheafOfModules.{t + 1} T) :
    (SheafOfModules.toSheaf R).map (finitePerfectAdicRestrictComp a b c h N).hom =
      𝟙 ((SheafOfModules.toSheaf T).obj N) := by
  ext Z x
  rfl

private lemma forget_over
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{t + 1}) (W : C)
    {M N : SheafOfModules.{t + 1} R} (g : M ⟶ N) :
    (SheafOfModules.toSheaf (R.over W)).map ((SheafOfModules.overFunctor R W).map g) =
      (J.overPullback AddCommGrpCat.{t + 1} W).map ((SheafOfModules.toSheaf R).map g) := rfl

section IsoComponents
variable {C D E E' F : Type*} [Category C] [Category D] [Category E]
  [Category E'] [Category F]

private lemma source_paste_app {R : C ⥤ D} {L : C ⥤ E'} {H : D ⥤ E} {S : E' ⥤ E}
    {P : E ⥤ F} {Q : E' ⥤ F} (e : R ⋙ H ≅ L ⋙ S) (z : S ⋙ P ≅ Q) (N : C) :
    (finitePerfectAdicPasteCoefficientStep e z).hom.app N =
      P.map (e.hom.app N) ≫ z.hom.app (L.obj N) := rfl

private lemma source_trans_app {F G H : C ⥤ D} (e : F ≅ G) (z : G ≅ H) (N : C) :
    (e ≪≫ z).hom.app N = e.hom.app N ≫ z.hom.app N := rfl

private lemma source_whiskerRight_app {F G : C ⥤ D} (e : F ≅ G) (P : D ⥤ E) (N : C) :
    (isoWhiskerRight e P).hom.app N = P.map (e.hom.app N) := rfl

private lemma source_whiskerLeft_app (P : C ⥤ D) {F G : D ⥤ E} (e : F ≅ G) (N : C) :
    (isoWhiskerLeft P e).hom.app N = e.hom.app (P.obj N) := rfl

end IsoComponents

private lemma source_lift_paste_app
    {B D : Type t} [CommRing B] [CommRing D] (q : B →+* D)
    {E : Type*} [Category E]
    {F : ModuleCat.{t + 1} (ULift.{t + 1} B) ⥤ E}
    {G : ModuleCat.{t + 1} (ULift.{t + 1} D) ⥤ E}
    (z : ModuleCat.restrictScalars (RingHom.ulift q) ⋙ F ≅ G)
    (N : ModuleCat.{t} D) :
    (finitePerfectAdicPasteCoefficientStep
      (finitePerfectAdicScalarModelLiftRestrict q) z).hom.app N =
        z.hom.app ((finitePerfectAdicScalarModelLift D).obj N) := by
  simp only [source_paste_app, finitePerfectAdicScalarModelLiftRestrict,
    NatIso.ofComponents_hom_app, Iso.refl_hom]
  erw [F.map_id, Category.id_comp]

private lemma sourceDirectIso_forget (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) :
    letI := ProEt.sliceDense X W
    let α := ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n)
    letI : Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α) :=
        finitePerfectAdicSliceScalar_injective X d W n
    letI : Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op α) :=
        finitePerfectAdicSliceScalar_surjective X d W n
    let αs := finitePerfectAdicSliceScalar X d W n
    letI : Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αs :=
      finitePerfectAdicSliceScalar_injective X d W n
    letI : Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αs :=
      finitePerfectAdicSliceScalar_surjective X d W n
    let M := (finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1))).obj N
    let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
    (SheafOfModules.toSheaf ((completedAdicRing X d).over W)).map
        ((sourceDirectIso X d V U W f n).hom.app N) =
      (SheafOfModules.toSheaf ((completedAdicFiniteRing X d n).over W)).map
        ((finitePerfectAdicAssociated αs).map ((chartConstantsIso X V U W f B).hom.app M) ≫
          (constantAssociatedIso αs).inv.app M ≫ (overDirectIso α W).hom.app M) := by
  dsimp only
  unfold sourceDirectIso
  simp only [source_trans_app, source_whiskerRight_app, source_whiskerLeft_app,
    Iso.symm_hom, Functor.comp_map, Functor.map_comp, forget_restrict,
    finitePerfectAdicSliceModules, finitePerfectAdicAssociated]

section AssociatedOverChart
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
  {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  {R S : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
  (V : C)
  [HasWeakSheafify (J.over V) AddCommGrpCat.{t + 1}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  [HasWeakSheafify (J.over V) (ModuleCat.{t + 1} B)]
  [HasWeakSheafify (J.over V) (ModuleCat.{t + 1} D)]
  [Presheaf.IsLocallyInjective (J.over V) (whiskerLeft (Over.forget V).op α)]
  [Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.forget V).op α)]
  [Presheaf.IsLocallyInjective (J.over V) (whiskerLeft (Over.forget V).op β)]
  [Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.forget V).op β)]

private lemma associatedOverChart_coefficient (N : ModuleCat.{t + 1} D)
    {YB : Sheaf (J.over V) (ModuleCat.{t + 1} B)}
    {YD : Sheaf (J.over V) (ModuleCat.{t + 1} D)}
    (eB : YB ≅ (constantSheaf (J.over V) (ModuleCat.{t + 1} B)).obj
      ((ModuleCat.restrictScalars q).obj N))
    (eD : YD ≅ (constantSheaf (J.over V) (ModuleCat.{t + 1} D)).obj N)
    (v : YB ⟶ (sheafCompose (J.over V) (ModuleCat.restrictScalars.{t + 1} q)).obj YD)
    (hv : v ≫ (sheafCompose (J.over V) (ModuleCat.restrictScalars.{t + 1} q)).map eD.hom =
      eB.hom ≫ (constantCommuteCompose (J.over V)
        (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) :
    let αs : (Functor.const (Over V)ᵒᵖ).obj (RingCat.of B) ⟶ (R.over V).obj :=
      whiskerLeft (Over.forget V).op α
    let βs : (Functor.const (Over V)ᵒᵖ).obj (RingCat.of D) ⟶ (S.over V).obj :=
      whiskerLeft (Over.forget V).op β
    let ps : R.over V ⟶ S.over V := (J.overPullback RingCat.{t + 1} V).map p
    (finitePerfectAdicAssociated αs).map eB.hom ≫
        (constantAssociatedIso αs).inv.app ((ModuleCat.restrictScalars q).obj N) ≫
        (overDirectIso α V).hom.app ((ModuleCat.restrictScalars q).obj N) ≫
        (SheafOfModules.overFunctor R V).map
          ((directCoefficientIso α β q p h).hom.app N) =
      (finitePerfectAdicAssociated αs).map v ≫
        (finitePerfectAdicAssociatedCoherence αs βs q ps
          (fun Z ↦ h ((Over.forget V).op.obj Z))).hom.app YD ≫
        (SheafOfModules.restrictScalars ps).map
          ((finitePerfectAdicAssociated βs).map eD.hom ≫
            (constantAssociatedIso βs).inv.app N ≫ (overDirectIso β V).hom.app N) := by
  dsimp only
  let αs : (Functor.const (Over V)ᵒᵖ).obj (RingCat.of B) ⟶ (R.over V).obj :=
      whiskerLeft (Over.forget V).op α
  let βs : (Functor.const (Over V)ᵒᵖ).obj (RingCat.of D) ⟶ (S.over V).obj :=
      whiskerLeft (Over.forget V).op β
  let ps : R.over V ⟶ S.over V := (J.overPullback RingCat.{t + 1} V).map p
  let P := SheafOfModules.restrictScalars ps
  have hA := associatedChart_coefficient αs βs q ps
    (fun Z ↦ h ((Over.forget V).op.obj Z)) N eB eD v hv
  have hO := overDirectIso_coefficient α β q p h V N
  calc
    _ = (finitePerfectAdicAssociated αs).map eB.hom ≫
        (constantAssociatedIso αs).inv.app ((ModuleCat.restrictScalars q).obj N) ≫
        (directCoefficientIso αs βs q ps
          (fun Z ↦ h ((Over.forget V).op.obj Z))).hom.app N ≫
        P.map ((overDirectIso β V).hom.app N) := by
      exact congrArg (fun k ↦ (finitePerfectAdicAssociated αs).map eB.hom ≫
        (constantAssociatedIso αs).inv.app ((ModuleCat.restrictScalars q).obj N) ≫ k) hO.symm
    _ = _ := by
      have H := congrArg (fun k ↦ k ≫ P.map ((overDirectIso β V).hom.app N)) hA
      simpa only [Functor.map_comp, Category.assoc] using H

end AssociatedOverChart

end AlgebraicGeometry.Scheme
