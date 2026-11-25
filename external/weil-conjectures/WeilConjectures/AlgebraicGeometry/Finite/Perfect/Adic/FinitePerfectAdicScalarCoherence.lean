/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarRealization
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement

/-! # Canonical scalar coherence of finite quotient realization

Source: Stacks Project, Tags 03CY and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section Associated

variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  {R S : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]

/-- The associated module sheaf for a locally bijective fixed-scalar presentation.
Source: Stacks Tag 03CY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicAssociated :=
  sheafToPresheaf J (ModuleCat.{t + 1} B) ⋙
    ProEtale.finiteCoefficientModulePresheaf C B ⋙ PresheafOfModules.sheafification.{t + 1} α

/-- Extend the abelian sheafification unit across compatible fixed scalar maps.
Source: Stacks Tag 03CY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicAssociatedMap (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : Sheaf J (ModuleCat.{t + 1} D)) :
    (finitePerfectAdicAssociated α).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).obj N) ⟶
      (SheafOfModules.restrictScalars.{t + 1} p).obj
        ((finitePerfectAdicAssociated β).obj N) := by
  let M := (ProEtale.finiteCoefficientModulePresheaf C D).obj N.obj
  let v := PresheafOfModules.toSheafify β (toSheafify J M.presheaf)
  let u :
      (ProEtale.finiteCoefficientModulePresheaf C B).obj
          (((sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).obj N).obj) ⟶
        (PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars.{t + 1} p).obj
            ((finitePerfectAdicAssociated β).obj N)).val :=
    PresheafOfModules.homMk (toSheafify J M.presheaf) (by
      intro Z b x
      have hh := ConcreteCategory.congr_hom (h Z) b
      change p.hom.app Z (α.app Z b) = β.app Z (q b) at hh
      have hv := (v.app Z).hom.map_smul (q b) (show M.obj Z from x)
      change (v.app Z) ((q b) • (show M.obj Z from x)) =
        (β.app Z (q b)) •
          (show ((finitePerfectAdicAssociated β).obj N).val.obj Z from (v.app Z) x) at hv
      rw [← hh] at hv
      exact hv)
  exact (PresheafOfModules.sheafificationHomEquiv α).symm u

private theorem associatedMap_unit (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : Sheaf J (ModuleCat.{t + 1} D)) :
    toSheafify J (N.obj ⋙ forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}) ≫
      (PresheafOfModules.toPresheaf R.obj).map
        (finitePerfectAdicAssociatedMap α β q p h N).val =
      toSheafify J (N.obj ⋙ forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}) := by
  erw [PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
  rfl

private theorem associatedMap_isIso (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    (N : Sheaf J (ModuleCat.{t + 1} D)) :
    IsIso (finitePerfectAdicAssociatedMap α β q p h N) := by
  let F := N.obj ⋙ forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}
  have : IsIso (toSheafify J F) := by
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1})).obj N).property
  have : IsIso (toSheafify J F ≫ (PresheafOfModules.toPresheaf R.obj).map
      (finitePerfectAdicAssociatedMap α β q p h N).val) := by
    rw [associatedMap_unit]
    infer_instance
  have := IsIso.of_isIso_comp_left (toSheafify J F)
    ((PresheafOfModules.toPresheaf R.obj).map
      (finitePerfectAdicAssociatedMap α β q p h N).val)
  have : IsIso ((SheafOfModules.forget R).map
      (finitePerfectAdicAssociatedMap α β q p h N)) :=
    isIso_of_reflects_iso (finitePerfectAdicAssociatedMap α β q p h N).val
      (PresheafOfModules.toPresheaf R.obj)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget R)

private theorem associatedMap_naturality (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
    {N N' : Sheaf J (ModuleCat.{t + 1} D)} (g : N ⟶ N') :
    (finitePerfectAdicAssociated α).map
        ((sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).map g) ≫
        finitePerfectAdicAssociatedMap α β q p h N' =
      finitePerfectAdicAssociatedMap α β q p h N ≫
        (SheafOfModules.restrictScalars.{t + 1} p).map
          ((finitePerfectAdicAssociated β).map g) := by
  apply (SheafOfModules.forget R).map_injective
  apply (PresheafOfModules.toPresheaf R.obj).map_injective
  let F := N.obj ⋙ forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1}
  let gAb := Functor.whiskerRight g.hom
    (forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1})
  have : IsIso (toSheafify J F) := by
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1})).obj N).property
  apply (cancel_epi (toSheafify J F)).mp
  change toSheafify J F ≫ sheafifyMap J gAb ≫
    (PresheafOfModules.toPresheaf R.obj).map
      (finitePerfectAdicAssociatedMap α β q p h N').val =
    toSheafify J F ≫
      (PresheafOfModules.toPresheaf R.obj).map
        (finitePerfectAdicAssociatedMap α β q p h N).val ≫ sheafifyMap J gAb
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    associatedMap_unit, ← Category.assoc, associatedMap_unit]
  exact toSheafify_naturality J gAb

/-- Associated module sheaves commute with compatible scalar restriction by the unique
comparison whose components are the specified sheafification-unit maps.

Source: Stacks Project, Tags 03CY and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence).

Proof: both underlying abelian sheaves are the sheafification of the same presheaf.
Define a map before associated sheafification by its unit on that presheaf. It is
B-linear because the displayed square of scalar maps commutes. The adjunction for
associated module sheafification extends it to an R-linear map. After forgetting
modules, precomposition with the unit identifies this map with the identity; the
unit is invertible since the input is already a sheaf. The forgetful functor reflects
isomorphisms, so this map gives the comparison. Naturality and uniqueness follow from
faithfulness of that same forgetful functor. This includes empty sites and zero rings. -/
theorem finitePerfectAdicAssociated_coherence_existsUnique
    (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z) :
    ∃! e : sheafCompose J (ModuleCat.restrictScalars.{t + 1} q) ⋙
        finitePerfectAdicAssociated α ≅
      finitePerfectAdicAssociated β ⋙ SheafOfModules.restrictScalars.{t + 1} p,
      ∀ N, e.hom.app N = finitePerfectAdicAssociatedMap α β q p h N := by
  have (N : Sheaf J (ModuleCat.{t + 1} D)) :
      IsIso (finitePerfectAdicAssociatedMap α β q p h N) := associatedMap_isIso α β q p h N
  let e : sheafCompose J (ModuleCat.restrictScalars.{t + 1} q) ⋙
      finitePerfectAdicAssociated α ≅
      finitePerfectAdicAssociated β ⋙ SheafOfModules.restrictScalars.{t + 1} p :=
    NatIso.ofComponents
    (fun N ↦ asIso (finitePerfectAdicAssociatedMap α β q p h N))
    (fun g ↦ associatedMap_naturality α β q p h g)
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  exact he' N

/-- The unique associated-sheaf scalar comparison fixed on underlying abelian sheaves.
Source: Stacks Tag 03CY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicAssociatedCoherence (q : B →+* D) (p : R ⟶ S)
    (h : ∀ Z : Cᵒᵖ, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z) :
    sheafCompose J (ModuleCat.restrictScalars.{t + 1} q) ⋙
        finitePerfectAdicAssociated α ≅
      finitePerfectAdicAssociated β ⋙ SheafOfModules.restrictScalars.{t + 1} p :=
  (finitePerfectAdicAssociated_coherence_existsUnique α β q p h).choose

/-- The explicit compositor for ordinary scalar restriction of module sheaves.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicRestrictComp {P : Sheaf J RingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ P) (c : R ⟶ P) (h : a ≫ b = c)
    (N : SheafOfModules.{t + 1} P) :
    (SheafOfModules.restrictScalars.{t + 1} a).obj
        ((SheafOfModules.restrictScalars.{t + 1} b).obj N) ≅
      (SheafOfModules.restrictScalars.{t + 1} c).obj N := by
  refine { hom := { val := { app := fun Z ↦ ?_, naturality := ?_ } }
           inv := { val := { app := fun Z ↦ ?_, naturality := ?_ } }
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · exact (ModuleCat.restrictScalarsComp'App (a.hom.app Z).hom (b.hom.app Z).hom
      (c.hom.app Z).hom (congrArg RingCat.Hom.hom
        (congrArg (fun f ↦ f.hom.app Z) h).symm) (N.val.obj Z)).inv
  · intros; ext; rfl
  · exact (ModuleCat.restrictScalarsComp'App (a.hom.app Z).hom (b.hom.app Z).hom
      (c.hom.app Z).hom (congrArg RingCat.Hom.hom
        (congrArg (fun f ↦ f.hom.app Z) h).symm) (N.val.obj Z)).hom
  · intros; ext; rfl
  · ext; rfl
  · ext; rfl

end Associated

/-- Consecutive finite quotient presentations respect their constant scalar units.
Source: Stacks Tags 03CY and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
theorem finitePerfectAdicSliceScalar_step (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (W : X.ProEt) (n : ℕ) (Z : (Over W)ᵒᵖ) :
    (finitePerfectAdicSliceScalar X d W (n + 1)).app Z ≫
        (completedAdicFiniteStep X d n).hom.app (op Z.unop.left) =
      RingCat.ofHom (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
        (finitePerfectAdicSliceScalar X d W n).app Z := by
  have h := congrArg (fun e ↦ e.app (op Z.unop.left))
    (toSheafify_naturality (ProEt.topology X) (completedAdicFinitePresheafStep X d n))
  change (ProEtale.finiteCoefficientConstants X (completedAdicQuotient d (n + 1))).app
      (op Z.unop.left) ≫
      ((toSheafify (ProEt.topology X)
        (ProEtale.finiteCoefficientPresheaf X (completedAdicQuotient d (n + 1)))).app
          (op Z.unop.left) ≫
        (sheafifyMap (ProEt.topology X) (completedAdicFinitePresheafStep X d n)).app
          (op Z.unop.left)) =
    RingCat.ofHom (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
      ((ProEtale.finiteCoefficientConstants X (completedAdicQuotient d n)).app
        (op Z.unop.left) ≫ (toSheafify (ProEt.topology X)
          (ProEtale.finiteCoefficientPresheaf X (completedAdicQuotient d n))).app
            (op Z.unop.left))
  dsimp only [NatTrans.comp_app] at h
  rw [← h, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun k ↦ k ≫
    (toSheafify (ProEt.topology X)
      (ProEtale.finiteCoefficientPresheaf X (completedAdicQuotient d n))).app
        (op Z.unop.left))
  ext x
  rfl

/-- The componentwise canonical scalar comparison after restricting to the chart slice.
Source: Stacks Tags 03CY and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicScalarComponent
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (N : Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) :
    (finitePerfectAdicScalarModules X d V U W f (n + 1)).obj
        ((sheafCompose (ProEt.topology U.left)
          (ModuleCat.restrictScalars.{t + 1}
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))).obj N) ≅
      (finitePerfectAdicScalarModules X d V U W f n).obj N := by
  have := ProEt.sliceDense X W
  have := finitePerfectAdicSliceScalar_injective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_surjective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  let Q := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let P := (((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
    (ProEt.topology W.left) (ModuleCat.{t + 1} Q)).inverse).obj
      ((ProEtale.localizationRestriction (ModuleCat.{t + 1} Q) f.left
        (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj N)
  let π := ((ProEt.topology X).overPullback RingCat.{t + 1} W)
  let e := (finitePerfectAdicAssociatedCoherence
    (finitePerfectAdicSliceScalar X d W (n + 1)) (finitePerfectAdicSliceScalar X d W n)
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
    (π.map (completedAdicFiniteStep X d n)) (finitePerfectAdicSliceScalar_step X d W n)).app P
  have hw : completedAdicProjection X d (n + 1) ≫ completedAdicFiniteStep X d n =
      completedAdicProjection X d n := by
    simpa only [completedAdicProjection, completedAdicRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ] using
      limit.w (completedAdicRingSystem X d) (homOfLE (Nat.le_succ n)).op
  exact (SheafOfModules.restrictScalars.{t + 1}
      (π.map (completedAdicProjection X d (n + 1)))).mapIso e ≪≫
    finitePerfectAdicRestrictComp (π.map (completedAdicProjection X d (n + 1)))
      (π.map (completedAdicFiniteStep X d n)) (π.map (completedAdicProjection X d n))
      (by rw [← π.map_comp, hw]) ((finitePerfectAdicSliceModules X d W n).obj P)

/-- The ordinary scalar compositor, assembled from associated sheafification and
composition of restriction of scalars. Source: Stacks Tags 03CY and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicScalarModulesCoherence
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    sheafCompose (ProEt.topology U.left)
        (ModuleCat.restrictScalars.{t + 1}
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) ⋙
        finitePerfectAdicScalarModules X d V U W f (n + 1) ≅
      finitePerfectAdicScalarModules X d V U W f n := by
  refine NatIso.ofComponents (finitePerfectAdicScalarComponent X d V U W f n) ?_
  intro N N' g
  have := ProEt.sliceDense X W
  have := finitePerfectAdicSliceScalar_injective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_surjective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  let Q := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  let G := ProEtale.localizationRestriction (ModuleCat.{t + 1} Q) f.left
    (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} Q)).inverse
  let π := ((ProEt.topology X).overPullback RingCat.{t + 1} W)
  have h := (finitePerfectAdicAssociatedCoherence
    (finitePerfectAdicSliceScalar X d W (n + 1)) (finitePerfectAdicSliceScalar X d W n)
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
    (π.map (completedAdicFiniteStep X d n))
      (finitePerfectAdicSliceScalar_step X d W n)).hom.naturality
      (G.map g)
  apply SheafOfModules.hom_ext
  ext Z x
  exact DFunLike.congr_fun
    (congrArg (fun k ↦ (k.val.app Z).hom.toAddMonoidHom) h) x

/-- Localize the uniquely normalized ordinary scalar compositor.
Source: Stacks Tags 05RU and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-coherence). -/
def finitePerfectAdicScalarCoherence
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ) :
    normalizationRestrict (ProEt.topology U.left)
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ⋙
        finitePerfectAdicScalarRealization X d V U W f (n + 1) ≅
      finitePerfectAdicScalarRealization X d V U W f n := by
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f (n + 1)).2.2
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.1
  have := (finitePerfectAdicScalarModules_exact X d V U W f n).2.2
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (finitePerfectAdicScalarModulesCoherence X d V U W f n)

end AlgebraicGeometry.Scheme
