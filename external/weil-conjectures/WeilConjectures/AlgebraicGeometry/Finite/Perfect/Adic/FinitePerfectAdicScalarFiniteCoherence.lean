/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData

/-! # Coefficient transitions for direct finite module sheaves

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
  directCoefficientMap overDirectMap directCoefficientIso

/-- Scalar restriction is compatible with composition of sheaf-ring maps.

Source: Stacks Project, Tag 06YY.
(blueprint: new-s3-finite-perfect-adic-scalar-finite-coherence)

Proof: use the identity on the underlying abelian sheaf. The displayed equality
of ring maps identifies the two scalar actions. These identity maps are natural
in the module sheaf, and their composites are identities. -/
def finitePerfectAdicRestrictCompIso
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    SheafOfModules.restrictScalars b ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars c :=
  NatIso.ofComponents (fun N ↦ finitePerfectAdicRestrictComp a b c h N) (by
    intro N N' g
    apply SheafOfModules.hom_ext
    ext Z x
    rfl)

private lemma restrictCompIso_hom_app
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (N : SheafOfModules.{t + 1} T) :
    (finitePerfectAdicRestrictCompIso a b c h).hom.app N =
      (finitePerfectAdicRestrictComp a b c h N).hom := rfl

attribute [local irreducible] finitePerfectAdicRestrictCompIso

section ProjectedConstants
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  {R S T : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)
  (a : T ⟶ R) (c : T ⟶ S) (hw : a ≫ p = c)

private def projectedConstantIso :
    ModuleCat.restrictScalars q ⋙ directConstant α ⋙ SheafOfModules.restrictScalars a ≅
      directConstant β ⋙ SheafOfModules.restrictScalars c :=
  isoWhiskerRight (directCoefficientIso α β q p h) (SheafOfModules.restrictScalars a) ≪≫
    isoWhiskerLeft (directConstant β) (finitePerfectAdicRestrictCompIso a p c hw)

private lemma projectedConstantIso_unit (N : ModuleCat.{t + 1} D) (Z : Cᵒᵖ) (x : N) :
    ((projectedConstantIso α β q p h a c hw).hom.app N).val.app Z
        ((directConstantUnit α ((ModuleCat.restrictScalars q).obj N)).app Z x) =
      (directConstantUnit β N).app Z x := by
  simp only [projectedConstantIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, restrictCompIso_hom_app, directCoefficientIso_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (directCoefficientMap α β q p h N).val.app Z
      ((directConstantUnit α ((ModuleCat.restrictScalars q).obj N)).app Z x) = _
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (directCoefficientMap_unit α β q p h N) Z) x

end ProjectedConstants

attribute [local irreducible] projectedConstantIso

section LiftedProjectedConstants
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type t} [CommRing B] [CommRing D]
  {R S T : Sheaf J RingCat.{t + 1}}
  (q : B →+* D)
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{t + 1} D)) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom (RingHom.ulift q) ≫ β.app Z)
  (a : T ⟶ R) (c : T ⟶ S) (hw : a ≫ p = c)

private def liftedProjectedIso :
    ModuleCat.restrictScalars q ⋙ directLifted α a ≅ directLifted β c :=
  isoWhiskerRight (finitePerfectAdicScalarModelLiftRestrict q)
      (directConstant α ⋙ SheafOfModules.restrictScalars a) ≪≫
    isoWhiskerLeft (finitePerfectAdicScalarModelLift D)
      (projectedConstantIso α β (RingHom.ulift q) p h a c hw)

private lemma liftedProjectedIso_unit (N : ModuleCat.{t} D) (Z : Cᵒᵖ)
    (x : (finitePerfectAdicScalarModelLift D).obj N) :
    ((liftedProjectedIso q α β p h a c hw).hom.app N).val.app Z
        ((directConstantUnit α ((finitePerfectAdicScalarModelLift B).obj
          ((ModuleCat.restrictScalars q).obj N))).app Z x) =
      (directConstantUnit β ((finitePerfectAdicScalarModelLift D).obj N)).app Z x := by
  simp only [liftedProjectedIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, finitePerfectAdicScalarModelLiftRestrict,
    NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id]
  exact projectedConstantIso_unit α β (RingHom.ulift q) p h a c hw
    ((finitePerfectAdicScalarModelLift D).obj N) Z x

private lemma liftedProjectedIso_coefficient (N : ModuleCat.{t} D) (Z : Cᵒᵖ)
    (x : ((directLifted α a).obj ((ModuleCat.restrictScalars q).obj N)).val.obj Z) :
    ((liftedProjectedIso q α β p h a c hw).hom.app N).val.app Z x =
      ((directCoefficientIso α β (RingHom.ulift q) p h).hom.app
        ((finitePerfectAdicScalarModelLift D).obj N)).val.app Z x := by
  simp only [liftedProjectedIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, finitePerfectAdicScalarModelLiftRestrict,
    NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
    projectedConstantIso, restrictCompIso_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rfl

private structure LiftedConstantTransition where
  iso : ModuleCat.restrictScalars q ⋙ directLifted α a ≅ directLifted β c
  unit : ∀ (N : ModuleCat.{t} D) (Z : Cᵒᵖ) (x : (finitePerfectAdicScalarModelLift D).obj N),
    (iso.hom.app N).val.app Z
        ((directConstantUnit α ((finitePerfectAdicScalarModelLift B).obj
          ((ModuleCat.restrictScalars q).obj N))).app Z x) =
      (directConstantUnit β ((finitePerfectAdicScalarModelLift D).obj N)).app Z x
  coefficient : ∀ (N : ModuleCat.{t} D) (Z : Cᵒᵖ)
    (x : ((directLifted α a).obj ((ModuleCat.restrictScalars q).obj N)).val.obj Z),
    (iso.hom.app N).val.app Z x =
      ((directCoefficientIso α β (RingHom.ulift q) p h).hom.app
        ((finitePerfectAdicScalarModelLift D).obj N)).val.app Z x

private lemma liftedConstantTransition_forget
    (z : LiftedConstantTransition q α β p h a c) (N : ModuleCat.{t} D) :
    (SheafOfModules.toSheaf T).map (z.iso.hom.app N) =
      (SheafOfModules.toSheaf R).map
        ((directCoefficientIso α β (RingHom.ulift q) p h).hom.app
          ((finitePerfectAdicScalarModelLift D).obj N)) := by
  ext Z x
  exact z.coefficient N Z x

private def liftedConstantTransition : LiftedConstantTransition q α β p h a c where
  iso := liftedProjectedIso q α β p h a c hw
  unit := liftedProjectedIso_unit q α β p h a c hw
  coefficient := liftedProjectedIso_coefficient q α β p h a c hw

end LiftedProjectedConstants

attribute [local irreducible] liftedProjectedIso

attribute [local semireducible] completedAdicRing

private lemma finiteProjection_step
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicProjection X d (n + 1) ≫ completedAdicFiniteStep X d n =
      completedAdicProjection X d n := by
  simpa only [completedAdicProjection, completedAdicRing, completedAdicRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ] using
    limit.w (completedAdicRingSystem X d) (homOfLE (Nat.le_succ n)).op

attribute [local irreducible] completedAdicRing

private lemma finiteScalar_step
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) (Z : X.ProEtᵒᵖ) :
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1))).app Z ≫
        (completedAdicFiniteStep X d n).hom.app Z =
      RingCat.ofHom (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
        (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n)).app Z := by
  exact finitePerfectAdicSliceScalar_step X d Z.unop n (op (Over.mk (𝟙 Z.unop)))

private def finiteTransition
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LiftedConstantTransition (C := X.ProEt) (J := ProEt.topology X)
      (R := completedAdicFiniteRing X d (n + 1))
      (S := completedAdicFiniteRing X d n) (T := completedAdicRing X d)
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
      (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1)))
      (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))
      (completedAdicFiniteStep X d n) (finiteScalar_step X d n)
      (completedAdicProjection X d (n + 1)) (completedAdicProjection X d n) :=
  liftedConstantTransition (C := X.ProEt) (J := ProEt.topology X)
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1)))
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))
    (completedAdicFiniteStep X d n) (finiteScalar_step X d n)
    (completedAdicProjection X d (n + 1)) (completedAdicProjection X d n)
    (finiteProjection_step X d n)

attribute [local irreducible] finiteTransition

private def directFiniteStep
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ⋙
        directFinite X d (n + 1) ≅ directFinite X d n := by
  exact (finiteTransition X d n).iso

end AlgebraicGeometry.Scheme
