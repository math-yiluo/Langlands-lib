/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectRingEquiv
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumLift
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement

/-! # Descent of stratified perfect models along isomorphisms of coefficient data

The completed constant realization is left adjoint to global sections with the constant
scalar action, so it commutes with restriction of scalars along the completed isomorphism
induced by a datum isomorphism. With the pullback and slice compatibilities of restriction
of scalars, stratified perfect models of a transported object descend.

## References

* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

private local instance (priority := 100000) fixedSmall (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance (priority := 100000) fixedSheafify
    (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance (priority := 100000) fixedLocallyBijective
    (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The level constant comparison is the sheafified constants map. -/
theorem pbcLevelConstantComparison_hom_eq (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

/-- Level constant comparisons are natural in the quotient ring. -/
theorem pbcLevelConstantComparison_naturality (T : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (pbcLevelConstantComparison T dB n).hom =
      (pbcLevelConstantComparison T dA n).hom ≫ AdicCoefficients.coefficientMap T q := by
  rw [pbcLevelConstantComparison_hom_eq, pbcLevelConstantComparison_hom_eq]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The completed scalar map followed by a level projection is the constant quotient map. -/
theorem pbcCompletedScalar_projection (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcCompletedScalar T d ≫ pbcAdicProjection T d n =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≫
        (pbcLevelConstantComparison T d n).hom := by
  dsimp only [pbcCompletedScalar, pbcAdicProjection, pbcCompletedComparison]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
  change (adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ _) ≫ _ = _
  congr 1
  exact (adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

/-- The completed isomorphism is compatible with the constant scalars. -/
theorem AdicCoefficientDatum.completionIso_scalar (T : Scheme.{u}) :
    pbcCompletedScalar T d ≫ (d.completionIso d' φ hφ T).hom =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ.toRingHom) ≫ pbcCompletedScalar T d' := by
  apply limit.hom_ext
  intro j
  obtain ⟨n⟩ := j
  change _ ≫ pbcAdicProjection T d' n = _ ≫ pbcAdicProjection T d' n
  rw [Category.assoc, d.completionIso_hom_projection d' φ hφ T n, ← Category.assoc,
    pbcCompletedScalar_projection, Category.assoc, Category.assoc,
    pbcCompletedScalar_projection, ← Category.assoc _ _ (pbcLevelConstantComparison T d' n).hom,
    ← Functor.map_comp]
  let := d.quotientFinite
  let := d'.quotientFinite
  change _ ≫ _ ≫ AdicCoefficients.coefficientMap T (d.quotientRingEquiv d' φ hφ n).toRingHom = _
  rw [← pbcLevelConstantComparison_naturality, ← Category.assoc, ← Functor.map_comp]
  rfl

end RingEquiv
section Adjunctions

/-- Restriction along the identity, normalized on underlying sections. -/
def pbcRestrictIdIso {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl)))
      (fun f ↦ by ext U x; rfl)

/-- Restriction along a ring sheaf isomorphism is an equivalence. -/
def pbcRestrictEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    pbcModules T S ≌ pbcModules T R :=
  CategoryTheory.Equivalence.mk (pbcRestrict e.hom) (pbcRestrict e.inv)
    (pbcRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫ pbcRestrictIdIso S).symm
    (pbcRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫ pbcRestrictIdIso R)

/-- The constant presheaf of modules, before sheafification. -/
def adicLisseConstantPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

/-- Maps out of a constant presheaf are maps into sections over a terminal object. -/
def adicLisseConstantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((adicLisseConstantPresheaf X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

/-- The constant presheaf is left adjoint to evaluation at a terminal object. -/
def adicLisseConstantPresheafAdjunction (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantPresheaf X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adicLisseConstantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

/-- Global sections over a terminal object, with the constant scalar action. -/
def adicLisseConstantGlobalSections (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

/-- Constant module sheaves are left adjoint to global sections. -/
def adicLisseConstantModulesAdjunction (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ adicLisseConstantGlobalSections X A T :=
  (adicLisseConstantPresheafAdjunction X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit X A))

/-- Global sections of completed modules, with the constant scalar action. -/
private def integralGlobalSections {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (pbcCompletedScalar X d) ⋙ adicLisseConstantGlobalSections X A T

/-- The completed constant realization is left adjoint to global sections. -/
private def integralConstantAdjunction {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobalSections X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((adicLisseConstantModulesAdjunction X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

end Adjunctions
section ConstantTransport

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

private theorem completionIso_scalar_apply (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : A') :
    (d.completionIso d' φ hφ T).hom.hom.app U ((pbcCompletedScalar T d).hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U (φ.symm a))) =
    (pbcCompletedScalar T d').hom.app U
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A'))).app U a) := by
  have h := congrArg (fun f ↦ f.hom.app U ((toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).app U (φ.symm a)))
    (d.completionIso_scalar d' φ hφ T)
  refine h.trans ?_
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ.toRingHom))) U)
    (φ.symm a)
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply] at hn
  exact congrArg (ConcreteCategory.hom ((pbcCompletedScalar T d').hom.app U))
    (hn.symm.trans (congrArg _ (φ.apply_symm_apply a)))

private theorem smul_congr' {T : Scheme.{u}} {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (N : pbcModules T R) (U : T.ProEtᵒᵖ) {r s : ((adicLisseForget T).obj R).obj.obj U}
    (h : r = s) (x : N.val.obj U) : r • x = s • x := by rw [h]

private def globalSectionsIso (T : Scheme.{u}) (Tm : T.ProEt) :
    integralGlobalSections T d' Tm ≅
      pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
        ModuleCat.restrictScalars φ.symm.toRingHom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.ofHom (X := (integralGlobalSections T d' Tm).obj N)
        (Y := (pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
          ModuleCat.restrictScalars φ.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr' N (op Tm) (completionIso_scalar_apply d d' φ hφ T (op Tm) a).symm x }
      inv := ModuleCat.ofHom (Y := (integralGlobalSections T d' Tm).obj N)
        (X := (pbcRestrict (d.completionIso d' φ hφ T).hom ⋙ integralGlobalSections T d Tm ⋙
          ModuleCat.restrictScalars φ.symm.toRingHom).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            exact smul_congr' N (op Tm) (completionIso_scalar_apply d d' φ hφ T (op Tm) a) x } })
    (fun f ↦ by
      ext x
      rfl)

private def constantModuleTransportIso (T : Scheme.{u}) (Tm : T.ProEt) (hT : IsTerminal Tm) :
    integralConstantModule T d' ≅
      ModuleCat.restrictScalars φ.toRingHom ⋙ integralConstantModule T d ⋙
        pbcRestrict (d.completionIso d' φ hφ T).inv :=
  let adj₁ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv φ).toAdjunction
  let adjG := integralConstantAdjunction T d Tm hT
  let adj₃ := (pbcRestrictEquivalence (d.completionIso d' φ hφ T).symm).toAdjunction
  let adjG' := integralConstantAdjunction T d' Tm hT
  (conjugateIsoEquiv (adj₁.comp (adjG.comp adj₃)) adjG').symm
    (globalSectionsIso d d' φ hφ T Tm).symm

/-- The completed constant realization commutes with the transport of coefficient data. -/
theorem integralConstantDerived_transport (T : Scheme.{u})
    (P : completedConstantDerived (ModuleCat.{u + 1} A')) :
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
    Nonempty ((integralConstantDerived T d').obj P ≅
      (d.transportDerived d' φ hφ T).obj ((integralConstantDerived T d).obj
        ((ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategory.obj P))) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
  let e := constantModuleTransportIso d d' φ hφ T (⊤_ T.ProEt) terminalIsTerminal
  let := (integralConstantModule_exact T d).1
  let := (integralConstantModule_exact T d).2
  let := (integralConstantModule_exact T d').1
  let := (integralConstantModule_exact T d').2
  exact ⟨((Functor.mapDerivedCategoryNatIso e) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm).app P⟩

end ConstantTransport
section PerfectTransport

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (φ : A ≃+* A')

/-- Restriction along a ring isomorphism preserves perfect complexes. -/
theorem isPerfectRingComplex_restrictScalars
    (P : completedConstantDerived (ModuleCat.{u + 1} A'))
    (hP : @DerivedCategory.IsPerfectRingComplex A' _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A')) P) :
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
    letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
    DerivedCategory.IsPerfectRingComplex
      ((ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategory.obj P) := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
  obtain ⟨Q, a, b, ha, hb, hproj, ⟨e⟩⟩ := hP
  let F := ModuleCat.restrictScalars.{u + 1} φ.toRingHom
  refine ⟨(F.mapHomologicalComplex _).obj Q, a, b, ?_, ?_, fun i ↦ ?_,
    ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app Q⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff] at ha ⊢
    exact fun i hi ↦ F.map_isZero (ha i hi)
  · rw [CochainComplex.isStrictlyLE_iff] at hb ⊢
    exact fun i hi ↦ F.map_isZero (hb i hi)
  · obtain ⟨h₁, h₂⟩ := hproj i
    let i₁ : RingHomInvPair (φ.symm.toRingHom : A' →+* A) (φ.toRingHom : A →+* A') :=
      { comp_eq := by ext x; exact φ.apply_symm_apply x
        comp_eq₂ := by ext x; exact φ.symm_apply_apply x }
    let i₂ : RingHomInvPair (φ.toRingHom : A →+* A') (φ.symm.toRingHom : A' →+* A) :=
      { comp_eq := by ext x; exact φ.symm_apply_apply x
        comp_eq₂ := by ext x; exact φ.apply_symm_apply x }
    let e₂ : Q.X i ≃ₛₗ[φ.symm.toRingHom] F.obj (Q.X i) :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ by
          change a • x = φ (φ.symm a) • x
          rw [φ.apply_symm_apply]
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact ⟨Module.Projective.of_equiv e₂, Module.Finite.of_surjective e₂.toLinearMap
      e₂.surjective⟩

end PerfectTransport
section Descent

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

private def pullbackTransportIso {T S : Scheme.{u}} (g : S ⟶ T) (K : PbcCompletedDerived T d) :
    (adicTowerPullback g (pbcAdicCompletion T d')).obj ((d.transportDerived d' φ hφ T).obj K) ≅
      (pbcDerivedRestrict ((adicTowerInverseImage g).map (d.completionIso d' φ hφ T).inv)).obj
        ((adicTowerPullback g (pbcAdicCompletion T d)).obj K) :=
  ((proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion T d') (pbcAdicCompletion T d)
    ((adicTowerInverseImage g).obj (pbcAdicCompletion T d'))
    ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))
    (d.completionIso d' φ hφ T).inv
    ((adicTowerInverseImage g).map (d.completionIso d' φ hφ T).inv)
    (Iso.refl _) (Iso.refl _) (by simp)).app K).symm

/-- Stratified perfect models descend along the transport of coefficient data. -/
theorem AdicCoefficientDatum.isIntegralStratifiedPerfect_of_transport (T : Scheme.{u})
    (K : PbcCompletedDerived T d)
    (hK : IsIntegralStratifiedPerfect T d' ((d.transportDerived d' φ hφ T).obj K)) :
    IsIntegralStratifiedPerfect T d K := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A')
  obtain ⟨s, hs⟩ := hK
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hw⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨P', hP', ⟨j⟩⟩ := hw U f hf
  let P := (ModuleCat.restrictScalars φ.toRingHom).mapDerivedCategory.obj P'
  refine ⟨P, isPerfectRingComplex_restrictScalars φ P' hP', ?_⟩
  let g := s.immersion i
  let e := (adicTowerInverseImage g).mapIso (d.completionIso d' φ hφ T)
  obtain ⟨k⟩ := integralConstantDerived_transport d d' φ hφ T P'
  apply sliceCoefficient_reflects (s.domain i) e U
  let B := (adicLisseForget (s.domain i)).obj ((adicTowerInverseImage g).obj
    (pbcAdicCompletion T d'))
  exact ⟨(sliceRestrictionIso (s.domain i) B U (pullbackTransportIso d d' φ hφ g K)).symm ≪≫ j ≪≫
    sliceRestrictionIso (s.domain i) B U
      ((adicTowerPullback g (pbcAdicCompletion T d')).mapIso k ≪≫
        pullbackTransportIso d d' φ hφ g ((integralConstantDerived T d).obj P))⟩

end Descent

end AlgebraicGeometry.Scheme
