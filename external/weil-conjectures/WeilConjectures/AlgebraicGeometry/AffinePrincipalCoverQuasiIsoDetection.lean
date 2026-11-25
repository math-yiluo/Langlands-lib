/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Detection of quasi-isomorphisms on an affine principal-open cover

Source: Stacks Project, Tag 08EE, final sheafification, and Tags 01HV and 01IB
(blueprint: lem-sc-affine-principal-cover-quasi-iso-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

local instance instAdditiveModuleCatExtendScalars_affinePrincipalCoverQuasiIsoDetection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
private theorem tilde_preservesHomology (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesHomology := by
  let T := tilde.functor R
  let : T.IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  let : T.PreservesMonomorphisms := ⟨by
    intro M N f hf
    let : Mono f := hf
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels T

set_option backward.isDefEq.respectTransparency false in
/-- Localization at one element detects the quasi-isomorphism of the associated
sheaf complexes on its principal open.
Source: Stacks Project, Tags 01HV and 01IB; Tag 08EE, final sheafification step.
(blueprint: lem-sc-affine-principal-cover-quasi-iso-detection).

Proof: The source-library tildePullbackIso identifies tilde followed by pullback
along Spec(A_a) → Spec(A) with scalar extension followed by tilde. Open restriction
is naturally pullback. Transport along X.isoSpec and hT and identify Spec(A_a)
with D(a) by equality of their open-immersion ranges. Associated sheaf preserves
colimits by its affine adjunction and preserves monomorphisms because each
localized stalk map preserves injectivity. Hence it preserves homology. Apply
this to the localized quasi-isomorphism. Restrict back along the inverse of
Spec(A_a) ≅ D(a), then use overFunctorEquiv and reflection of quasi-isomorphisms
by the open-scheme equivalence. The zero element, zero ring and unit cases use
the same localization and equivalence constructions.
No covering or derived-category hypotheses are needed.
-/
private theorem principalOpen_localized_quasiIso
    (X : Scheme.{u}) [IsAffine X]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (a : X.presheaf.obj (.op ⊤))
    (F M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ) (α : F ⟶ M)
    (hα : QuasiIso ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars
        (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away a)))
      (ComplexShape.up ℤ)).map α)) :
    QuasiIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      (X.basicOpen a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  let A := X.presheaf.obj (.op ⊤)
  let S : CommRingCat.{u} := .of (Localization.Away a)
  let φ : A ⟶ S := CommRingCat.ofHom (algebraMap A (Localization.Away a))
  let j := Spec.map φ
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization a
  let p := j ≫ X.isoSpec.inv
  have hp : Set.range p = Set.range (X.basicOpen a).ι := by
    change p.opensRange.carrier = (X.basicOpen a).ι.opensRange.carrier
    congr 1
    rw [Hom.opensRange_comp, Hom.opensRange_localizationAway, Opens.opensRange_ι]
    apply X.isoSpec.hom.image_injective
    dsimp only
    simp only [← Hom.comp_image, X.isoSpec.inv_hom_id]
    rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine X a,
      Hom.image_preimage_eq_opensRange_inf, Hom.opensRange_of_isIso, top_inf_eq]
    exact Hom.id_image _
  obtain ⟨e, heinv⟩ : ∃ e : Spec S ≅ (X.basicOpen a).toScheme,
      e.inv ≫ p = (X.basicOpen a).ι :=
    ⟨IsOpenImmersion.isoOfRangeEq p (X.basicOpen a).ι hp,
      IsOpenImmersion.isoOfRangeEq_inv_fac p (X.basicOpen a).ι hp⟩
  obtain ⟨t⟩ := hT
  have ep : T ⋙ Modules.restrictFunctor p ≅ ModuleCat.extendScalars φ.hom ⋙
      tilde.functor S :=
    Functor.isoWhiskerRight t _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Modules.restrictFunctorComp p X.isoSpec.hom).symm ≪≫
      Functor.isoWhiskerLeft _ (Modules.restrictFunctorCongr (by simp [p])) ≪≫
      Functor.isoWhiskerLeft _ (Modules.restrictFunctorIsoPullback j) ≪≫
      Modules.tildePullbackIso φ
  have : (tilde.functor S).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := S) f g
  have : (Modules.restrictFunctor p).Additive := ⟨by intros; rfl⟩
  have : (tilde.functor S).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : (tilde.functor S).PreservesHomology := tilde_preservesHomology S
  have : QuasiIso ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.map α) := hα
  have hloc : QuasiIso (((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α) := by
    exact HomologicalComplex.quasiIso_map_of_preservesHomology
      (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
       (ComplexShape.up ℤ)).map α) (tilde.functor S)
  have ec := NatIso.mapHomologicalComplex ep (ComplexShape.up ℤ)
  have htp : QuasiIso (((T ⋙ Modules.restrictFunctor p).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ec.app F) (ec.app M) (ec.hom.naturality α).symm)).mpr hloc
  have htp' : QuasiIso (((Modules.restrictFunctor p).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
    htp
  have : (Modules.restrictFunctor (X.basicOpen a).ι).Additive := ⟨by intros; rfl⟩
  have : (Modules.overEquiv (X.basicOpen a)).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have hpull : QuasiIso (((Modules.restrictFunctor e.inv).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((Modules.restrictFunctor p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have eqp := (Modules.restrictFunctorComp e.inv p).symm ≪≫
    Modules.restrictFunctorCongr heinv
  have eqpc := NatIso.mapHomologicalComplex eqp (ComplexShape.up ℤ)
  have hopen : QuasiIso (((Modules.restrictFunctor (X.basicOpen a).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (eqpc.app _) (eqpc.app _) (eqpc.hom.naturality _).symm)).mp hpull
  have eqo := NatIso.mapHomologicalComplex (Modules.overFunctorEquiv (X.basicOpen a))
    (ComplexShape.up ℤ)
  have hover : QuasiIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      (X.basicOpen a) ⋙ (Modules.overEquiv (X.basicOpen a)).functor).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (eqo.app _) (eqo.app _) (eqo.hom.naturality _).symm)).mpr hopen
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (Modules.overEquiv (X.basicOpen a)).functor).mp hover

private theorem isIso_over_of_cover (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    {I : Type*} (V : I → TopologicalSpace.Opens X) (hsub : ∀ i, V i ≤ U)
    (hcover : ∀ x : X, x ∈ U → ∃ i, x ∈ V i)
    {M N : SheafOfModules.{u} (moduleRings X)} (β : M ⟶ N)
    (h : ∀ i, IsIso (β.over (V i))) : IsIso (β.over U) := by
  let W : I → Over U := fun i ↦ Over.mk (homOfLE (hsub i))
  have hW : ((Opens.grothendieckTopology X).over U).CoversTop W := by
    intro Z
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    obtain ⟨i, hi⟩ := hcover x (Z.hom.le hx)
    refine ⟨Z.left ⊓ V i, homOfLE inf_le_left, ?_, ⟨hx, hi⟩⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨i, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
  have : IsIso ((SheafOfModules.toSheaf ((moduleRings X).over U)).map (β.over U)) := by
    apply Sheaf.isIso_of_coversTop hW
    intro i
    have := h i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro Z
    exact (NatTrans.isIso_iff_isIso_app
      ((SheafOfModules.toSheaf ((moduleRings X).over (V i))).map
        (β.over (V i))).hom).mp inferInstance
      (.op (Over.mk Z.unop.hom.left))
  exact isIso_of_reflects_iso (β.over U) (SheafOfModules.toSheaf _)

private theorem quasiIso_over_of_cover (X : RingedSpace.{u})
    (U : TopologicalSpace.Opens X) {I : Type*} (V : I → TopologicalSpace.Opens X)
    (hsub : ∀ i, V i ≤ U) (hcover : ∀ x : X, x ∈ U → ∃ i, x ∈ V i)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ} (β : K ⟶ L)
    (h : ∀ i, QuasiIso (((SheafOfModules.overFunctor.{u} (moduleRings X)
      (V i)).mapHomologicalComplex (ComplexShape.up ℤ)).map β)) :
    QuasiIso (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map β) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map β
  have hiso : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X) U).map
      (ShortComplex.homologyMap φ)) := by
    apply isIso_over_of_cover X U V hsub hcover
    intro i
    let R := SheafOfModules.overFunctor.{u} (moduleRings X) (V i)
    have hφ : ShortComplex.QuasiIso (R.mapShortComplex.map φ) := by
      have := h i
      exact (quasiIsoAt_iff ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map β) n).mp
        inferInstance
    have : IsIso (ShortComplex.homologyMap (R.mapShortComplex.map φ)) :=
      (ShortComplex.quasiIso_iff _).mp hφ
    have he := ShortComplex.mapHomologyIso_inv_naturality φ R
    have : IsIso (R.map (ShortComplex.homologyMap φ) ≫
        ((L.sc n).mapHomologyIso R).inv) := by
      rw [he]
      infer_instance
    exact (isIso_comp_right_iff _ ((L.sc n).mapHomologyIso R).inv).mp inferInstance
  let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
  have he := ShortComplex.mapHomologyIso_inv_naturality φ R
  have : IsIso (((K.sc n).mapHomologyIso R).inv ≫
      ShortComplex.homologyMap (R.mapShortComplex.map φ)) := by
    rw [← he]
    infer_instance
  exact (isIso_comp_left_iff ((K.sc n).mapHomologyIso R).inv
    (ShortComplex.homologyMap (R.mapShortComplex.map φ))).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Localized quasi-isomorphisms on a principal-open cover give an invertible
map on the open derived category. No pseudo-coherence or boundedness is required.
Source: Stacks Project, Tag 08EE, final sheafification step, and Tags 01HV and 01IB
(blueprint: lem-sc-affine-principal-cover-quasi-iso-detection).

Proof: Tilde preserves colimits by its adjunction and monomorphisms by
injectivity of localized stalk maps, hence preserves homology. The proved
source-library tildePullbackIso and the open restriction/pullback comparison
identify tilde restricted to Spec(A_f) with tilde of scalar extension.
Transport along X.isoSpec and hT, and identify Spec(A_f) with D(f) by equality
of open-immersion ranges. This gives a quasi-isomorphism on each D(f).
The D(f), with their inclusions into U, cover the terminal object of the
localized open site over U. Apply Mathlib's sheaf local-isomorphism criterion
to the underlying abelian sheaves. Exact restriction commutes with homology,
so the restricted complex map is a quasi-isomorphism. The equivalence with
modules on U preserves this assertion. Apply Q, which inverts quasi-isomorphisms,
and conjugate by mapDerivedCategoryFactors to obtain the required map.
For an empty cover the covering hypothesis forces U to be empty; the same local
criterion applies vacuously. No unit-ideal hypothesis on the family is needed.
-/
theorem affine_principal_cover_quasiIso_detection
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (r : ℕ) (f : Fin r → X.presheaf.obj (.op ⊤))
    (hsub : ∀ j, X.basicOpen (f j) ≤ U)
    (hcover : ∀ x : X, x ∈ U → ∃ j, x ∈ X.basicOpen (f j))
    (F M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ) (α : F ⟶ M)
    (hα : ∀ j : Fin r, QuasiIso ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars
        (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away (f j))))
      (ComplexShape.up ℤ)).map α)) :
    IsIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.map
      (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α))) :=
  by
    let β := (T.mapHomologicalComplex (ComplexShape.up ℤ)).map α
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
    have hβ : QuasiIso ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map β) :=
      quasiIso_over_of_cover X.toRingedSpace U (fun j ↦ X.basicOpen (f j)) hsub hcover β
        (fun j ↦ principalOpen_localized_quasiIso X T hT (f j) F M α (hα j))
    have hRE : QuasiIso (((R ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ)).map β) := by
      exact HomologicalComplex.quasiIso_map_of_preservesHomology
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map β) E
    have : IsIso (DerivedCategory.Q.map
        (((R ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ)).map β)) := inferInstance
    have he := (R ⋙ E).mapDerivedCategoryFactors_hom_naturality β
    have : IsIso ((R ⋙ E).mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
        (R ⋙ E).mapDerivedCategoryFactors.hom.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
      rw [he]
      infer_instance
    exact (isIso_comp_right_iff _
      ((R ⋙ E).mapDerivedCategoryFactors.hom.app
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).mp inferInstance

end AlgebraicGeometry.Scheme
