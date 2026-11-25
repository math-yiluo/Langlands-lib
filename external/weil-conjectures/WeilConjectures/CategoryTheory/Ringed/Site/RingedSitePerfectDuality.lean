/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteStrictPerfectHom
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Perfect duality on a small ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ,
lemma-dual-perfect-complex (blueprint: lem-sfb-ringed-site-perfect-duality).
The canonical maps are explicit transposes of evaluation in a normalized K-flat
closed tensor-Hom presentation, rather than unspecified isomorphic morphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private instance (priority := 10) isIso_prod_mkHom
    {A B : Type*} [Category A] [Category B]
    {X Y : A} {U V : B} (f : X ⟶ Y) (g : U ⟶ V) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) := (isIso_prod_iff A B).mpr ⟨inferInstance, inferInstance⟩

private theorem isIso_of_comp_eq
    {A : Type*} [Category A] {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (hg : IsIso g) (hh : IsIso h) : IsIso f := by
  have := hg
  have : IsIso (f ≫ g) := e.symm ▸ hh
  exact IsIso.of_isIso_comp_right f g

private theorem isIso_right_of_comp_eq
    {A : Type*} [Category A] {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (hf : IsIso f) (hh : IsIso h) : IsIso g := by
  have := hf
  have : IsIso (f ≫ g) := e.symm ▸ hh
  exact IsIso.of_isIso_comp_left f g

private theorem map_to_kInjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K I : CochainComplex A ℤ) [I.IsKInjective]
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) :
    ∃ g : K ⟶ I, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj K) I).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso A).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app K)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem derived_iso_of_complex_reflection
    {Dmod : Type*} [Category Dmod] [Abelian Dmod] [HasDerivedCategory Dmod]
    {ι : Type*} {Dslice : ι → Type*} [∀ i, Category (Dslice i)] [∀ i, Abelian (Dslice i)]
    [∀ i, HasDerivedCategory (Dslice i)]
    (F : ∀ i, DerivedCategory Dmod ⥤ DerivedCategory (Dslice i))
    (G : ∀ i, CochainComplex Dmod ℤ ⥤ CochainComplex (Dslice i) ℤ)
    (e : ∀ i, DerivedCategory.Q ⋙ F i ≅ G i ⋙ DerivedCategory.Q)
    (h : ∀ {K L : CochainComplex Dmod ℤ} (g : K ⟶ L),
      (∀ i, QuasiIso ((G i).map g)) → QuasiIso g)
    {P Q : DerivedCategory Dmod} (f : P ⟶ Q) (K I : CochainComplex Dmod ℤ) [I.IsKInjective]
    (p : DerivedCategory.Q.obj K ≅ P) (q : Q ≅ DerivedCategory.Q.obj I)
    (hf : ∀ i, IsIso ((F i).map f)) : IsIso f :=
  (map_to_kInjective K I (p.hom ≫ f ≫ q.hom)).elim fun g hg ↦
    have hrestr (i : ι) : QuasiIso ((G i).map g) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (Dslice i) ((G i).map g)).mp
        (isIso_right_of_comp_eq ((e i).hom.naturality g).symm
          (NatIso.hom_app_isIso (e i) K)
          (IsIso.comp_isIso'
            (show IsIso ((F i).map (DerivedCategory.Q.map g)) from by
              simpa only [hg, Functor.map_comp] using
                IsIso.comp_isIso' (Functor.map_isIso (F i) p.hom)
                  (IsIso.comp_isIso' (hf i) (Functor.map_isIso (F i) q.hom)))
            (NatIso.hom_app_isIso (e i) I)))
    have hqg : QuasiIso g := h g hrestr
    have hh : IsIso (p.hom ≫ f ≫ q.hom) :=
      hg ▸ (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).mpr hqg
    isIso_of_comp_eq (show f ≫ q.hom = f ≫ q.hom from rfl) q.isIso_hom
      (isIso_right_of_comp_eq
        (show p.hom ≫ (f ≫ q.hom) = p.hom ≫ f ≫ q.hom from rfl) p.isIso_hom hh)

section Transport
variable {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
  (T : WeilConjectures.CoefficientClosedStructure H)
  (s : @SymmetricCategory D _ T.monoidal) (O : D) (u : T.monoidal.tensorUnit ≅ O)

private theorem bidual_transport {P P' : D} (p : P ≅ P')
    (h : IsIso (ringedSiteBidual T s O P')) : IsIso (ringedSiteBidual T s O P) := by
  have := h
  have hn := ringedSiteBidual_naturality T s O p.hom
  have : IsIso (p.hom ≫ ringedSiteBidual T s O P') := by infer_instance
  exact isIso_of_comp_eq hn.symm inferInstance inferInstance

private theorem evaluation_transport_source {P P' : D} (p : P ≅ P') (N : D)
    (h : IsIso (ringedSiteDualEvaluation T O u P' N)) :
    IsIso (ringedSiteDualEvaluation T O u P N) := by
  have := h
  have hn := ringedSiteDualEvaluation_source_naturality T O u p.hom N
  have : IsIso (ringedSiteDualEvaluation T O u P' N ≫
      H.map (Prod.mkHom p.hom.op (𝟙 N))) := by infer_instance
  exact isIso_right_of_comp_eq hn inferInstance inferInstance

private theorem evaluation_transport_target (P : D) {N N' : D} (q : N ≅ N')
    (h : IsIso (ringedSiteDualEvaluation T O u P N)) :
    IsIso (ringedSiteDualEvaluation T O u P N') := by
  have := h
  have hn := ringedSiteDualEvaluation_naturality T O u P q.hom
  have : IsIso (ringedSiteDualEvaluation T O u P N ≫
      H.map (Prod.mkHom (𝟙 (op P)) q.hom)) := by infer_instance
  exact isIso_right_of_comp_eq hn inferInstance inferInstance
private theorem evaluation_left_isIso (P N : D)
    (h : IsIso (ringedSiteDualEvaluation T O u P N)) :
    IsIso (ringedSiteDualEvaluationLeft T s O u P N) := by
  unfold ringedSiteDualEvaluationLeft
  exact IsIso.comp_isIso' (s.braiding (H.obj (op P, O)) N).isIso_hom h

end Transport

@[irreducible] private noncomputable def restrictScalarsSelfIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) :
    SheafOfModules.restrictScalars.{max c v r} (𝟙 S) ≅
      𝟭 (SheafOfModules.{max c v r} S) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact { hom := { val := 𝟙 _ }, inv := { val := 𝟙 _ } }
  · intro M N f
    ext V x
    rfl

@[irreducible] private noncomputable def restrictionComplexIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (U : C) :
    ringedSiteDualityRestrictionComplex.{c, v, r} J R U ≅
      (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex
        (.up ℤ) := by
  let F := SheafOfModules.localizedSystemRestriction.{c, v, r} R U
  exact NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft F
    (restrictScalarsSelfIso _) ≪≫ Functor.rightUnitor F) (.up ℤ)

private theorem sheafOver_map_isIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{r}) (U : C)
    {M N : SheafOfModules.{max c v r} S} (f : M ⟶ N)
    [IsIso ((SheafOfModules.overFunctor S U).map f)] :
    IsIso ((J.overPullback AddCommGrpCat.{max c v r} U).map
      ((SheafOfModules.toSheaf S).map f)) := by
  change IsIso ((SheafOfModules.toSheaf (S.over U)).map
    ((SheafOfModules.overFunctor S U).map f))
  infer_instance

section LocalModels

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

set_option hygiene false in
set_option quotPrecheck false in
local notation "S" => ((sheafCompose J
  (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => SheafOfModules.{max c v r} S
set_option hygiene false in
set_option quotPrecheck false in
local notation "AU" U => SheafOfModules.{max c v r} ((S).over U)

variable [HasDerivedCategory.{w} A] [∀ U : C, HasDerivedCategory.{w'} (AU U)]
  (F : ∀ U : C, DerivedCategory A ⥤ DerivedCategory (AU U))

omit [∀ U : C, HasDerivedCategory.{w'} (AU U)]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem exists_kInjective_model (P : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ Nonempty (P ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨K, ⟨p⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := A)) P
  obtain ⟨I₀, η₀, hI₀⟩ :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c,
      v, r} J R).2.2
  have : QuasiIso (η₀.app K) := (hI₀ K).1
  exact ⟨I₀.obj K, (hI₀ K).2.1, ⟨p.symm ≪≫ asIso (DerivedCategory.Q.map (η₀.app K))⟩⟩

private theorem perfect_local_models
    (e : ∀ U : C, DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.overFunctor.{max c v r} S U).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    (P : DerivedCategory A) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P ↔
    ∀ V : C, ∃ T : Sieve V, T ∈ J V ∧
      ∀ (U : C) (f : U ⟶ V), T f →
        ∃ E : CochainComplex (AU U) ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
          Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) ∧
          Nonempty ((F U).obj P ≅ DerivedCategory.Q.obj E) := by
  classical
  constructor
  · rintro ⟨K, hK, ⟨p⟩⟩ V
    obtain ⟨T, hT, h⟩ := hK V
    refine ⟨T, hT, ?_⟩
    intro U f hf
    obtain ⟨E, hb, hp, α, hα⟩ := h U f hf
    have := hα
    exact ⟨E, hb, hp, ⟨(F U).mapIso p ≪≫ (e U).app K ≪≫ (asIso
      (DerivedCategory.Q.map α)).symm⟩⟩
  · intro h
    obtain ⟨I, hI, ⟨p⟩⟩ := exists_kInjective_model.{c, v, r, w} J R P
    have := hI
    refine ⟨I, ?_, ⟨p⟩⟩
    intro V
    obtain ⟨T, hT, h⟩ := h V
    refine ⟨T, hT, ?_⟩
    intro U f hf
    obtain ⟨E, hb, hp, ⟨q⟩⟩ := h U f hf
    let G := SheafOfModules.localizedSystemRestriction.{c, v, r} R U
    have : G.PreservesKInjectiveComplexes :=
      (SheafOfModules.localizedSystemAdjunction.{c, v, r} R U).preservesKInjectiveComplexes
    have : CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I) :=
      Functor.PreservesKInjectiveComplexes.isKInjective_map I
    let q' := q.symm ≪≫ (F U).mapIso p ≪≫ (e U).app I
    obtain ⟨α, hα⟩ := map_to_kInjective E ((G.mapHomologicalComplex (.up ℤ)).obj I) q'.hom
    have : IsIso (DerivedCategory.Q.map α) := by rw [hα]; infer_instance
    exact ⟨E, hb, hp, α, (DerivedCategory.isIso_Q_map_iff_quasiIso _ α).mp inferInstance⟩

omit [HasDerivedCategory.{w} A] [∀ U : C, HasDerivedCategory.{w'} (AU U)] in
private theorem quasiIso_local {ι : Type*} (Y : ι → C) (hY : J.CoversTop Y)
    {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((SheafOfModules.localizedSystemRestriction.{c, v, r} R
      (Y i)).mapHomologicalComplex (.up ℤ)).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  let H := HomologicalComplex.shortComplexFunctor A (.up ℤ) n
  have : IsIso ((SheafOfModules.toSheaf S).map (ShortComplex.homologyMap (H.map f))) := by
    apply Sheaf.isIso_of_coversTop hY
    intro i
    let G := SheafOfModules.localizedSystemRestriction.{c, v, r} R (Y i)
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f) := hf i
    have hsc : ShortComplex.QuasiIso (G.mapShortComplex.map (H.map f)) :=
      (quasiIsoAt_iff ((G.mapHomologicalComplex (.up ℤ)).map f) n).mp inferInstance
    have hn := ShortComplex.mapHomologyIso_hom_naturality (H.map f) G
    have : IsIso (((H.obj K).mapHomologyIso G).hom ≫
        G.map (ShortComplex.homologyMap (H.map f))) := by
      rw [← hn]
      exact IsIso.comp_isIso' hsc.isIso' ((H.obj L).mapHomologyIso G).isIso_hom
    have : IsIso (G.map (ShortComplex.homologyMap (H.map f))) :=
      IsIso.of_isIso_comp_left ((H.obj K).mapHomologyIso G).hom _
    exact sheafOver_map_isIso S (Y i)
      (ShortComplex.homologyMap (H.map f))
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf S)

private theorem derived_iso_local
    (e : ∀ U : C, DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.overFunctor.{max c v r} S U).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    {ι : Type*} (Y : ι → C) (hY : J.CoversTop Y)
    {P Q : DerivedCategory A} (f : P ⟶ Q)
    (hf : ∀ i, IsIso ((F (Y i)).map f)) : IsIso f := by
  classical
  obtain ⟨K, ⟨p⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := A)) P
  obtain ⟨I, hI, ⟨q⟩⟩ := exists_kInjective_model.{c, v, r, w} J R Q
  have := hI
  exact derived_iso_of_complex_reflection (Dmod := A) (Dslice := fun i ↦ AU (Y i))
    (fun i ↦ F (Y i))
    (fun i ↦ (SheafOfModules.localizedSystemRestriction.{c, v, r} R
      (Y i)).mapHomologicalComplex (.up ℤ)) (fun i ↦ e (Y i))
    (fun {K L} g hg ↦ quasiIso_local.{c, v, r} J R Y hY g hg) f K I p q hf

end LocalModels

private lemma isDualizable_finite_power
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∏ᶜ fun _ : Fin n ↦ U) := by
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∏ᶜ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∏ᶜ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift fun i : Fin n ↦ Pi.π _ i.succ)
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

private theorem strict_kflat
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (E : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) E := by
  let A := SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨a, b, hb⟩ := hb
  have : E.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff E b).mpr (fun n hn ↦ hb n (Or.inr hn))
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R E b
  intro n
  have hd : IsDualizable (E.X n) := IsDualizable.of_retract
    ⟨pE.i n, pE.p n, pE.splitting n⟩
    (isDualizable_finite_power _ isDualizable_unit (pE.N n))
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (E.X n)).symm hd.flat.2

private theorem strict_bidual
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    IsIso (ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R)
      (DerivedCategory.Q.obj E)) := by
  obtain ⟨_, _, h, hD, hβ, _⟩ := ringedSiteStrictPerfectHom.{c, v, r, w} J R E hE pE
  have := hβ
  have hn := ringedSiteBidual_normalization.{c, v, r, w} J R M E
    (h (ringedSiteDualityUnitComplex.{c, v, r} J R)) hD
  have hh : IsIso (DerivedCategory.Q.map (ringedSiteOrdinaryBidual.{c, v, r, w} J R E) ≫
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R _ _ hD).hom) := by infer_instance
  have hg : IsIso ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R)
          (h (ringedSiteDualityUnitComplex.{c, v, r} J R))).hom.op
        (𝟙 (ringedSiteDualityUnit.{c, v, r, w} J R)))) :=
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso
      ((ringedSiteOrdinaryHomIso.{c, v, r, w} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R)
          (h (ringedSiteDualityUnitComplex.{c, v, r} J R))).op.prod
        (Iso.refl _))).isIso_hom
  exact isIso_of_comp_eq hn hg hh

private theorem exists_kFlat_model
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (N : DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) :
    ∃ F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
        (J := J) (R := R) F ∧
        Nonempty (DerivedCategory.Q.obj F ≅ N) := by
  obtain ⟨K, ⟨q⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q N
  obtain ⟨F, f, hF, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  have := hf
  exact ⟨F, hF, ⟨asIso (DerivedCategory.Q.map f) ≪≫ q⟩⟩

private theorem strict_evaluation
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E)
    (N : DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) :
    IsIso (ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
      (DerivedCategory.Q.obj E) N) := by
  classical
  obtain ⟨hbD, ⟨pD⟩, h, _, _, hε⟩ :=
    ringedSiteStrictPerfectHom.{c, v, r, w} J R E hE pE
  have hD := strict_kflat.{c, v, r} J R _ hbD pD
  obtain ⟨F, hF, ⟨q⟩⟩ := exists_kFlat_model.{c, v, r, w} J R N
  apply evaluation_transport_target M.closed (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
    (DerivedCategory.Q.obj E) q
  have := hε F
  have hn := ringedSiteDualEvaluation_normalization.{c, v, r, w} J R M E F hF hD
    (h (ringedSiteDualityUnitComplex.{c, v, r} J R)) (h F)
  have hr : IsIso (DerivedCategory.Q.map
      (ringedSiteOrdinaryEvaluation.{c, v, r, w} J R E F) ≫
        (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E F (h F)).hom) :=
    IsIso.comp_isIso'
      (Functor.map_isIso DerivedCategory.Q
        (ringedSiteOrdinaryEvaluation.{c, v, r, w} J R E F))
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E F (h F)).isIso_hom
  have hs := isIso_right_of_comp_eq hn (M.models.iso J R M.closed F _ hF hD).isIso_hom hr
  exact isIso_right_of_comp_eq rfl
    (Functor.map_isIso M.closed.tensor (Prod.mkHom (𝟙 _)
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R)
        (h (ringedSiteDualityUnitComplex.{c, v, r} J R))).hom)) hs

section ComparisonData
variable {D D' B B' : Type*} [Category D] [Category D'] [Category B] [Category B']
  {H : Dᵒᵖ × D ⥤ D} {H' : D'ᵒᵖ × D' ⥤ D'}

/-- Normalized restriction comparisons, with the categories kept abstract. -/
private structure DualityRestrictionData
    (T : WeilConjectures.CoefficientClosedStructure H)
    (s : @SymmetricCategory D _ T.monoidal) (O : D) (u : T.monoidal.tensorUnit ≅ O)
    (T' : WeilConjectures.CoefficientClosedStructure H')
    (s' : @SymmetricCategory D' _ T'.monoidal) (O' : D')
    (u' : T'.monoidal.tensorUnit ≅ O') (G : B ⥤ B') (Q : B ⥤ D) (Q' : B' ⥤ D') where
  F : D ⥤ D'
  e : Q ⋙ F ≅ G ⋙ Q'
  t : T.tensor ⋙ F ≅ (F.prod F) ⋙ T'.tensor
  h : H ⋙ F ≅ (F.op.prod F) ⋙ H'
  o : F.obj O ≅ O'
  bidual (P : D) :
    F.map (ringedSiteBidual T s O P) ≫
      h.hom.app (op (H.obj (op P, O)), O) ≫
      H'.map (Prod.mkHom (h.inv.app (op P, O)).op o.hom) ≫
      H'.map (Prod.mkHom (H'.map (Prod.mkHom (𝟙 (op (F.obj P))) o.inv)).op
        (𝟙 O')) = ringedSiteBidual T' s' O' (F.obj P)
  evaluation (P N : D) :
    F.map (ringedSiteDualEvaluation T O u P N) ≫ h.hom.app (op P, N) =
      t.hom.app (N, H.obj (op P, O)) ≫
      T'.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app (op P, O))) ≫
      T'.tensor.map (Prod.mkHom (𝟙 _)
        (H'.map (Prod.mkHom (𝟙 (op (F.obj P))) o.hom))) ≫
      ringedSiteDualEvaluation T' O' u' (F.obj P) (F.obj N)

private theorem DualityRestrictionData.bidual_isIso
    {T : WeilConjectures.CoefficientClosedStructure H}
    {s : @SymmetricCategory D _ T.monoidal} {O : D} {u : T.monoidal.tensorUnit ≅ O}
    {T' : WeilConjectures.CoefficientClosedStructure H'}
    {s' : @SymmetricCategory D' _ T'.monoidal} {O' : D'}
    {u' : T'.monoidal.tensorUnit ≅ O'} {G : B ⥤ B'} {Q : B ⥤ D} {Q' : B' ⥤ D'}
    (d : DualityRestrictionData T s O u T' s' O' u' G Q Q') (P : D)
    (h : IsIso (ringedSiteBidual T' s' O' (d.F.obj P))) :
    IsIso (d.F.map (ringedSiteBidual T s O P)) := by
  have := h
  exact isIso_of_comp_eq (d.bidual P) inferInstance h

private theorem DualityRestrictionData.evaluation_isIso
    {T : WeilConjectures.CoefficientClosedStructure H}
    {s : @SymmetricCategory D _ T.monoidal} {O : D} {u : T.monoidal.tensorUnit ≅ O}
    {T' : WeilConjectures.CoefficientClosedStructure H'}
    {s' : @SymmetricCategory D' _ T'.monoidal} {O' : D'}
    {u' : T'.monoidal.tensorUnit ≅ O'} {G : B ⥤ B'} {Q : B ⥤ D} {Q' : B' ⥤ D'}
    (d : DualityRestrictionData T s O u T' s' O' u' G Q Q') (P N : D)
    (h : IsIso (ringedSiteDualEvaluation T' O' u' (d.F.obj P) (d.F.obj N))) :
    IsIso (d.F.map (ringedSiteDualEvaluation T O u P N)) := by
  have := h
  have hi : IsIso (d.t.hom.app (N, H.obj (op P, O)) ≫
      T'.tensor.map (Prod.mkHom (𝟙 _) (d.h.hom.app (op P, O))) ≫
      T'.tensor.map (Prod.mkHom (𝟙 _)
        (H'.map (Prod.mkHom (𝟙 (op (d.F.obj P))) d.o.hom))) ≫
      ringedSiteDualEvaluation T' O' u' (d.F.obj P) (d.F.obj N)) :=
    IsIso.comp_isIso' (NatIso.hom_app_isIso d.t _)
      (IsIso.comp_isIso'
        (T'.tensor.mapIso ((Iso.refl _).prod (d.h.app (op P, O)))).isIso_hom
        (IsIso.comp_isIso'
          (T'.tensor.mapIso ((Iso.refl _).prod
            (H'.mapIso ((Iso.refl _).prod d.o)))).isIso_hom h))
  rw [← d.evaluation P N] at hi
  have := hi
  exact IsIso.of_isIso_comp_right _ (d.h.hom.app (op P, N))

end ComparisonData

section RestrictionData

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (SheafOfModules.{max c v r} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U)))]

private abbrev RestrictionData (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U)) :=
  DualityRestrictionData M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R)
    M.unitIso MU.closed MU.symmetric
    (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U)) MU.unitIso
    (ringedSiteDualityRestrictionComplex.{c, v, r} J R U)
    DerivedCategory.Q DerivedCategory.Q

private theorem restrictionData_nonempty (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U)) :
    Nonempty (RestrictionData J R U M MU) := by
  obtain ⟨F, ⟨e⟩, t, h, o, _, hb, he⟩ :=
    ringedSiteDualityMaps_restriction.{c, v, r, w, w'} J R M U MU
  exact ⟨{ F := F, e := e, t := t, h := h, o := o, bidual := hb, evaluation := he }⟩

end RestrictionData

set_option maxHeartbeats 60000 in
-- Bound normalization-instance searches during elaboration and linting.
/-- Perfect-complex duality for the specified canonical maps.
The existential is a normalized presentation of the already recorded derived
tensor and Hom: its transposition, unit, associator and symmetry are fixed on
ordinary representatives. It is not a choice of an arbitrary bidual morphism or
an arbitrary isomorphism. The last clause says the actual canonical evaluation
natural transformation is invertible, in the tensor order of the node.
Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-ringed-site-perfect-duality).

Proof:
1. Use lem-sfb-ringed-site-duality-maps for the normalized canonical maps and
   lem-weil-pbc-ringed-internal-hom-exact-restriction to restrict them. On covering
   slice sites choose the bounded finite-free-summand representatives E of hP.
2. Split each E^i into a finite free sheaf. Its dual is a finite free summand;
   the dual-basis formulas invert termwise biduality and tensor-Hom evaluation.
   Hom out of each term, and tensor with it or its dual, are exact retracts of
   finite direct sum, using lem-sc-finite-free-internal-hom-exact. Thus the terms
   and their duals are flat (def-pc-flat-sheaf-modules).
3. Apply lem-pc-bounded-exact-term-hom-quasi-iso to the K-injective augmentation
   of an arbitrary complex F. Ordinary Hom(E,F) computes derived Hom, naturally
   in F; boundedness of E makes each Hom product finite.
4. For F=O[0] obtain the dual complex D, with D^q=(E^(-q))^dual and differential
   (-1)^(q+1) times the dual differential. It is supported in [-b,-a] and its
   terms are finite free summands, so it is strictly perfect on this slice.
5. The two Hom comparisons identify the canonical bidual map with
   x ↦ (phi ↦ (-1)^i phi(x)). The double-dual differential is minus the double
   dual of d_E. These signs give a chain map, termwise invertible by step 2.
6. Choose a flat-term K-flat representative F of N by lem-pc-kflat-resolution.
   D is K-flat by lem-pc-bounded-above-flat-kflat-site; the comparison in
   lem-weil-pbc-site-derived-tensor-descent computes tensor by Tot(F tensor D).
7. Under step 3 and this comparison, canonical evaluation has summand map
   y tensor phi ↦ (x ↦ y phi(x)), with no sign. It is termwise invertible by
   step 2, and the tensor differential agrees with the Hom differential. The
   bounded dual makes each degree sum finite even when N is unbounded. The
   normalized Koszul symmetry gives precisely the order dual tensor N here.
8. Exact slice restriction commutes with cohomology. Represent any derived map
   by an actual map to a K-injective complex (lem-weil-pbc-kinjective-hom-derived).
   The sheaf-cover criterion lem-sfb-sheaf-cover-local-isomorphism makes its
   cohomology maps invertible globally if they are so on this covering family.
   Apply this to the canonical maps of steps 5 and 7.
9. Choose one global K-injective representative of the dual. Its restrictions
   remain K-injective by lem-pur-kinjective-restrict-localized. Lift the local
   isomorphisms from D to actual quasi-isomorphisms using
   lem-weil-pbc-kinjective-hom-derived; these are exactly the local perfectness
   condition. No global bound on P or its dual is imposed.
10. The comparison is natural by lem-sfb-ringed-site-duality-maps and symmetry.
    Since each component is invertible by step 8, its component inverses are
    natural too, proving IsIso of this specified natural transformation. -/
theorem ringedSitePerfectDuality
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (P : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P) :
    ∃ M : RingedSiteDualityModel.{c, v, r, w} J R,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, ringedSiteDualityUnit.{c, v, r, w} J R)) ∧
      IsIso (ringedSiteBidual M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) P) ∧
      IsIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P) := by
  classical
  let AU (U : C) := SheafOfModules.{max c v r} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U))
  obtain ⟨sliceDerived⟩ : Nonempty (∀ U : C, HasDerivedCategory.{max c v r + 1}
      (SheafOfModules.{max c v r} (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))) :=
    ⟨fun U ↦ HasDerivedCategory.standard _⟩
  let : ∀ U : C, HasDerivedCategory.{max c v r + 1}
      (SheafOfModules.{max c v r} (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) := sliceDerived
  let (U : C) : HasDerivedCategory.{max c v r + 1} (AU U) := sliceDerived U
  obtain ⟨M⟩ := ringedSiteDualityMaps_exists.{c, v, r, w} J R
  obtain ⟨MU⟩ : Nonempty (∀ U : C,
      RingedSiteDualityModel.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)) :=
    ⟨fun U ↦ (ringedSiteDualityMaps_exists.{max c v, v, r, max c v r + 1}
      (J.over U) (R.over U)).some⟩
  obtain ⟨d⟩ : Nonempty (∀ U : C,
      RestrictionData.{c, v, r, w, max c v r + 1} J R U M (MU U)) :=
    ⟨fun U ↦ (restrictionData_nonempty.{c, v, r, w, max c v r + 1}
      J R U M (MU U)).some⟩
  let F (U : C) := (d U).F
  let h (U : C) := (d U).h
  let o (U : C) := (d U).o
  have e (U : C) : DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
    (d U).e ≪≫ Functor.isoWhiskerRight
      (restrictionComplexIso.{c, v, r, w} J R U) DerivedCategory.Q
  have hmodels := (perfect_local_models.{c, v, r, w, max c v r + 1} J R F e P).mp hP
  let LP (U : C) : Prop := ∃ E : CochainComplex (AU U) ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) ∧
    Nonempty ((F U).obj P ≅ DerivedCategory.Q.obj E)
  let Y : { U : C // LP U } → C := Subtype.val
  have hY : J.CoversTop Y := by
    intro V
    obtain ⟨T, hT, hm⟩ := hmodels V
    apply J.superset_covering _ hT
    intro U f hf
    exact ⟨⟨U, hm U f hf⟩, ⟨𝟙 U⟩⟩
  refine ⟨M, ?_, ?_, ?_⟩
  · apply (perfect_local_models.{c, v, r, w, max c v r + 1} J R F e _).mpr
    intro V
    obtain ⟨T, hT, hm⟩ := hmodels V
    refine ⟨T, hT, ?_⟩
    intro U f hf
    obtain ⟨E, hE, ⟨pE⟩, ⟨p⟩⟩ := hm U f hf
    obtain ⟨hd, pd, hc, _⟩ :=
      ringedSiteStrictPerfectHom.{max c v, v, r, max c v r + 1}
        (J.over U) (R.over U) E hE pE
    let D := homComplex (R := R.over U) E
      (ringedSiteDualityUnitComplex.{max c v, v, r} (J.over U) (R.over U))
    refine ⟨D, hd, pd, ⟨?_⟩⟩
    exact (h U).app (op P, ringedSiteDualityUnit.{c, v, r, w} J R) ≪≫
      (derivedInternalHomOfUniverses.{max c v, v, r, max c v r + 1}
        (J.over U) (R.over U)).mapIso (p.symm.op.prod (o U)) ≪≫
      (ringedSiteOrdinaryHomIso.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)
        E (ringedSiteDualityUnitComplex.{max c v, v, r} (J.over U) (R.over U))
          (hc _)).symm
  · apply derived_iso_local.{c, v, r, w, max c v r + 1} J R F e Y hY
    intro i
    let U := Y i
    obtain ⟨E, hE, ⟨pE⟩, ⟨p⟩⟩ := i.property
    have hi := bidual_transport (MU U).closed (MU U).symmetric
      (ringedSiteDualityUnit.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)) p
      (strict_bidual.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)
        (MU U) E hE pE)
    exact (d U).bidual_isIso P hi
  · apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro N
    have hi : IsIso (ringedSiteDualEvaluation M.closed
        (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N) := by
      apply derived_iso_local.{c, v, r, w, max c v r + 1} J R F e Y hY
      intro i
      let U := Y i
      obtain ⟨E, hE, ⟨pE⟩, ⟨p⟩⟩ := i.property
      have hlocal := evaluation_transport_source (MU U).closed
        (ringedSiteDualityUnit.{max c v, v, r, max c v r + 1} (J.over U) (R.over U))
          (MU U).unitIso p ((F U).obj N)
        (strict_evaluation.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)
          (MU U) E hE pE ((F U).obj N))
      exact (d U).evaluation_isIso P N hlocal
    change IsIso (ringedSiteDualEvaluationLeft M.closed M.symmetric
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N)
    exact evaluation_left_isIso M.closed M.symmetric
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N hi

end CategoryTheory
