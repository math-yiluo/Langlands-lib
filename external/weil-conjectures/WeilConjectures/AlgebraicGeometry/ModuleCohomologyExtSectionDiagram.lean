/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.StandardAbelianExtSectionDiagram
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # The abelian Ext map in the common section-complex diagram

Source: Stacks Project, Tags 01FB, 01F7 and 03FD.
(blueprint: new-module-cohomology-ext-section-diagram)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution


/-- The map on abelian Ext cohomology induced by inverse image and the counit.
Source: Stacks Project, Tag 01F7. -/
abbrev abelianEdgeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    AddCommGrpCat.of (H ((pushforward f).obj F) p) ⟶ AddCommGrpCat.of (H F p) :=
  standardSectionExtHom f F p

attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem section_comparison_hom_naturality
    (X : Scheme.{u}) {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (I J : InjectiveResolution F) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = J.ι) (p : ℕ) :
    (abelianResolutionIso X I p).hom ≫
      HomologicalComplex.homologyMap
        (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p =
      (abelianResolutionIso X J p).hom := by
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let ιI := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map I.ι
  let ιJ := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (.up ℕ)).map J.ι
  have : QuasiIso ιI := by
    dsimp only [ιI]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map I.ι) := inferInstance
    exact quasiIso_comp _ _
  have : QuasiIso ιJ := by
    dsimp only [ιJ]
    have : QuasiIso ((T.mapHomologicalComplex (.up ℕ)).map J.ι) := inferInstance
    exact quasiIso_comp _ _
  have hw : ιI ≫ (T.mapHomologicalComplex (.up ℕ)).map φ =
      (CochainComplex.single₀ _).map (𝟙 (T.obj F)) ≫ ιJ := by
    rw [(CochainComplex.single₀ _).map_id, Category.id_comp]
    simp only [ιI, ιJ, Category.assoc,
      ← Functor.map_comp, hφ]
  have hc := acyclicComparison_naturality (abelianSections X) (ιI) (ιJ)
    (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n))
    (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n))
    (𝟙 (T.obj F)) ((T.mapHomologicalComplex (.up ℕ)).map φ) hw p
  rw [((abelianSections X).rightDerived p).map_id, Category.comp_id] at hc
  change HomologicalComplex.homologyMap
      (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p ≫
      ((abelianSections X).rightDerivedObjIsoOfResolution (ιJ)
        (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n)) p).inv =
    ((abelianSections X).rightDerivedObjIsoOfResolution (ιI)
      (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p).inv at hc
  have hh :
      ((abelianSections X).rightDerivedObjIsoOfResolution ιI
        (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p).hom ≫
        HomologicalComplex.homologyMap
          (((moduleSections X).mapHomologicalComplex (.up ℕ)).map φ) p =
      ((abelianSections X).rightDerivedObjIsoOfResolution ιJ
        (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n)) p).hom := by
    rw [← cancel_mono
      ((abelianSections X).rightDerivedObjIsoOfResolution ιJ
        (fun n ↦ forgottenInjectiveAcyclic X (J.cocomplex.X n)) p).inv]
    rw [Category.assoc, hc]
    simp only [Iso.hom_inv_id]
  dsimp only [abelianResolutionIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [hh]

private theorem section_lift_homology_eq
    (Y : Scheme.{u}) {G : Y.Modules} (J : InjectiveResolution G)
    (K : CochainComplex Y.Modules ℕ) (hK : ∀ n, Injective (K.X n))
    (β γ : J.cocomplex ⟶ K) (h : J.ι ≫ β = J.ι ≫ γ) (p : ℕ) :
    HomologicalComplex.homologyMap
      (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β) p =
    HomologicalComplex.homologyMap
      (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map γ) p := by
  let : ∀ n, Injective (K.X n) := hK
  let e := ComplexShape.embeddingUpNat
  let E := e.extendFunctor Y.Modules
  have : QuasiIso (E.map J.ι) :=
    (HomologicalComplex.quasiIso_extendMap_iff J.ι e).2 inferInstance
  have he : Nonempty (Homotopy (E.map J.ι ≫ E.map β) (E.map J.ι ≫ E.map γ)) := by
    rw [← E.map_comp, ← E.map_comp]
    exact ⟨(Homotopy.ofEq h).extend e⟩
  obtain ⟨hh⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := K.extend e)
    ⟨0, fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn⟩
    (E.map J.ι) (E.map β) (E.map γ) he
  have : (moduleSections Y).Additive := by
    dsimp only [moduleSections, RingedSpace.globalSectionsFunctor, SheafOfModules.evaluation]
    infer_instance
  exact ((moduleSections Y).mapHomotopy hh.ofExtend).homologyMap_eq p

/-- The section-diagram equality is stable after inserting the identity on its codomain.
This is a strict intermediate compatibility statement; cancelling the identity gives the
item theorem. Source: Stacks Project, Tag 01FB. (blueprint: new-abelian-edge-section-identity) -/
theorem abelianEdge_section_diagram_after_identity {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (D : ModuleCohomologyFMapData f ((pushforward f).obj F) F
      (𝟙 ((pushforward f).obj F))) (p : ℕ) :
    ((abelianResolutionIso Y D.J p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β)) ≫
        𝟙 ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
          (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.K)) =
      (abelianEdgeHom f F p ≫ (abelianResolutionIso X D.I p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (D.a.hom ≫
            ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda)) ≫
        𝟙 ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
          (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.K)) := by
  let J := injectiveResolution ((pushforward f).obj F)
  let φ := InjectiveResolution.desc (𝟙 ((pushforward f).obj F)) J D.J
  let β := standardSectionEdgeLift f D.I D.K D.injective D.lambda
  let Γ := (moduleSections Y).mapHomologicalComplex (.up ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p
  have hφ : D.J.ι ≫ φ = J.ι := by simp [φ]
  have hβ : J.ι.f 0 ≫ β.f 0 =
      (pushforward f).map (D.I.ι.f 0) ≫ D.lambda.f 0 :=
    sectionAugmentationLift_comm _ _ _ _ _
  have haug : D.J.ι ≫ D.β = D.J.ι ≫ (φ ≫ β) := by
    rw [← Category.assoc, hφ]
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    rw [D.compatible, Category.id_comp, hβ]
  have hh := section_lift_homology_eq Y D.J D.K D.injective D.β (φ ≫ β) haug p
  change H.map (Γ.map D.β) = H.map (Γ.map (φ ≫ β)) at hh
  rw [Functor.map_comp, Functor.map_comp] at hh
  have hc := section_comparison_hom_naturality Y D.J J φ hφ p
  change (abelianResolutionIso Y D.J p).hom ≫ H.map (Γ.map φ) =
    (abelianResolutionIso Y J p).hom at hc
  simp only [Category.comp_id]
  change (abelianResolutionIso Y D.J p).hom ≫ H.map (Γ.map D.β) = _
  rw [hh, ← Category.assoc, hc]
  exact standard_abelian_ext_section_diagram f D.I D.K D.injective D.lambda
    D.quasiIso D.a D.sections p

/-- The Ext map and the horizontal section map agree after the vertical section map.
This is a square between abelian Ext and section homology; neither the module
edge map nor the module/Ext equivalence occurs in the assertion.
Source: Stacks Project, Tag 01FB, the common section diagram;
Tag 01F7, its functorial cohomology map; Tag 03FD, forgotten injective acyclicity.
(blueprint: new-module-cohomology-ext-section-diagram)

Proof: Forget modules in I,J,K and in the augmentation equation D.compatible.
The forgotten I and J are resolutions by abelian-section-acyclic objects;
their canonical acyclic comparisons give abelianResolutionIso. The forgotten
f_*I computes the derived abelian direct image, because injective module terms
are abelian-cohomology acyclic on every open (03FD). The quasi-isomorphism
lambda into K compares this complex with its injective replacement. The
augmentation lift beta represents the map from the abelian sheaf f_*F into
this derived direct image. Evaluating the derived adjunction at the constant
integer sheaf identifies that map with exact inverse image on Ext followed
by the counit coeff(f,identity). The terminal-source comparison evaluates
the free generator at 1, so its inverse-image identification is constIso(f).
The global-section identification f_*I(Y)=I(X) is precisely D.a, pinned by
D.sections. Consequently both composites into H(Γ(Y,K)) are H(Γ(beta)).
Homotopy invariance removes the choices of augmentation lifts; naturality of
the acyclic comparison removes the choices of resolutions. This proves the
displayed square before any cancellation of its vertical map. Degree zero
is the section identity; empty schemes and zero coefficients give the same
square. No acyclicity of f_*F or exactness of module pullback is used. -/
theorem abelianEdge_section_diagram {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (D : ModuleCohomologyFMapData f ((pushforward f).obj F) F
      (𝟙 ((pushforward f).obj F))) (p : ℕ) :
    (abelianResolutionIso Y D.J p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) =
      abelianEdgeHom f F p ≫ (abelianResolutionIso X D.I p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (D.a.hom ≫
            ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) := by
  convert abelianEdge_section_diagram_after_identity f F D p using 1

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
