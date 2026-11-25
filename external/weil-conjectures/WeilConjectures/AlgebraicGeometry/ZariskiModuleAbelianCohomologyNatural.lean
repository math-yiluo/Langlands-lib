/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Natural comparison of module and abelian cohomology

Source: Stacks Project, sites-cohomology.tex, Tag 03FD.
(blueprint: lem-sc-module-abelian-zariski-cohomology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
namespace AlgebraicGeometry

-- Naturality of forgetting homology is independent of the ringed space.
private theorem resolutionForget_naturality
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    (G : A ⥤ B) (V : B ⥤ D) [G.Additive] [V.Additive] [V.PreservesHomology]
    {M N : A} (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (q : ℕ) :
    V.map ((G.rightDerived q).map f) ≫
        (V.mapIso (J.isoRightDerivedObj G q) ≪≫
          ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).sc q).mapHomologyIso
            V).symm).hom =
      (V.mapIso (I.isoRightDerivedObj G q) ≪≫
          ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc q).mapHomologyIso
            V).symm).hom ≫
        HomologicalComplex.homologyMap
          ((V.mapHomologicalComplex _).map ((G.mapHomologicalComplex _).map φ)) q := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← V.map_comp,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm G q,
    V.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ V.map (I.isoRightDerivedObj G q).hom ≫ k)
    (ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ q).map
        ((G.mapHomologicalComplex _).map φ)) V)

-- Comparing the two section complexes requires unfolding module and abelian evaluations.
set_option backward.isDefEq.respectTransparency false in
/-- Module cohomology and abelian sheaf cohomology are naturally isomorphic.

Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD.
(blueprint: new-zariski-module-abelian-cohomology-components)

Proof: Choose an injective resolution of each module sheaf. Forgetting to abelian sheaves
is exact, and every forgotten injective module is acyclic for global sections. Thus the
same global-sections complex computes both cohomologies. The acyclic-resolution comparison
provides the component isomorphisms. A module morphism lifts to a chain map of resolutions;
the induced map on the common complex computes both cohomology maps. Independence of the
lift up to homotopy proves the naturality squares. Assemble these component isomorphisms
into a natural isomorphism. The componentwise comparison comes from the common resolution
complex. No degree-zero normalization is asserted here. -/
theorem zariskiModuleAbelianCohomologyNatural_components (X : Scheme.{u}) (q : ℕ) :
    let F := RingedSpace.moduleCohomology X.toRingedSpace q ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u}
    let G := SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
      @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
        (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
        inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    ∃ e : ∀ M, F.obj M ≅ G.obj M,
      ∀ {M N} (f : M ⟶ N), F.map f ≫ (e N).hom = (e M).hom ≫ G.map f := by
  classical
  let : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
        (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  have : T.PreservesHomology := inferInstance
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    (Opens.grothendieckTopology X.carrier) (⊤ : Opens X.carrier) q
  have hac (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      [Injective I] : Γ.rightAcyclic (T.obj I) := by
    intro n
    let : Subsingleton (Sheaf.H' (T.obj I) (n + 1) ⊤) :=
      injective_module_abelian_acyclic ⊤ I (n + 1) (Nat.succ_pos n)
    obtain ⟨dn⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      (Opens.grothendieckTopology X.carrier) (⊤ : Opens X.carrier) (n + 1)
    have hz : IsZero (Sheaf.H' (T.obj I) (n + 1) ⊤) :=
      AddCommGrpCat.isZero_of_subsingleton _
    exact hz.of_iso (dn.app (T.obj I)).symm
  let I := fun M : SheafOfModules.{u} (moduleRings X.toRingedSpace) ↦ injectiveResolution M
  let ι := fun M ↦
    (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app M ≫
      (T.mapHomologicalComplex (ComplexShape.up ℕ)).map (I M).ι
  have hι (M) : QuasiIso (ι M) := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map (I M).ι) :=
      inferInstance
    exact quasiIso_comp _ _
  -- The forgotten module resolution is termwise acyclic for abelian sections.
  let c := fun M ↦ Γ.rightDerivedObjIsoOfResolution (ι M)
    (fun n ↦ hac ((I M).cocomplex.X n)) q
  -- Exact forgetting commutes with the homology of the section complex.
  let a : ∀ M, V.obj ((G.rightDerived q).obj M) ≅
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I M).cocomplex)).homology q :=
    fun M ↦ V.mapIso ((I M).isoRightDerivedObj G q) ≪≫
      ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I M).cocomplex).sc q).mapHomologyIso
        V).symm
  let e := fun M ↦ a M ≪≫ (c M).symm ≪≫ (d.app (T.obj M)).symm
  refine ⟨e, ?_⟩
  intro M N f
  let φ := InjectiveResolution.desc f (I N) (I M)
  -- Use one lift of f throughout all three comparison squares.
  have ha : V.map ((G.rightDerived q).map f) ≫ (a N).hom =
      (a M).hom ≫ HomologicalComplex.homologyMap
        ((Γ.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map φ)) q := by
    exact resolutionForget_naturality G V f (I M) (I N) φ
      (InjectiveResolution.desc_commutes_zero f (I N) (I M)) q
  have hw : ι M ≫ (T.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ _).map (T.map f) ≫ ι N := by
    dsimp only [ι]
    rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
      Functor.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ (T.mapHomologicalComplex _).map (I N).ι)
        ((HomologicalComplex.singleMapHomologicalComplex T
          (ComplexShape.up ℕ) 0).inv.naturality f).symm
  have hc := acyclicComparison_naturality Γ (ι M) (ι N)
    (fun n ↦ hac ((I M).cocomplex.X n)) (fun n ↦ hac ((I N).cocomplex.X n))
    (T.map f) ((T.mapHomologicalComplex _).map φ) hw q
  dsimp only [e, Iso.trans_hom, Iso.symm_hom]
  change V.map ((G.rightDerived q).map f) ≫
    ((a N).hom ≫ (c N).inv ≫ (d.app (T.obj N)).inv) =
      ((a M).hom ≫ (c M).inv ≫ (d.app (T.obj M)).inv) ≫ _
  rw [← Category.assoc, ← Category.assoc, ha]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  exact congrArg (fun k ↦ (a M).hom ≫ (c M).inv ≫ k)
    (d.inv.naturality (T.map f))

/-- Module cohomology and abelian sheaf cohomology are naturally isomorphic.

Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD.
(blueprint: lem-sc-module-abelian-zariski-cohomology)

The componentwise comparison and its naturality are provided by
`zariskiModuleAbelianCohomologyNatural_components`; `NatIso.ofComponents`
assembles them into the required natural isomorphism. -/
theorem zariskiModuleAbelianCohomologyNatural (X : Scheme.{u}) (q : ℕ) :
    Nonempty ((RingedSpace.moduleCohomology X.toRingedSpace q ⋙
        forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
          (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
          inferInstance
          (@hasExt_of_enoughInjectives _ _ _ inferInstance
            (@IsGrothendieckAbelian.enoughInjectives _ _ _
              (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
        (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))) := by
  classical
  let F := RingedSpace.moduleCohomology X.toRingedSpace q ⋙
    forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}
  let G := SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
    @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
      (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
      inferInstance
      (@hasExt_of_enoughInjectives _ _ _ inferInstance
        (@IsGrothendieckAbelian.enoughInjectives _ _ _
          (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
            (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  obtain ⟨e, h⟩ := zariskiModuleAbelianCohomologyNatural_components X q
  exact ⟨NatIso.ofComponents e h⟩

end AlgebraicGeometry
