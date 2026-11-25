/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianResolutionSectionsIso
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Existence of an augmentation quotient in one degree

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: new-abelian-cech-comparison-core)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev sectionsMap {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I J : InjectiveResolution F} (f : I.cocomplex ⟶ J.cocomplex) :
    abelianCechSections I ⟶ abelianCechSections J :=
  ((sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))).mapHomologicalComplex
    (.up ℕ)).map f

set_option backward.isDefEq.respectTransparency false in
private noncomputable def totalMap {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I J : InjectiveResolution F} (f : I.cocomplex ⟶ J.cocomplex) :
    (abelianCechDouble U I).total (.up ℕ) ⟶
      (abelianCechDouble U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
      (((TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map f))
    (.up ℕ)

set_option backward.isDefEq.respectTransparency false in
private theorem alpha_naturality {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I J : InjectiveResolution F} (f : I.cocomplex ⟶ J.cocomplex) :
    abelianCechAlpha U I ≫ totalMap U f = sectionsMap f ≫ abelianCechAlpha U J := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [abelianCechAlpha, totalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (TopCat.Sheaf.toCechCochainZero U (I.cocomplex.X n) ≫
    ((TopCat.Sheaf.cechComplexFunctor U).map (f.f n)).f 0) ≫ _ =
    (sectionsMap f).f n ≫
      (TopCat.Sheaf.toCechCochainZero U (J.cocomplex.X n) ≫ _)
  rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ (abelianCechDouble U J).ιTotal (.up ℕ) 0 n n (by simp))
  ext s
  funext y
  exact NatTrans.naturality_apply (f.f n).hom
    (homOfLE (le_top (a := ⨅ l, U (y l)))).op s

set_option backward.isDefEq.respectTransparency false in
private theorem beta_naturality {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I J : InjectiveResolution F} (f : InjectiveResolution.Hom I J (𝟙 F)) :
    abelianCechBeta U I ≫ totalMap U f.hom = abelianCechBeta U J := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [abelianCechBeta, totalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (((TopCat.Sheaf.cechComplexFunctor U).map (I.ι.f 0)).f n ≫
    ((TopCat.Sheaf.cechComplexFunctor U).map (f.hom.f 0)).f n) ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
  have hf : I.ι.f 0 ≫ f.hom.f 0 = J.ι.f 0 := by
    simp
  rw [hf]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A quotient comparison exists in one degree, without a normalization assertion.

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2, the quotient of beta by
alpha; resolution independence expands the functoriality verification there.
(blueprint: new-abelian-cech-comparison-core)

Proof: Fix an injective resolution I. The section-homology identification
exists_abelianResolutionSectionsIso gives an isomorphism e from its section
homology to Ext, with the specified cocycle formula. Define c by H(beta),
inverse H(alpha), and e, in that order; hα I makes the middle map invertible.

For any resolution J, use InjectiveResolution.homotopyEquiv J I to lift the
identity of F to a chain map J -> I. Applying sections to this homotopy
equivalence makes its homology map s invertible. Applying the Čech functor,
flipping the double complex and totalizing gives a map with homology map t.
Restriction naturality and the augmentation identity prove the commuting alpha
and beta squares explicitly. The alpha square and hα make t invertible.
Transport the specified cycle z on J along the sections map. The adjunction's
naturality identifies this cycle with a composed with the resolution lift.
InjectiveResolution.extMk_comp_mk₀ for the identity shows its Ext class is
unchanged. The cocycle formula for e and c(x)=extMk(a) therefore identify its
homology class with inverse H(alpha)(H(beta)(x)). Apply the two augmentation
squares, and cancel the invertible t, to obtain the required equation on J.

The argument uses neither hcover nor a finite-cover assumption: the supplied
quasi-isomorphisms suffice. If F is zero, or the space and cover are empty, the
same quotient construction uses the zero groups and still applies. -/
theorem exists_abelianCechComparison_core
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hα : ∀ I : InjectiveResolution F, QuasiIso (abelianCechAlpha U I)) (q : ℕ) :
    ∃ c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F,
      IsAbelianCechComparison U F q c := by
  classical
  let I := injectiveResolution F
  obtain ⟨e, he⟩ := exists_abelianResolutionSectionsIso I q
  have := hα I
  let αI := HomologicalComplex.homologyMap (abelianCechAlpha U I) q
  let βI := HomologicalComplex.homologyMap (abelianCechBeta U I) q
  let c := βI ≫ inv αI ≫ e.hom
  refine ⟨c, ?_⟩
  intro J x a ha z hz hc
  let r := InjectiveResolution.homotopyEquiv J I
  let φ : InjectiveResolution.Hom J I (𝟙 F) :=
    ⟨r.hom, by simp [r, InjectiveResolution.homotopyEquiv]⟩
  let s := HomologicalComplex.homologyMap (sectionsMap φ.hom) q
  let t := HomologicalComplex.homologyMap (totalMap U φ.hom) q
  have hs : IsIso s := by
    let G := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))
    exact (G.mapHomotopyEquiv r).toHomologyIso q |>.isIso_hom
  have hA : HomologicalComplex.homologyMap (abelianCechAlpha U J) q ≫ t =
      s ≫ αI := by
    rw [← HomologicalComplex.homologyMap_comp, alpha_naturality,
      HomologicalComplex.homologyMap_comp]
  have hB : HomologicalComplex.homologyMap (abelianCechBeta U J) q ≫ t = βI := by
    rw [← HomologicalComplex.homologyMap_comp, beta_naturality]
  have := hα J
  have ht : IsIso t := by
    have : IsIso (HomologicalComplex.homologyMap (abelianCechAlpha U J) q ≫ t) := by
      rw [hA]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (HomologicalComplex.homologyMap (abelianCechAlpha U J) q) t
  let z' := HomologicalComplex.cyclesMap (sectionsMap φ.hom) q z
  have ha' : (a ≫ φ.hom.f q) ≫ I.cocomplex.d q (q + 1) = 0 := by
    rw [Category.assoc, φ.hom.comm, ← Category.assoc, ha, zero_comp]
  have hz' :
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ (a ≫ φ.hom.f q)) (ULift.up 1) =
          (abelianCechSections I).iCycles q z' := by
    rw [Adjunction.homEquiv_naturality_right]
    change (φ.hom.f q).hom.app (op ⊤)
      (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ a) (ULift.up 1)) = _
    rw [hz]
    exact (ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (sectionsMap φ.hom) q) z).symm
  have hez : e.hom ((abelianCechSections I).homologyπ q z') =
      J.extMk a (q + 1) rfl ha := by
    rw [he (a ≫ φ.hom.f q) ha' z' hz']
    simpa using (J.extMk_comp_mk₀ a (q + 1) rfl ha φ).symm
  have hcz : inv αI (βI x) = (abelianCechSections I).homologyπ q z' := by
    apply (AddCommGrpCat.mono_iff_injective e.hom).1 inferInstance
    exact hc.trans hez.symm
  have hπ : s ((abelianCechSections J).homologyπ q z) =
      (abelianCechSections I).homologyπ q z' :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (sectionsMap φ.hom) q) z
  apply (AddCommGrpCat.mono_iff_injective t).1 inferInstance
  change (HomologicalComplex.homologyMap (abelianCechBeta U J) q ≫ t) x =
    (HomologicalComplex.homologyMap (abelianCechAlpha U J) q ≫ t)
      ((abelianCechSections J).homologyπ q z)
  rw [hB, hA]
  change βI x = αI (s ((abelianCechSections J).homologyπ q z))
  rw [hπ, ← hcz]
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id αI) (βI x) |>.symm
end AlgebraicGeometry.Scheme.Modules
