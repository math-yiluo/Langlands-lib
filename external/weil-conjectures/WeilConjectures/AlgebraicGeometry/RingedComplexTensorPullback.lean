/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback

/-! # Tensor comparison on actual complexes of module sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and
sites-modules.tex, Tag 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe v u w u' w'

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace CategoryTheory.ConstantCompletion

/-- A tensor comparison together with its two naturality laws and unit normalization.
The tensor functors and unitors are parameters, so concrete localized monoidal
structures are checked once when constructing this data. -/
structure TensorPullbackComparison
    {E : Type u} [Category.{w} E] {E' : Type u'} [Category.{w'} E']
    (P : E ⥤ E') (T : E ⥤ E ⥤ E) (T' : E' ⥤ E' ⥤ E')
    (R : E) (S : E') (ρ : ∀ N : E, (T.obj N).obj R ≅ N)
    (ρ' : ∀ N : E', (T'.obj N).obj S ≅ N) where
  j : P.obj R ≅ S
  t : ∀ N M : E, P.obj ((T.obj N).obj M) ≅ (T'.obj (P.obj N)).obj (P.obj M)
  rightNaturality : ∀ (N M M' : E) (g : M ⟶ M'),
    P.map ((T.obj N).map g) ≫ (t N M').hom =
      (t N M).hom ≫ (T'.obj (P.obj N)).map (P.map g)
  leftNaturality : ∀ (N N' M : E) (f : N ⟶ N'),
    P.map ((T.map f).app M) ≫ (t N' M).hom =
      (t N M).hom ≫ (T'.map (P.map f)).app (P.obj M)
  unit : ∀ N : E, P.map (ρ N).inv ≫ (t N R).hom ≫
    (T'.obj (P.obj N)).map j.hom = (ρ' (P.obj N)).inv

private theorem normalizedComposite
    {E : Type u} [Category.{w} E] {X U V W : E}
    (a : X ⟶ U) (b : U ≅ V) (c : V ≅ W) (d : X ⟶ W)
    (h : d ≫ c.inv ≫ b.inv = a) : a ≫ b.hom ≫ c.hom = d := by
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem tensorUnitInverse
    {E : Type u} [Category.{w} E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [MonoidalCategory E']
    (P : E ⥤ E') (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (h : ∀ M : E, (μ M (𝟙_ E)).hom ≫ (𝟙 (P.obj M) ⊗ₘ j₀.hom) ≫
      (MonoidalCategory.rightUnitor (P.obj M)).hom =
        P.map (MonoidalCategory.rightUnitor M).hom) (M : E) :
    (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
        (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
      P.map (MonoidalCategory.rightUnitor M).inv := by
  let q := μ M (𝟙_ E) ≪≫ (MonoidalCategory.tensorLeft (P.obj M)).mapIso j₀ ≪≫
    MonoidalCategory.rightUnitor (P.obj M)
  have hq : q = P.mapIso (MonoidalCategory.rightUnitor M) := by
    apply Iso.ext
    simpa only [q, Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorLeft, MonoidalCategory.curriedTensor_obj_map] using h M
  simpa only [q, Iso.trans_inv, Functor.mapIso_inv, MonoidalCategory.tensorLeft,
    MonoidalCategory.curriedTensor_obj_map, Category.assoc] using congrArg Iso.inv hq

private theorem inverseNaturality
    {E : Type u} [Category.{w} E] {A B C D : E}
    (i : A ≅ B) (j : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ j.hom = i.hom ≫ g) : g ≫ j.inv = i.inv ≫ f := by
  apply (cancel_mono j.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

-- Prove the component calculation abstractly, before specializing to module sheaves.
private theorem tensorTotalRightUnit
    {E : Type u} [Category.{w} E] [Abelian E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [Abelian E'] [MonoidalCategory E']
    [MonoidalPreadditive E] [MonoidalPreadditive E']
    [MonoidalClosed E] [MonoidalClosed E']
    [HasCoproducts.{0} E] [HasCoproducts.{0} E']
    (P : E ⥤ E') [P.Additive]
    (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map (f ⊗ₘ g) ≫ (μ X' Y').hom = (μ X Y).hom ≫ (P.map f ⊗ₘ P.map g))
    (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (hunit : ∀ M : E, (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
      (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
        P.map (MonoidalCategory.rightUnitor M).inv)
    (N : CochainComplex E ℤ) :
    let Pc := P.mapHomologicalComplex (.up ℤ)
    let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
    let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
      (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
    (HomologicalComplex.rightUnitor (Pc.obj N)).inv ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (Pc.obj N)) j.inv
          (MonoidalCategory.curriedTensor E') (.up ℤ) ≫
        tensorPullbackTotal P μ hμ N RX =
      Pc.map (HomologicalComplex.rightUnitor N).inv := by
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
  let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
    (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
  apply HomologicalComplex.hom_ext
  intro n
  have hj : j.inv.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ E')).hom ≫ j₀.inv ≫
      P.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ E)).inv := by
    simp only [j, Iso.trans_inv, HomologicalComplex.comp_f,
      Functor.mapIso_inv, Iso.app_inv, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc,
      Iso.inv_hom_id_assoc]
  have hn := hμ (𝟙 (N.X n))
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ E)).inv
  have hn' :
      (P.obj (N.X n) ◁ P.map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ E)).inv) ≫
          (μ (N.X n) (RX.X 0)).inv =
        (μ (N.X n) (𝟙_ E)).inv ≫
          P.map (N.X n ◁
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (𝟙_ E)).inv) := by
    apply (cancel_mono (μ (N.X n) (RX.X 0)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
      P.map_id, Category.id_comp, Iso.inv_hom_id_assoc] using
      congrArg (fun z ↦
        (μ (N.X n) (𝟙_ E)).inv ≫ z) hn.symm
  simp only [HomologicalComplex.comp_f]
  change (HomologicalComplex.rightUnitor' (Pc.obj N)).inv n ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 (Pc.obj N)) j.inv
      (MonoidalCategory.curriedTensor E') (.up ℤ)).f n ≫
        (tensorPullbackTotal P μ hμ N RX).f n =
      P.map ((HomologicalComplex.rightUnitor N).inv.f n)
  erw [HomologicalComplex.rightUnitor'_inv]
  erw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp]
  erw [tensorPullbackTotal]
  change _ ≫ _ ≫ _ ≫ _ ≫ tensorPullbackTotalComponent P μ N RX n = _
  erw [tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc]
  erw [hj, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  change (MonoidalCategory.rightUnitor (P.obj (N.X n))).inv ≫
      (P.obj (N.X n) ◁ _) ≫ (P.obj (N.X n) ◁ _) ≫
      (P.obj (N.X n) ◁ j₀.inv) ≫ (P.obj (N.X n) ◁ _) ≫
      (μ (N.X n) (RX.X 0)).inv ≫ _ =
    P.map ((HomologicalComplex.rightUnitor N).inv.f n)
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [← Category.assoc _ (μ (N.X n) (RX.X 0)).inv,
    hn', Category.assoc]
  have hu := hunit (N.X n)
  simp only [← Category.assoc] at hu ⊢
  rw [hu, ← P.map_comp, ← P.map_comp]
  congr 1
  simp only [Category.assoc]
  exact (HomologicalComplex.rightUnitor'_inv N n).symm

-- Keep total-complex constructions abstract until their one sheaf specialization.
private theorem tensorComparisonFamily
    {E : Type u} [Category.{w} E] [Abelian E] [MonoidalCategory E]
    {E' : Type u'} [Category.{w'} E'] [Abelian E'] [MonoidalCategory E']
    [MonoidalPreadditive E] [MonoidalPreadditive E']
    [MonoidalClosed E] [MonoidalClosed E']
    [HasCoproducts.{0} E] [HasCoproducts.{0} E']
    (P : E ⥤ E') [P.Additive]
    (μ : ∀ X Y : E, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : E} (f : X ⟶ X') (g : Y ⟶ Y'),
      P.map (f ⊗ₘ g) ≫ (μ X' Y').hom = (μ X Y).hom ≫ (P.map f ⊗ₘ P.map g))
    (G : E' ⥤ E) (am : P ⊣ G) (j₀ : P.obj (𝟙_ E) ≅ 𝟙_ E')
    (hunit : ∀ M : E, (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
      (P.obj M ◁ j₀.inv) ≫ (μ M (𝟙_ E)).inv =
        P.map (MonoidalCategory.rightUnitor M).inv) :
    Nonempty (TensorPullbackComparison (P.mapHomologicalComplex (.up ℤ))
      ((MonoidalCategory.curriedTensor E).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))
      ((MonoidalCategory.curriedTensor E').map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))
      ((HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E))
      ((HomologicalComplex.single E' (.up ℤ) 0).obj (𝟙_ E'))
      (fun N ↦ HomologicalComplex.rightUnitor N)
      (fun N ↦ HomologicalComplex.rightUnitor N)) := by
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let RX := (HomologicalComplex.single E (.up ℤ) 0).obj (𝟙_ E)
  let j := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app (𝟙_ E) ≪≫
    (HomologicalComplex.single E' (.up ℤ) 0).mapIso j₀
  let β (N M : CochainComplex E ℤ) :=
    @asIso _ _ _ _ (tensorPullbackTotal P μ hμ N M)
      (tensorPullbackTotal_isIso P μ hμ G am N M)
  have hβ {N N' M M' : CochainComplex E ℤ} (f : N ⟶ N') (g : M ⟶ M') :
      HomologicalComplex.mapBifunctorMap (Pc.map f) (Pc.map g)
          (MonoidalCategory.curriedTensor E') (.up ℤ) ≫ (β N' M').hom =
        (β N M).hom ≫ Pc.map (HomologicalComplex.mapBifunctorMap f g
          (MonoidalCategory.curriedTensor E) (.up ℤ)) := by
    exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
      P μ hμ f g
  refine ⟨⟨j, fun N M ↦ (β N M).symm, ?_, ?_, ?_⟩⟩
  · intro N M M' g
    dsimp only [Functor.map₂HomologicalComplex]
    apply inverseNaturality
    simpa only [Pc.map_id] using hβ (𝟙 N) g
  · intro N N' M f
    dsimp only [Functor.map₂HomologicalComplex]
    apply inverseNaturality
    simpa only [Pc.map_id] using hβ f (𝟙 M)
  · intro N
    let T := (MonoidalCategory.curriedTensor E').map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)
    exact normalizedComposite _ (β N RX).symm ((T.obj (Pc.obj N)).mapIso j) _
      (tensorTotalRightUnit P μ hμ j₀ hunit N)

-- The two naturalities and unit calculation elaborate in one declaration.
/-- Module inverse image commutes with total tensor, naturally in both complexes,
and the comparison respects the inverse right unitor.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, proof by total complexes;
sites-modules.tex, Tag 03EL, ordinary tensor and unit comparison.
(auxiliary; not a blueprint node).

Proof: use the canonical ordinary tensor comparison on module sheaves. Its inverse
on each bidegree, followed by insertion into the pulled-back total tensor, defines
the reverse chain comparison. Naturality handles the two differentials; additivity
preserves their signs. Module inverse image is a left adjoint, so it preserves the
coproducts defining totalization, making this chain map invertible. Naturality on
summands gives the two displayed naturality equations for the family of
isomorphisms. The ordinary rank-one comparison gives the isomorphism on the ring
complex, using preservation of zero objects outside degree zero. Test the right
unitor equation on every tensor summand: only the ring-complex degree zero can
contribute, and there it is the ordinary right-unit equation. All other summands
are zero. Coproduct extensionality proves the equation of chain maps. -/
theorem ringedComplexTensorPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
    (c : F.rings.obj R ⟶ S) :
    Nonempty (TensorPullbackComparison ((pull F c).mapHomologicalComplex (.up ℤ))
      (ringedKoszulTensor R) (ringedKoszulTensor S)
      (ringedSiteRingComplex R) (ringedSiteRingComplex S)
      (ringedKoszulRightUnitIso R) (ringedKoszulRightUnitIso S)) := by
  let P : Mod R ⥤ Mod S := pull F c
  obtain ⟨G, _, am, _⟩ := module_adjunction_exists V adj F c
  let hobj : ∀ M : Mod R, P.obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := fun _ ↦ rfl
  have hmap : ∀ {M N : Mod R} (f : M ⟶ N), P.map f =
      eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := SheafOfModules.canonicalRingedTensorComparison_existsUnique
    R S (F.rings.obj R) L (F.algebra R) c P hobj V adj hmap
  obtain ⟨j₀, hj₀, _⟩ := SheafOfModules.canonicalRingedTensorComparison_unit
    R S (F.rings.obj R) L (F.algebra R) c P hobj hmap k
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let := Classical.choice (SheafOfModules.tensorClosed S).2.1
  let := SheafOfModules.ringedTensorPreadditive R
  let := SheafOfModules.ringedTensorPreadditive S
  have hunit (M : Mod R) :
      (MonoidalCategory.rightUnitor (P.obj M)).inv ≫
          (P.obj M ◁ j₀.inv) ≫ (k.mu M (SheafOfModules.unit (siteModuleRings R))).inv =
        P.map (MonoidalCategory.rightUnitor M).inv :=
    tensorUnitInverse P k.mu j₀ hj₀ M
  exact tensorComparisonFamily P k.mu k.naturality G.obj am j₀ hunit

end CategoryTheory.ConstantCompletion
