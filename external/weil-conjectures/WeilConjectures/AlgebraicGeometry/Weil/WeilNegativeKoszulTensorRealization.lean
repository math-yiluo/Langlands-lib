/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulTransitions
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.AlgebraicGeometry.Weil.WeilNegativeKoszulFactorRealization
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedRealizationTensor

/-! # Realization of negative exterior factors as negative two-term factors

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(blueprint: lem-weil-pbc-negative-koszul-tensor-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem exteriorUnit_isIso {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    IsIso (finiteKoszulExteriorUnitZero r a m) := by
  unfold finiteKoszulExteriorUnitZero
  change IsIso ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toModuleIso.inv ≫ _)
  infer_instance

private theorem bifunctorMap_comp
    {D E F : Type*} [Category D] [Category E] [Category F]
    (T : D ⥤ E ⥤ F) {K₀ K₁ K₂ : D} {L₀ L₁ L₂ : E}
    (f₀ : K₀ ⟶ K₁) (f₁ : K₁ ⟶ K₂) (g₀ : L₀ ⟶ L₁) (g₁ : L₁ ⟶ L₂) :
    (T.map f₀).app L₀ ≫ (T.obj K₁).map g₀ ≫
        (T.map f₁).app L₁ ≫ (T.obj K₂).map g₁ =
      (T.map (f₀ ≫ f₁)).app L₀ ≫ (T.obj K₂).map (g₀ ≫ g₁) := by
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [(T.map f₁).naturality_assoc]

private theorem negativeTransition_succ
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u + 1}) (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections) (m : ℕ) :
    ringedNegativeKoszulTransition O (r + 1) b m =
      ((ringedKoszulTensor O).map (ringedNegativeKoszulFactorTransition O (b 0) m)).app
          (ringedNegativeKoszul O r (fun i ↦ b i.succ) (m + 1)) ≫
        ((ringedKoszulTensor O).obj (ringedNegativeKoszulFactor O (b 0) m)).map
          (ringedNegativeKoszulTransition O r (fun i ↦ b i.succ) m) := rfl

private theorem bifunctorInclusion_natural
    {V : Type*} [Category V] [Preadditive V] (B : V ⥤ V ⥤ V)
    [B.PreservesZeroMorphisms] [∀ P, (B.obj P).PreservesZeroMorphisms]
    [∀ K L : CochainComplex V ℤ,
      HomologicalComplex.HasMapBifunctor K L B (.up ℤ)]
    (K L K' L' : CochainComplex V ℤ) (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.ιMapBifunctor K L B (.up ℤ) 0 0 0 (by rfl) ≫
        (HomologicalComplex.mapBifunctorMap f (𝟙 L) B (.up ℤ)).f 0 ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 K') g B (.up ℤ)).f 0 =
      (B.map (f.f 0)).app (L.X 0) ≫ (B.obj (K'.X 0)).map (g.f 0) ≫
        HomologicalComplex.ιMapBifunctor K' L' B (.up ℤ) 0 0 0 (by rfl) := by
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rw [(B.obj (K'.X 0)).map_id (L.X 0), B.map_id (K'.X 0), NatTrans.id_app]
  simp only [Category.id_comp]

private theorem tensorInclusion_natural
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u + 1}) :
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ∀ (K L K' L' : ringedSiteComplex O) (f : K ⟶ K') (g : L ⟶ L'),
      CochainComplex.ιMapBifunctor K L (curriedTensor _) 0 0 0 (by rfl) ≫
          (((ringedKoszulTensor O).map f).app L).f 0 ≫
            (((ringedKoszulTensor O).obj K').map g).f 0 =
        (f.f 0 ⊗ₘ g.f 0) ≫
          CochainComplex.ιMapBifunctor K' L' (curriedTensor _) 0 0 0 (by rfl) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  intro K L K' L' f g
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor _) (.up ℤ)
      0 0 0 (by rfl) ≫ (HomologicalComplex.mapBifunctorMap f (𝟙 L)
      (curriedTensor _) (.up ℤ)).f 0 ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K') g (curriedTensor _) (.up ℤ)).f 0 = _
  rw [tensorHom_def_assoc]
  exact bifunctorInclusion_natural (curriedTensor _) K L K' L' f g

private theorem negativeTensorInduction
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u + 1})
    {A : Type (u + 1)} [CommRing A]
    (Q : ModuleCat.{u + 1} A ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    [Q.Additive]
    (c : SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) ⟶ Q.obj (ModuleCat.of A A))
    (b : A → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections) :
    let H := Q.mapHomologicalComplex (.up ℤ)
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    (∀ a : A, ∃ e : ∀ m : ℕ, H.obj (completedKoszulPower (A := A) 1 (fun _ ↦ a) m) ≅
        ringedNegativeKoszulFactor O (b a) m,
      (∀ m, H.map (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m) ≫
        (e m).hom = (e (m + 1)).hom ≫ ringedNegativeKoszulFactorTransition O (b a) m) ∧
      (∀ m, c ≫ Q.map
            (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a) m) ≫ (e m).hom.f 0 =
        ringedNegativeKoszulFactorBasis O (b a) m 0)) →
    (∃ t : ∀ K L : CochainComplex (ModuleCat.{u + 1} A) ℤ,
        H.obj (HomologicalComplex.tensorObj K L) ≅
          ((ringedKoszulTensor O).obj (H.obj K)).obj (H.obj L),
      (∀ (K L K' L' : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (f : K ⟶ K') (g : L ⟶ L'),
        H.map (HomologicalComplex.tensorHom f g) ≫ (t K' L').hom =
          (t K L).hom ≫ ((ringedKoszulTensor O).map (H.map f)).app (H.obj L) ≫
            ((ringedKoszulTensor O).obj (H.obj K')).map (H.map g)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u + 1} A) ℤ)
          (v : ModuleCat.of A A ⟶ K.X 0) (w : ModuleCat.of A A ⟶ L.X 0),
        c ≫ Q.map ((ρ_ (ModuleCat.of A A)).inv ≫ (v ⊗ₘ w) ≫
          HomologicalComplex.ιTensorObj K L 0 0 0 (by omega)) ≫ (t K L).hom.f 0 =
        (λ_ (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))).inv ≫
          ((c ≫ Q.map v) ⊗ₘ (c ≫ Q.map w)) ≫
            CochainComplex.ιMapBifunctor (H.obj K) (H.obj L)
              (curriedTensor _) 0 0 0 (by omega))) →
    ∀ (r : ℕ) (a : Fin r → A), ∃ e : ∀ m : ℕ, H.obj (finiteNegativeKoszulTensor r a m) ≅
        ringedNegativeKoszul O r (fun i ↦ b (a i)) m,
      (∀ m, H.map (finiteNegativeKoszulTransition r a m) ≫ (e m).hom =
        (e (m + 1)).hom ≫ ringedNegativeKoszulTransition O r (fun i ↦ b (a i)) m) ∧
      (∀ m, c ≫ Q.map (finiteNegativeKoszulUnitZero r a m) ≫ (e m).hom.f 0 =
        ringedNegativeKoszulBasis O r (fun i ↦ b (a i)) m ∅ 0) := by
  dsimp only
  let H := Q.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  intro hfactor htensor r a
  obtain ⟨t, ht, htu⟩ := htensor
  obtain ⟨z, _, hzu⟩ := hfactor (0 : A)
  let v := Q.map (finiteKoszulExteriorUnitZero 1 (fun _ ↦ (0 : A)) 0) ≫
    (z 0).hom.f 0
  have : IsIso (finiteKoszulExteriorUnitZero 1 (fun _ ↦ (0 : A)) 0) :=
    exteriorUnit_isIso 1 (fun _ ↦ (0 : A)) 0
  have : IsIso v := by dsimp only [v]; infer_instance
  have hv : c ≫ v = ringedNegativeKoszulFactorBasis O
      (b (0 : A)) 0 0 := by
    simpa only [v, Category.assoc] using hzu 0
  have : IsIso (c ≫ v) := by
    rw [hv]
    simp only [ringedNegativeKoszulFactorBasis, show ¬ (0 : ℤ) = -1 by decide,
      ↓reduceDIte, eqToHom_refl, Category.comp_id]
    infer_instance
  have : IsIso c := IsIso.of_isIso_comp_right c v
  induction r with
  | zero =>
    let e :=
      (HomologicalComplex.singleMapHomologicalComplex Q (.up ℤ) 0).app
        (ModuleCat.of A A) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (asIso c).symm
    refine ⟨fun _ ↦ e, ?_, ?_⟩
    · intro m
      change H.map (𝟙 _) ≫ e.hom = e.hom ≫ 𝟙 _
      simp
    · intro m
      change c ≫ Q.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of A A)).inv ≫ e.hom.f 0 =
        ringedNegativeKoszulBasis O 0 (fun i ↦ b (a i)) m ∅ 0
      dsimp only [e, Iso.trans_hom, Iso.app_hom, HomologicalComplex.comp_f,
        Functor.mapIso_hom,
        Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      simp [HomologicalComplex.single_map_f_self, ringedNegativeKoszulBasis,
        Category.assoc]
  | succ r ih =>
    obtain ⟨f, hf, hfu⟩ := hfactor (a 0)
    obtain ⟨g, hg, hgu⟩ := ih (fun i ↦ a i.succ)
    let K (m : ℕ) := completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m
    let L (m : ℕ) := finiteNegativeKoszulTensor r (fun i ↦ a i.succ) m
    let T := ringedKoszulTensor O
    let s (m : ℕ) := ((T.mapIso (f m)).app (H.obj (L m))) ≪≫
      (T.obj (ringedNegativeKoszulFactor O (b (a 0)) m)).mapIso
        (g m)
    refine ⟨fun m ↦ t (K m) (L m) ≪≫ s m, ?_, ?_⟩
    · intro m
      dsimp only [Iso.trans_hom]
      change H.map (HomologicalComplex.tensorHom
          (completedKoszulTransition 1 (fun _ ↦ a 0) m)
          (finiteNegativeKoszulTransition r (fun i ↦ a i.succ) m)) ≫
        (t (K m) (L m)).hom ≫ (s m).hom = _
      rw [← Category.assoc, ht]
      simp only [Category.assoc]
      apply congrArg ((t (K (m + 1)) (L (m + 1))).hom ≫ ·)
      dsimp only [s, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
      rw [negativeTransition_succ]
      simp only [Category.assoc]
      rw [bifunctorMap_comp, bifunctorMap_comp, hf m, hg m]
    · intro m
      dsimp only [Iso.trans_hom, HomologicalComplex.comp_f]
      change c ≫ Q.map ((ρ_ (ModuleCat.of A A)).inv ≫
          (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m ⊗ₘ
            finiteNegativeKoszulUnitZero r (fun i ↦ a i.succ) m) ≫
          HomologicalComplex.ιTensorObj (K m) (L m) 0 0 0 (by omega)) ≫
          (t (K m) (L m)).hom.f 0 ≫ (s m).hom.f 0 = _
      have hunit := congrArg (fun k ↦ k ≫ (s m).hom.f 0)
        (htu (K m) (L m) (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m)
          (finiteNegativeKoszulUnitZero r (fun i ↦ a i.succ) m))
      simp only [Category.assoc] at hunit
      rw [hunit]
      dsimp only [s, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
        HomologicalComplex.comp_f]
      rw [tensorInclusion_natural]
      dsimp only [H, K, L, Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
      rw [tensorHom_comp_tensorHom_assoc]
      rw [show (c ≫ Q.map (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m)) ≫
          (f m).hom.f 0 = ringedNegativeKoszulFactorBasis O
            (b (a 0)) m 0 by
        simpa only [Category.assoc] using hfu m]
      rw [show (c ≫ Q.map (finiteNegativeKoszulUnitZero r
          (fun i ↦ a i.succ) m)) ≫ (g m).hom.f 0 =
          ringedNegativeKoszulBasis O r
            (fun i ↦ b (a i.succ)) m ∅ 0 by
        simpa only [Category.assoc] using hgu m]
      dsimp only [T, ringedKoszulTensor, Functor.map₂HomologicalComplex, curriedTensor]
      change _ = (λ_ (SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))).inv ≫
        (ringedNegativeKoszulFactorBasis O (b (a 0)) m
            (if (0 : Fin (r + 1)) ∈ (∅ : Finset (Fin (r + 1))) then -1 else 0) ⊗ₘ
          ringedNegativeKoszulBasis O r (fun i ↦ b (a i.succ)) m
            ((∅ : Finset (Fin (r + 1))).preimage Fin.succ
              (Fin.succ_injective r).injOn)
            (0 - if (0 : Fin (r + 1)) ∈ (∅ : Finset (Fin (r + 1))) then -1 else 0)) ≫
        CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O (b (a 0)) m)
          (ringedNegativeKoszul O r (fun i ↦ b (a i.succ)) m) (curriedTensor _)
          (if (0 : Fin (r + 1)) ∈ (∅ : Finset (Fin (r + 1))) then -1 else 0)
          (0 - if (0 : Fin (r + 1)) ∈ (∅ : Finset (Fin (r + 1))) then -1 else 0)
          0 (by omega)
      rw [Finset.preimage_empty]
      dsimp only [curriedTensor]
      rfl

/-- Scalar realization of the ordered algebraic negative factors is the ordered
tensor of the explicit negative two-term factors on the completed site.
This assertion has no internal Hom or positive Koszul complex.

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul, finite free terms.
(blueprint: lem-weil-pbc-negative-koszul-tensor-realization).

Proof: in rank one use exteriorPower.zeroEquiv and exteriorPower.oneEquiv,
followed by the basis of the free module on Fin 1. Higher exterior powers vanish
because their basis index type is empty. The extended exterior complex therefore
has just A in degrees -1 and 0; contraction is multiplication by a^(m+1).
The generator transition is multiplication by a in degree -1 and identity in
degree zero. Constant sheafification and scalar extension send these free bases
to the regular coefficient sheaf, and their multiplication maps to multiplication
by the corresponding constant scalars. Restriction along the completed ring
isomorphism and reindexing along the site equivalence send these scalars to
completedCechScalar and send the prescribed coefficient unit to section 1.
Use the tensor comparison of sheafification, extension, restriction along the
ring isomorphism and reindexing on each finite total summand. These functors
preserve the required coproducts (extension and sheafification are left adjoints,
and the last two functors are equivalences). Induct on the ordered factors.
The total tensor differential, with its existing Koszul sign, is preserved on
each summand. Naturality of the tensor comparisons gives exactly the recursively
defined transitions. The comparison on the summand (0,0) sends the tensor of
the first and tail units to the tensor of their sections 1. Iterating gives
ringedNegativeKoszulBasis at the empty subset. At rank zero use the unit
comparison A[0] to O[0]. This involves no duality or exchange of tensor factors.
All formulas hold for the zero ring, empty site, and zero or unit scalars. -/
theorem negativeKoszulTensorRealization
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let G := completedKoszulConstant X (intrinsicPresentationDatum d)
    let H := (G ⋙ F).mapHomologicalComplex (.up ℤ)
    let O := completedCechRing X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∃ e : ∀ m : ℕ, H.obj (finiteNegativeKoszulTensor r a m) ≅
        ringedNegativeKoszul O r b m,
      (∀ m, H.map (finiteNegativeKoszulTransition r a m) ≫ (e m).hom =
        (e (m + 1)).hom ≫ ringedNegativeKoszulTransition O r b m) ∧
      (∀ m, completedCechCoefficientUnit X d ≫ F.map (completedKoszulOne X
          (intrinsicPresentationDatum d)) ≫ (G ⋙ F).map
            (finiteNegativeKoszulUnitZero r a m) ≫ (e m).hom.f 0 =
        ringedNegativeKoszulBasis O r b m ∅ 0) := by
  let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
  let G := completedKoszulConstant X (intrinsicPresentationDatum d)
  let Q := G ⋙ F
  let O := completedCechRing X d
  let c := completedCechCoefficientUnit X d ≫
    F.map (completedKoszulOne X (intrinsicPresentationDatum d))
  obtain ⟨e, he, hu⟩ := negativeTensorInduction O Q c (completedCechScalar X d)
    (fun x ↦ by
      obtain ⟨f, hf, hfu⟩ := negativeKoszulFactorRealization X d x
      refine ⟨f, hf, fun m ↦ ?_⟩
      simpa only [c, Category.assoc] using hfu m)
    (completedRealizationTensor X d) r a
  refine ⟨e, he, fun m ↦ ?_⟩
  simpa only [c, Category.assoc] using hu m

end AlgebraicGeometry.Scheme
