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
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedRealizationRegularSupplement
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Realization of a single exterior Koszul factor

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW;
algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(blueprint: lem-weil-pbc-negative-koszul-factor-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private def rankOneNegativeIso {A : Type (u + 1)} [CommRing A] (a : A) (m : ℕ) :
    (completedKoszulPower (A := A) 1 (fun _ ↦ a) m).X (-1) ≅ ModuleCat.of A A :=
  ((ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a ^ (m + 1))).extendXIso
    ComplexShape.embeddingDownNat (i := 1) (by rfl)) ≪≫
    (exteriorPower.oneEquiv A (Fin 1 →₀ A)).toModuleIso ≪≫
    (Finsupp.uniqueLinearEquiv A A (0 : Fin 1)).toModuleIso

private def rankOneZeroIso {A : Type (u + 1)} [CommRing A] (a : A) (m : ℕ) :
    (completedKoszulPower (A := A) 1 (fun _ ↦ a) m).X 0 ≅ ModuleCat.of A A :=
  ((ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a ^ (m + 1))).extendXIso
    ComplexShape.embeddingDownNat (i := 0) rfl) ≪≫
    (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).toModuleIso

private theorem rankOne_isZero {A : Type (u + 1)} [CommRing A]
    (a : A) (m : ℕ) (i : ℤ) (hi : i ≠ -1) (hi0 : i ≠ 0) :
    IsZero ((completedKoszulPower (A := A) 1 (fun _ ↦ a) m).X i) := by
  classical
  by_cases hp : 0 < i
  · apply HomologicalComplex.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ i
    omega
  · let q := (-i).toNat
    have hq : ComplexShape.embeddingDownNat.f q = i := by
      change -(q : ℤ) = i
      dsimp [q]
      omega
    have hqpos : 1 < q := by dsimp [q]; omega
    have : IsEmpty (Set.powersetCard (Fin 1) q) := ⟨fun s ↦ by
      have h := Finset.card_le_univ s.val
      have hs : s.val.card = q := s.property
      simp only [Fintype.card_fin, hs] at h
      omega⟩
    let b := (Finsupp.basisSingleOne :
      Module.Basis (Fin 1) A (Fin 1 →₀ A)).exteriorPower q
    have : Subsingleton (⋀[A]^q (Fin 1 →₀ A)) := b.repr.injective.subsingleton
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of A (⋀[A]^q (Fin 1 →₀ A)))).of_iso
      ((ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat hq)

private theorem rankOne_boundary {A : Type (u + 1)} [CommRing A] (a : A) (m : ℕ) :
    (rankOneNegativeIso a m).inv ≫
        (completedKoszulPower (A := A) 1 (fun _ ↦ a) m).d (-1) 0 ≫
        (rankOneZeroIso a m).hom =
      ModuleCat.ofHom (LinearMap.mul A A (a ^ (m + 1))) := by
  rw [show (completedKoszulPower (A := A) 1 (fun _ ↦ a) m).d (-1) 0 =
      _ from (ExteriorAlgebra.koszulComplex A 1 (fun _ ↦ a ^ (m + 1))).extend_d_eq
        ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl]
  dsimp only [rankOneNegativeIso, rankOneZeroIso, Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (exteriorPower.zeroEquiv A (Fin 1 →₀ A))
    (ExteriorAlgebra.koszulBoundary A 1 (fun _ ↦ a ^ (m + 1)) 0
      ((exteriorPower.oneEquiv A (Fin 1 →₀ A)).symm (Finsupp.single 0 x))) =
        a ^ (m + 1) * x
  apply (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).symm.injective
  apply Subtype.ext
  simp [ExteriorAlgebra.koszulBoundary, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.zeroEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply,
    CliffordAlgebra.contractLeft_ι, Algebra.smul_def, map_mul, map_pow, mul_comm]

private theorem rankOne_transition_negative {A : Type (u + 1)} [CommRing A]
    (a : A) (m : ℕ) :
    (rankOneNegativeIso a (m + 1)).inv ≫
        (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m).f (-1) ≫
        (rankOneNegativeIso a m).hom =
      ModuleCat.ofHom (LinearMap.mul A A a) := by
  unfold completedKoszulTransition
  erw [HomologicalComplex.extendMap_f _ _ (i := 1) (i' := -1) rfl]
  dsimp only [rankOneNegativeIso, Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  change (Finsupp.uniqueLinearEquiv A A (0 : Fin 1)).toLinearMap.comp
      ((exteriorPower.oneEquiv A (Fin 1 →₀ A)).toLinearMap.comp
        ((exteriorPower.map 1 (completedKoszulGenerator 1 (fun _ ↦ a))).comp
          ((exteriorPower.oneEquiv A (Fin 1 →₀ A)).symm.toLinearMap.comp
            (Finsupp.uniqueLinearEquiv A A (0 : Fin 1)).symm.toLinearMap))) = _
  have hn := exteriorPower.oneEquiv_naturality
    (completedKoszulGenerator (A := A) 1 (fun _ ↦ a))
  change (exteriorPower.oneEquiv A (Fin 1 →₀ A)).toLinearMap.comp
      (exteriorPower.map 1 (completedKoszulGenerator 1 (fun _ ↦ a))) = _ at hn
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hn
    ((exteriorPower.oneEquiv A (Fin 1 →₀ A)).symm
      ((Finsupp.uniqueLinearEquiv A A (0 : Fin 1)).symm x))
  dsimp only [LinearMap.comp_apply] at hx ⊢
  refine (congrArg (Finsupp.uniqueLinearEquiv A A (0 : Fin 1)) hx).trans ?_
  simp [completedKoszulGenerator, Finsupp.uniqueLinearEquiv, mul_comm]

private theorem rankOne_transition_zero {A : Type (u + 1)} [CommRing A]
    (a : A) (m : ℕ) :
    (rankOneZeroIso a (m + 1)).inv ≫
        (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m).f 0 ≫
        (rankOneZeroIso a m).hom = 𝟙 _ := by
  unfold completedKoszulTransition
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl]
  dsimp only [rankOneZeroIso, Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  change (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).toLinearMap.comp
      ((exteriorPower.map 0 (completedKoszulGenerator 1 (fun _ ↦ a))).comp
        (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).symm.toLinearMap) = _
  have hn := exteriorPower.zeroEquiv_naturality
    (completedKoszulGenerator (A := A) 1 (fun _ ↦ a))
  change (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).toLinearMap.comp
      (exteriorPower.map 0 (completedKoszulGenerator 1 (fun _ ↦ a))) = _ at hn
  rw [← LinearMap.comp_assoc, hn]
  exact (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).comp_symm

private theorem rankOne_unit {A : Type (u + 1)} [CommRing A] (a : A) (m : ℕ) :
    finiteKoszulExteriorUnitZero 1 (fun _ ↦ a) m ≫ (rankOneZeroIso a m).hom = 𝟙 _ := by
  dsimp only [finiteKoszulExteriorUnitZero, rankOneZeroIso, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (exteriorPower.zeroEquiv A (Fin 1 →₀ A)).toModuleIso.inv_hom_id

attribute [local irreducible] completedKoszulPower completedKoszulTransition
  finiteKoszulExteriorUnitZero rankOneNegativeIso rankOneZeroIso

private theorem realizeRankOne
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u + 1}) {A : Type (u + 1)} [CommRing A]
    (Q : ModuleCat.{u + 1} A ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    [Q.PreservesZeroMorphisms]
    (c : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) ⟶
      Q.obj (ModuleCat.of A A)) [IsIso c] (a : A)
    (b : (O.obj ⋙ CategoryTheory.forget CommRingCat.{u + 1}).sections)
    (hc : ∀ n : ℕ, c ≫ Q.map (ModuleCat.ofHom (LinearMap.mul A A (a ^ n))) =
      ((ringedKoszulScalar O b) ^ n).asHom ≫ c) :
    let H := Q.mapHomologicalComplex (.up ℤ)
    ∃ e : ∀ m : ℕ, H.obj (completedKoszulPower (A := A) 1 (fun _ ↦ a) m) ≅
        ringedNegativeKoszulFactor O b m,
      (∀ m, H.map (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m) ≫
        (e m).hom = (e (m + 1)).hom ≫ ringedNegativeKoszulFactorTransition O b m) ∧
      (∀ m, c ≫ Q.map (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a) m) ≫
        (e m).hom.f 0 = ringedNegativeKoszulFactorBasis O b m 0) := by
  let H := Q.mapHomologicalComplex (.up ℤ)
  let K (m : ℕ) := completedKoszulPower (A := A) 1 (fun _ ↦ a) m
  have hd (m : ℕ) : c ≫ Q.map (rankOneNegativeIso a m).inv ≫ Q.map ((K m).d (-1) 0) =
      ((ringedKoszulScalar O b) ^ (m + 1)).asHom ≫ c ≫ Q.map (rankOneZeroIso a m).inv := by
    have h : (rankOneNegativeIso a m).inv ≫ (K m).d (-1) 0 =
        ModuleCat.ofHom (LinearMap.mul A A (a ^ (m + 1))) ≫
          (rankOneZeroIso a m).inv := by
      apply (cancel_mono (rankOneZeroIso a m).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        rankOne_boundary a m
    rw [← Q.map_comp, h, Q.map_comp, ← Category.assoc, hc]
    simp only [Category.assoc]
  let v (m : ℕ) : ringedNegativeKoszulFactor O b m ⟶ H.obj (K m) :=
    HomologicalComplex.mkHomFromDouble (c := .up ℤ) (i₀ := -1) (i₁ := 0)
      (by decide) (by decide)
      (c ≫ Q.map (rankOneNegativeIso a m).inv)
      (c ≫ Q.map (rankOneZeroIso a m).inv) (hd m) (by
        intro k hk
        have hk1 : k = 1 := by change (0 : ℤ) + 1 = k at hk; omega
        subst k
        exact (Q.map_isZero (rankOne_isZero a m 1 (by decide) (by decide))).eq_of_tgt _ _)
  have vi (m : ℕ) : IsIso (v m) := by
    have (i : ℤ) : IsIso ((v m).f i) := by
      by_cases hi : i = -1
      · subst i
        dsimp only [v]
        rw [HomologicalComplex.mkHomFromDouble_f₀]
        infer_instance
      · by_cases hi0 : i = 0
        · subst i
          dsimp only [v]
          rw [HomologicalComplex.mkHomFromDouble_f₁]
          infer_instance
        · exact (HomologicalComplex.isZero_double_X _ _ i hi hi0).isIso
            (Q.map_isZero (rankOne_isZero a m i hi hi0)) _
    exact HomologicalComplex.Hom.isIso_of_components (v m)
  have htneg (m : ℕ) : c ≫ Q.map (rankOneNegativeIso a (m + 1)).inv ≫
      Q.map ((completedKoszulTransition (A := A) 1 (fun _ ↦ a) m).f (-1)) =
        (ringedKoszulScalar O b).asHom ≫ c ≫ Q.map (rankOneNegativeIso a m).inv := by
    have h : (rankOneNegativeIso a (m + 1)).inv ≫
        (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m).f (-1) =
          ModuleCat.ofHom (LinearMap.mul A A a) ≫ (rankOneNegativeIso a m).inv := by
      apply (cancel_mono (rankOneNegativeIso a m).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        rankOne_transition_negative a m
    have hc1 : c ≫ Q.map (ModuleCat.ofHom (LinearMap.mul A A a)) =
        (ringedKoszulScalar O b).asHom ≫ c := by simpa only [pow_one] using hc 1
    rw [← Q.map_comp, h, Q.map_comp, ← Category.assoc, hc1]
    simp only [Category.assoc]
  have htzero (m : ℕ) : Q.map (rankOneZeroIso a (m + 1)).inv ≫
      Q.map ((completedKoszulTransition (A := A) 1 (fun _ ↦ a) m).f 0) =
        Q.map (rankOneZeroIso a m).inv := by
    rw [← Q.map_comp]
    congr 1
    apply (cancel_mono (rankOneZeroIso a m).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id] using rankOne_transition_zero a m
  let e (m : ℕ) := (asIso (v m)).symm
  refine ⟨e, ?_, ?_⟩
  · intro m
    apply (cancel_epi (v (m + 1))).mp
    apply (cancel_mono (v m)).mp
    dsimp only [e, Iso.symm_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
    apply HomologicalComplex.from_double_hom_ext
    · simp only [HomologicalComplex.comp_f, v,
        HomologicalComplex.mkHomFromDouble_f₀,
        Functor.mapHomologicalComplex_map_f, Category.assoc]
      simp only [ringedNegativeKoszulFactorTransition,
        ringedNegativeKoszulFactorTransitionF, ↓reduceDIte, eqToHom_refl,
        Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
      rw [htneg]
    · simp only [HomologicalComplex.comp_f, v,
        HomologicalComplex.mkHomFromDouble_f₁,
        Functor.mapHomologicalComplex_map_f, Category.assoc]
      simp only [ringedNegativeKoszulFactorTransition,
        ringedNegativeKoszulFactorTransitionF, show ¬ (0 : ℤ) = -1 by decide,
        ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [htzero]
  · intro m
    apply (cancel_mono ((v m).f 0)).mp
    dsimp only [e, Iso.symm_hom, asIso_inv]
    simp only [HomologicalComplex.Hom.inv_f_apply, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    dsimp only [v]
    rw [HomologicalComplex.mkHomFromDouble_f₁]
    simp only [ringedNegativeKoszulFactorBasis, show ¬ (0 : ℤ) = -1 by decide,
      ↓reduceDIte, eqToHom_refl, Category.comp_id, Iso.inv_hom_id_assoc]
    have hu : finiteKoszulExteriorUnitZero 1 (fun _ ↦ a) m =
        (rankOneZeroIso a m).inv := by
      apply (cancel_mono (rankOneZeroIso a m).hom).mp
      simpa using rankOne_unit a m
    rw [hu]

private theorem scalar_power
    {D : Type*} [Category D] {A : Type (u + 1)} [CommRing A]
    (Q : ModuleCat.{u + 1} A ⥤ D) {U : D} (c : U ⟶ Q.obj (ModuleCat.of A A))
    (a : A) (s : End U)
    (hc : c ≫ Q.map (ModuleCat.ofHom (LinearMap.mul A A a)) = s.asHom ≫ c) (n : ℕ) :
    c ≫ Q.map (ModuleCat.ofHom (LinearMap.mul A A (a ^ n))) = (s ^ n).asHom ≫ c := by
  induction n with
  | zero =>
    have hmul : ModuleCat.ofHom (LinearMap.mul A A (a ^ 0)) =
        𝟙 (ModuleCat.of A A) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp
    rw [hmul, Q.map_id]
    simp
  | succ n ih =>
    have hmul : ModuleCat.ofHom (LinearMap.mul A A (a ^ (n + 1))) =
        ModuleCat.ofHom (LinearMap.mul A A (a ^ n)) ≫
          ModuleCat.ofHom (LinearMap.mul A A a) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [pow_succ, mul_assoc, mul_comm a]
    rw [hmul, Q.map_comp, ← Category.assoc, ih, Category.assoc, hc]
    rw [pow_succ', End.mul_asHom, Category.assoc]

/-- The rank-one exterior complex realizes as the explicit negative two-term factor.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free factors; Modules on Sites,
Tags 03D8, 03EK and 0GMW for constant sheafification and scalar extension.
(blueprint: lem-weil-pbc-negative-koszul-factor-realization).

Proof: the basis of A^(Fin 1) identifies its first exterior power with A;
exteriorPower.zeroEquiv identifies its zeroth power with A. All higher powers
have empty exterior basis and are zero. Reindexing gives a complex supported in
-1 and 0. Contraction sends the first basis vector to a^(m+1), and the exterior
transition is a in degree -1 and identity in degree zero. Constant sheafification
and extension of scalars carry these two bases to the regular coefficient module.
Restriction along the completed coefficient ring isomorphism and the site
equivalence carry scalar a to completedCechScalar X d a. Thus the degreewise
basis maps form the required chain isomorphism and intertwine the transitions.
The exterior degree-zero unit is 1, and the two coefficient units are sections 1,
so its composite is exactly the specified degree-zero double-complex inclusion.
There is no tensor induction, duality, or internal Hom in this assertion. The
argument uses no nonzero scalar and applies to the zero ring and empty site. -/
theorem negativeKoszulFactorRealization
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (a : A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let G := completedKoszulConstant X (intrinsicPresentationDatum d)
    let Q := G ⋙ F
    let H := Q.mapHomologicalComplex (.up ℤ)
    let O := completedCechRing X d
    let b := completedCechScalar X d a
    ∃ e : ∀ m : ℕ, H.obj (completedKoszulPower (A := A) 1 (fun _ ↦ a) m) ≅
        ringedNegativeKoszulFactor O b m,
      (∀ m, H.map (completedKoszulTransition (A := A) 1 (fun _ ↦ a) m) ≫
        (e m).hom = (e (m + 1)).hom ≫ ringedNegativeKoszulFactorTransition O b m) ∧
      (∀ m, completedCechCoefficientUnit X d ≫ F.map (completedKoszulOne X
          (intrinsicPresentationDatum d)) ≫ Q.map
            (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a) m) ≫ (e m).hom.f 0 =
        ringedNegativeKoszulFactorBasis O b m 0) := by
  let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
  let Q := completedKoszulConstant X (intrinsicPresentationDatum d) ⋙ F
  let c := completedCechCoefficientUnit X d ≫
    F.map (completedKoszulOne X (intrinsicPresentationDatum d))
  obtain ⟨hci, hc⟩ := completedRealizationRegular X d
  have : IsIso c := hci
  exact realizeRankOne (completedCechRing X d) Q c a (completedCechScalar X d a)
    (scalar_power Q c a _ (hc a))

end AlgebraicGeometry.Scheme
