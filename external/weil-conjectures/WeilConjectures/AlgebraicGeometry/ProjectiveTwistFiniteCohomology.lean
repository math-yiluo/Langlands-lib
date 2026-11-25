/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Finite cohomology of a single projective twist over an affine base

Source: Stacks Project, Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-m4-projective-twist-finite-cohomology)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

namespace AffineTwistCech

-- All comparison data below are explicit constructions. Choosing preimages in the
-- bijectivity proof proves a proposition and does not define any sheaf or complex.

open ProjectiveSpace Scheme.Modules Opposite MvPolynomial Limits

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n]

/-- The scalar action supplied by the projective projection to `T`. -/
private noncomputable def baseRingHom (n : Type u) (T : Scheme.{u}) :
    Γ(T, ⊤) →+* Γ(ℙ(n; T), ⊤) :=
  (ℙ(n; T) ↘ T).appTop.hom

private theorem bijective_sum_awayMonomial (T : Scheme.{u}) [IsAffine T]
    {s : Set n} (hs : s.Nonempty) :
    Function.Bijective fun c : laurentExponents s 0 →₀ Γ(T, ⊤) ↦ c.sum fun e r ↦
      ((ℙ(n; T) ↘ T).appTop ≫
        ℙ(n; T).presheaf.map (homOfLE le_top).op) r *
      (Proj.awayToSection _ _ ≫ (toProjInt n T).appLE (basicOpenInt n s)
        (toProjInt n T ⁻¹ᵁ basicOpenInt n s) le_rfl)
        (awayMonomial (ULift.{u} ℤ) s e) := by
  have hdeg := indicatorDegree_pos hs
  have hf := monomialToNat_indicator_mem (ULift.{u} ℤ) s
  have hW : IsAffineOpen (basicOpenInt n s) := Proj.isAffineOpen_basicOpen _ _ hf hdeg
  have : IsAffine (basicOpenInt n s).toScheme := hW
  have hpo := isPushout_appTop_of_isPullback (isPullback_preimage n T
    (basicOpenInt n s))
  have hpo' := hpo.of_iso (Iso.refl _)
    ((basicOpenInt n s).topIso ≪≫ (Proj.basicOpenIsoAway _ _ hf hdeg).symm)
    (Iso.refl _) (toProjInt n T ⁻¹ᵁ basicOpenInt n s).topIso
    (f' := Scheme.Hom.appTop (terminal.from (basicOpenInt n s).toScheme) ≫
      (basicOpenInt n s).topIso.hom ≫
      (Proj.basicOpenIsoAway _ _ hf hdeg).inv)
    (g' := Scheme.Hom.appTop (terminal.from T))
    (inl' := Proj.awayToSection _ _ ≫ (toProjInt n T).appLE (basicOpenInt n s)
        (toProjInt n T ⁻¹ᵁ basicOpenInt n s) le_rfl)
    (inr' := (ℙ(n; T) ↘ T).appTop ≫
        ℙ(n; T).presheaf.map (homOfLE le_top).op)
    (by simp) (by simp) ?_ ?_
  · convert CommRingCat.IsPushout.bijective_sum_mul hpo' surjective_intCastRingHom_Γ_terminal
      (awayMonomialBasisInt s) using 1
    ext c
    simp
  · rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Proj.basicOpenIsoAway_hom _ _ hf hdeg, Category.assoc]
    erw [Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl

private theorem bijective_sum_twistMonomialSection (T : Scheme.{u}) [IsAffine T] {s : Set n}
    (hs : s.Nonempty) (m : ℤ) :
    Function.Bijective fun c : laurentExponents s m →₀ Γ(T, ⊤) ↦ c.sum fun e r ↦
      ((ℙ(n; T) ↘ T).appTop ≫
        ℙ(n; T).presheaf.map
          (homOfLE (le_top : toProjInt n T ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection T s e := by
  obtain ⟨i, hi⟩ := hs
  have hfun : (fun c : laurentExponents s m →₀ Γ(T, ⊤) ↦ c.sum fun e r ↦
      ((ℙ(n; T) ↘ T).appTop ≫
        ℙ(n; T).presheaf.map
          (homOfLE (le_top : toProjInt n T ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection T s e) =
      (fun r ↦ r • twistMonomialSection T s
        (Proj.singleExponent (s := s) (m := m) hi)) ∘
      (fun c : laurentExponents s 0 →₀ Γ(T, ⊤) ↦ c.sum fun e r ↦
        ((ℙ(n; T) ↘ T).appTop ≫
          ℙ(n; T).presheaf.map
          (homOfLE (le_top : toProjInt n T ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r *
        (Proj.awayToSection _ _ ≫ (toProjInt n T).appLE (basicOpenInt n s)
          (toProjInt n T ⁻¹ᵁ basicOpenInt n s) le_rfl)
          (awayMonomial (ULift.{u} ℤ) s e)) ∘
      Finsupp.equivMapDomain (shiftExponentEquiv m hi) := by
    funext c
    simp only [Function.comp_apply, Finsupp.sum_equivMapDomain]
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [twistMonomialSection_eq_smul hi e, mul_smul]
    rfl
  rw [hfun]
  exact (isFreeGenerator_twistMonomialSection_singleExponent hi).bijective.comp
    ((bijective_sum_awayMonomial T ⟨i, hi⟩).comp
      (Finsupp.domCongr (M := Γ(T, ⊤)) (shiftExponentEquiv m hi)).bijective)

variable (T : Scheme.{u}) [IsAffine T] (m : ℤ)

/-- Send monomial coefficients to sections, using the ring structure morphism. -/
private noncomputable def twistMonomialLinearMap (s : Set n) :
    (laurentExponents s m →₀ Γ(T, ⊤)) →ₗ[Γ(T, ⊤)] (ModuleCat.restrictScalars
      (baseRingHom n T)).obj
        ((twist n T m).presheafModuleCat.obj
          (op (toProjInt n T ⁻¹ᵁ basicOpenInt n s))) :=
  Finsupp.linearCombination Γ(T, ⊤) fun e ↦ twistMonomialSection T s e

variable {T m}

/-- The Laurent-monomial section basis gives bijectivity for the ring scalar map. -/
private lemma bijective_twistMonomialLinearMap {s : Set n} (hs : s.Nonempty) :
    Function.Bijective (twistMonomialLinearMap T m s) := by
  exact bijective_sum_twistMonomialSection T hs m

/-- Restriction preserves each Laurent monomial and its coefficient. -/
private lemma ring_twistMonomialLinearMap_mapDomain
    {T : Scheme.{u}} [IsAffine T] {m : ℤ} {s t : Set n} (hts : t ⊆ s)
    (c : laurentExponents t m →₀ Γ(T, ⊤)) :
    twistMonomialLinearMap T m s (c.mapDomain (Set.inclusion (laurentExponents_mono hts m))) =
      (twist n T m).presheafModuleCat.map (homOfLE ((toProjInt n _).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistMonomialLinearMap T m t c) := by
  rw [twistMonomialLinearMap, twistMonomialLinearMap, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun e _ ↦ ?_
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  erw [(((twist n T m).presheafModuleCat.map _).hom).map_smul]
  congr 1
  exact (twist_presheaf_map_twistMonomialSection hts e).symm

variable (T m) in
/-- Assemble the monomial sections over all standard intersections. -/
private noncomputable def monomialCechToCechFun (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n Γ(T, ⊤) m p) :
    ((cechComplexFunctor (standardOpen n T)).obj
      (twist n T m).presheafModuleCat).X p :=
  (ModuleCat.piIsoPi (fun σ : Fin (p + 1) → n ↦
      (twist n T m).presheafModuleCat.obj
        (op (∏ᶜ fun l ↦ standardOpen n T (σ l))))).inv fun σ ↦
    (twist n T m).presheafModuleCat.map
      (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
        (preimage_basicOpenInt_range _ σ).ge)).op
      (twistMonomialLinearMap T m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ)))

/-- The assembled section has the prescribed component on each intersection. -/
private lemma ring_cechComplexFunctorπ_monomialCechToCechFun
    {T : Scheme.{u}} [IsAffine T] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n Γ(T, ⊤) m p) (σ : Fin (p + 1) → n) :
    TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
      (twist n T m).presheafModuleCat p σ (monomialCechToCechFun T m p c) =
      (twist n T m).presheafModuleCat.map
        (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
          (preimage_basicOpenInt_range _ σ).ge)).op
        (twistMonomialLinearMap T m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ))) :=
  TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv _ _ _ σ

variable (T m) in
/-- The section comparison is linear over the base ring. -/
private noncomputable def monomialCechToCech (p : ℕ) :
    ProjectiveSpace.MonomialCechCochain n Γ(T, ⊤) m p →ₗ[Γ(T, ⊤)] (ModuleCat.restrictScalars
      (baseRingHom n T)).obj
        (((cechComplexFunctor (standardOpen n T)).obj
          (twist n T m).presheafModuleCat).X p) where
  toFun := monomialCechToCechFun T m p
  map_add' c c' := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n T)
      (twist n T m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
      (twist n T m).presheafModuleCat p σ
      (monomialCechToCechFun T m p c + monomialCechToCechFun T m p c')
    rw [map_add, ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun]
    simp only [Pi.add_apply, map_add]
  map_smul' r c := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n T)
      (twist n T m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
      (twist n T m).presheafModuleCat p σ
      (baseRingHom n T r •
        monomialCechToCechFun T m p c)
    rw [(TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
      (twist n T m).presheafModuleCat p σ).hom.map_smul,
      ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun, Pi.smul_apply,
      LinearEquiv.map_smul, LinearMap.map_smul,
      ModuleCat.restrictScalars.smul_def]
    exact ((twist n T m).presheafModuleCat.map _).hom.map_smul _ _

omit [Fintype n] in
/-- Passing from supported coefficients to subtype indices preserves coefficients. -/
private lemma ring_supportedEquivFinsupp_apply
    {T : Scheme.{u}} [IsAffine T] (s : Set (n → ℤ))
    (x : Finsupp.supported Γ(T, ⊤) Γ(T, ⊤) s) (e : s) :
    Finsupp.supportedEquivFinsupp s x e = (x : (n → ℤ) →₀ Γ(T, ⊤)) e := by
  simp

/-- The coefficient differential is the alternating face sum. -/
private lemma ring_supportedEquivFinsupp_monomialCechComplex_d
    {T : Scheme.{u}} [IsAffine T] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n Γ(T, ⊤) m p) (τ : Fin (p + 2) → n) :
    Finsupp.supportedEquivFinsupp (laurentExponents (Set.range τ) m)
        (((ProjectiveSpace.monomialCechComplex n Γ(T, ⊤) m).d p (p + 1)).hom c τ) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Finsupp.supportedEquivFinsupp (laurentExponents (Set.range (τ ∘ i.succAbove)) m)
          (c (τ ∘ i.succAbove))).mapDomain
          (Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)) := by
  ext e
  rw [ring_supportedEquivFinsupp_apply, Finsupp.finsetSum_apply]
  have h := ProjectiveSpace.monomialCechComplex_d_apply p c τ e.1
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Finsupp.smul_apply]
  congr 1
  by_cases he : e.1 ∈ laurentExponents (Set.range (τ ∘ i.succAbove)) m
  · rw [show e = Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)
        ⟨e.1, he⟩ from rfl, Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _),
      ring_supportedEquivFinsupp_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨e', he'⟩ ↦ he (he' ▸ e'.2)]
    exact ProjectiveSpace.MonomialCechCochain.coeff_eq_zero_of_notMem c _ he

/-- The monomial section comparison commutes with the Čech differentials. -/
private lemma ring_monomialCechToCechFun_d
    {T : Scheme.{u}} [IsAffine T] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n Γ(T, ⊤) m p) :
    ((cechComplexFunctor (standardOpen n T)).obj
      (twist n T m).presheafModuleCat).d p (p + 1)
        (monomialCechToCechFun T m p c) =
      monomialCechToCechFun T m (p + 1)
        (((ProjectiveSpace.monomialCechComplex n Γ(T, ⊤) m).d p (p + 1)).hom c) := by
  refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n T)
    (twist n T m).presheafModuleCat fun τ ↦ ?_
  rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, ring_cechComplexFunctorπ_monomialCechToCechFun,
    ring_supportedEquivFinsupp_monomialCechComplex_d, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : (∏ᶜ fun l ↦ standardOpen n T (τ l)) ≤
      toProjInt n T ⁻¹ᵁ basicOpenInt n (Set.range (τ ∘ i.succAbove)) :=
    (TopCat.Presheaf.piObj_le_iInf _ τ).trans ((preimage_basicOpenInt_range _ τ).ge.trans
      ((toProjInt n _).preimage_mono (Proj.basicOpen_monomialToNat_indicator_mono
        (Set.range_comp_subset_range _ _))))
  rw [ring_cechComplexFunctorπ_monomialCechToCechFun, map_zsmul, map_zsmul]
  congr 1
  rw [ring_twistMonomialLinearMap_mapDomain, TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op]
  · exact TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op _
  · exact Set.range_comp_subset_range _ _

/-- Each component comparison is bijective by the Laurent-monomial section basis. -/
private lemma bijective_monomialCechToCech (p : ℕ) :
    Function.Bijective (monomialCechToCech T m (n := n) p) := by
  have hle (σ : Fin (p + 1) → n) : toProjInt n T ⁻¹ᵁ basicOpenInt n (Set.range σ) ≤
      ∏ᶜ fun l ↦ standardOpen n T (σ l) :=
    (preimage_basicOpenInt_range _ σ).le.trans (TopCat.Presheaf.iInf_le_piObj _ σ)
  have hne (σ : Fin (p + 1) → n) : (Set.range σ).Nonempty := Set.range_nonempty σ
  constructor
  · intro c c' hcc
    change monomialCechToCechFun T m p c = monomialCechToCechFun T m p c' at hcc
    funext σ
    have hπ := congrArg (fun x ↦ (twist n T m).presheafModuleCat.map
      (homOfLE (hle σ)).op (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
        (twist n T m).presheafModuleCat p σ x)) hcc
    simp only [ring_cechComplexFunctorπ_monomialCechToCechFun] at hπ
    rw [TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _),
      TopCat.Presheaf.map_apply_self, TopCat.Presheaf.map_apply_self] at hπ
    exact (Finsupp.supportedEquivFinsupp _).injective
      ((bijective_twistMonomialLinearMap (hne σ)).1 hπ)
  · intro x
    choose y hy using fun σ : Fin (p + 1) → n ↦
      (bijective_twistMonomialLinearMap (T := T) (m := m) (hne σ)).2
        ((twist n T m).presheafModuleCat.map (homOfLE (hle σ)).op
          (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
            (twist n T m).presheafModuleCat p σ x))
    refine ⟨fun σ ↦ (Finsupp.supportedEquivFinsupp (M := Γ(T, ⊤)) (R := Γ(T, ⊤))
      (laurentExponents (Set.range σ) m)).symm (y σ), ?_⟩
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n T)
      (twist n T m).presheafModuleCat fun σ ↦ ?_
    change TopCat.Presheaf.cechComplexFunctorπ (standardOpen n T)
      (twist n T m).presheafModuleCat p σ (monomialCechToCechFun T m p _) = _
    rw [ring_cechComplexFunctorπ_monomialCechToCechFun, LinearEquiv.apply_symm_apply, hy,
      TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_apply_self]

variable (n T m) in
/-- The twist Čech complex is the monomial complex over any commutative ring. -/
private noncomputable def cechComplexTwistIso :
    ((ModuleCat.restrictScalars
        (baseRingHom n T)).mapHomologicalComplex _).obj
      ((cechComplexFunctor (standardOpen n T)).obj
        (twist n T m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n Γ(T, ⊤) m :=
  (HomologicalComplex.Hom.isoOfComponents (fun p ↦
    (LinearEquiv.ofBijective (monomialCechToCech T m p)
      (bijective_monomialCechToCech p)).toModuleIso) (by
    rintro p _ rfl
    ext c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.mapHomologicalComplex_obj_d,
      LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
    exact ring_monomialCechToCechFun_d p c)).symm

/-- Affine Čech comparison identifies ordinary twist cohomology with monomial homology. -/
private theorem nonempty_H_twist_linearEquiv_homology (T : Scheme.{u}) [IsAffine T]
    (m : ℤ) (q : ℕ) :
    letI : Module Γ(T, ⊤) ((twist n T m).H q) :=
      Module.compHom _ (ℙ(n; T) ↘ T).appTop.hom
    Nonempty ((ProjectiveSpace.twist n T m).H q ≃ₗ[Γ(T, ⊤)]
      (ProjectiveSpace.monomialCechComplex n Γ(T, ⊤) m).homology q) := by
  let : Module Γ(T, ⊤) ((twist n T m).H q) :=
    Module.compHom _ (ℙ(n; T) ↘ T).appTop.hom
  let φ := baseRingHom n T
  let K := (cechComplexFunctor (ProjectiveSpace.standardOpen n T)).obj
    (ProjectiveSpace.twist n T m).presheafModuleCat
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; T) ↘ T) (ProjectiveSpace.standardOpen n T)
    (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (ProjectiveSpace.iSup_standardOpen n _)
    (ProjectiveSpace.twist n T m) q
  let e₂ := cechComplexTwistIso n T m
  let e₃ : (ProjectiveSpace.twist n T m).H q ≃ₗ[Γ(T, ⊤)]
      (ModuleCat.restrictScalars φ).obj (K.homology q) :=
    { e₁.symm.toAddEquiv with map_smul' := fun c x ↦ e₁.symm.map_smul (φ c) x }
  exact ⟨e₃ ≪≫ₗ ((ModuleCat.restrictScalarsHomologyIso φ K q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv⟩

end AffineTwistCech

namespace ProjectiveSpace

open Limits Scheme.Modules

private def opensSiteCech (X : Scheme.{u}) {n : Type u} (U : n → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k, U (t k)
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k
      apply Subsingleton.elim
    · intro b _
      apply Subsingleton.elim
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private noncomputable def opensSiteCechIso (X : Scheme.{u}) {n : Type u} (U : n → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (opensSiteCech X U).complex F ≅ (TopCat.Presheaf.cechComplex U).obj F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro s
    funext t
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl)

/-- A finite affine cover bounds quasi-coherent cohomology on any scheme separated
 over an affine scheme. The empty cover forces the scheme to be empty. -/
private theorem finite_affine_cover_cohomology_bound {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) [IsSeparated f] (n : Type u) [Finite n] (U : n → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {q : ℕ} (hq : Nat.card n ≤ q) : Subsingleton (ℱ.H q) := by
  classical
  have := Fintype.ofFinite n
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let P := ℱ.presheafModuleCat ⋙ forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat
  obtain ⟨K, e, r, -, -, hr⟩ := Scheme.alternatingCechComputes
    X U hcover P
      (opensSiteCech _ U)
  have hempty : IsEmpty {t : Fin (q + 1) → n // StrictMono t} := by
    refine ⟨fun t ↦ ?_⟩
    have hc := Fintype.card_le_of_injective t.1 t.2.injective
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hc
    omega
  have hz : Limits.IsZero (K.X q) := by
    exact ((AddCommGrpCat.isZero_iff_subsingleton).mpr inferInstance).of_iso (e q)
  have hh : Limits.IsZero (K.homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc q) hz
  have := hr q
  have hz' : Limits.IsZero (((opensSiteCech _ U).complex P).homology q) :=
    hh.of_iso (asIso (HomologicalComplex.homologyMap r q))
  have hcech : Limits.IsZero (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    hz'.of_iso (HomologicalComplex.homologyMapIso (opensSiteCechIso _ U P) q).symm
  let ec := TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q
  have : Subsingleton (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    (AddCommGrpCat.isZero_iff_subsingleton).mp hcech
  have : Subsingleton (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :=
    ec.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  obtain ⟨el⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    f U hU hcover ℱ q
  exact el.symm.toEquiv.subsingleton

private theorem finite_negativeExponents (N : Type u) [Fintype N] (m : ℤ)
    {d : ℕ} (hN : Fintype.card N = d + 1) : Finite (negativeExponents N m) := by
  by_cases hm : m ≤ -(d : ℤ) - 1
  · have : Finite {s : N →₀ ℕ | s.degree = (-m - d - 1).toNat} :=
      (Finsupp.finite_of_degree_eq _).to_subtype
    exact Finite.of_equiv _ (negativeExponentsEquiv N m hN hm).symm
  · have : IsEmpty (negativeExponents N m) := isEmpty_negativeExponents hN (by omega)
    infer_instance

private theorem finite_monomial_homology_top (N : Type u) [Fintype N]
    (A : Type u) [CommRing A] (m : ℤ) {d : ℕ} (hN : Fintype.card N = d + 1)
    (h : d ≠ 0 ∨ m < 0) : Module.Finite A ((monomialCechComplex N A m).homology d) := by
  have : Finite (negativeExponents N m) := finite_negativeExponents N m hN
  exact Module.Finite.equiv
    (monomialCechComplexHomologyTopLinearEquiv N A m hN
      (Fintype.equivFinOfCardEq hN).symm h).symm

/-- Every twist has finite cohomology over the ring of an affine Noetherian base.

Source: Stacks Project, Tag 01XT, Lemma 30.8.1.
(blueprint: lem-pc-m4-projective-twist-finite-cohomology)

Proof: Set A = Gamma(T,O). The affine isomorphism T ≅ Spec A induces an
isomorphism of projective spaces, carrying the twist to the twist by its base-change
isomorphism. Compute cohomology by the standard affine coordinate cover. Its intersections
are affine and the twist is quasi-coherent, so the Cech-to-derived comparison applies.
Decompose the resulting complex by Laurent monomials of total degree m. A monomial with
some but not all exponents negative gives a contractible simplex complex. The remaining
summands contribute only in degree zero (all exponents nonnegative), or the top degree
(all exponents strictly negative). In each of those degrees only finitely many exponent
vectors have the prescribed total degree, so the cohomology is finite free over A.
With one coordinate the scheme is Spec A, every twist is free of rank one and positive
cohomology vanishes. With no coordinates the scheme is empty and all cohomology vanishes.
The comparison with T commutes with multiplication by every element of A, since restriction,
localization and the Cech comparison are natural for multiplication endomorphisms.
Thus the A-action is exactly restriction along the projective projection displayed below. -/
theorem finite_H_twist_affine {T : Scheme.{u}} [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (N : Type u) [Finite N] (m : ℤ) (q : ℕ) :
    letI : Module Γ(T, ⊤) ((twist N T m).H q) :=
      Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
    Module.Finite Γ(T, ⊤) ((twist N T m).H q) := by
  classical
  let : Fintype N := Fintype.ofFinite N
  let : Module Γ(T, ⊤) ((twist N T m).H q) :=
    Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
  by_cases hq : Nat.card N ≤ q
  · have : Subsingleton ((twist N T m).H q) :=
      finite_affine_cover_cohomology_bound (ℙ(N; T) ↘ T) N (standardOpen N T)
        (fun i ↦ isAffineOpen_standardOpen N T i) (iSup_standardOpen N T) _ hq
    infer_instance
  have hNpos : 0 < Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have : Nonempty N := Fintype.card_pos_iff.mp hNpos
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  obtain ⟨e⟩ := AffineTwistCech.nonempty_H_twist_linearEquiv_homology T m q (n := N)
  have hfin : Module.Finite Γ(T, ⊤) ((monomialCechComplex N Γ(T, ⊤) m).homology q) := by
    by_cases hqd : q = d
    · subst q
      by_cases hm : 0 ≤ m
      · by_cases hd0 : d = 0
        · subst d
          lift m to ℕ using hm
          have : Module.Finite Γ(T, ⊤) (MvPolynomial.homogeneousSubmodule N Γ(T, ⊤) m) :=
            Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg N Γ(T, ⊤) m)
          exact Module.Finite.equiv
            (monomialCechComplexHomologyZeroLinearEquiv N Γ(T, ⊤) m).symm
        · exact finite_monomial_homology_top N Γ(T, ⊤) m hd (.inl hd0)
      · exact finite_monomial_homology_top N Γ(T, ⊤) m hd (.inr (by omega))
    · by_cases hq0 : q = 0
      · subst q
        by_cases hm : 0 ≤ m
        · lift m to ℕ using hm
          have : Module.Finite Γ(T, ⊤) (MvPolynomial.homogeneousSubmodule N Γ(T, ⊤) m) :=
            Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg N Γ(T, ⊤) m)
          exact Module.Finite.equiv
            (monomialCechComplexHomologyZeroLinearEquiv N Γ(T, ⊤) m).symm
        · have : Nontrivial N := by
            rw [← Fintype.one_lt_card_iff_nontrivial]
            omega
          have : Subsingleton ((monomialCechComplex N Γ(T, ⊤) m).homology 0) :=
            subsingleton_monomialCechComplex_homology_zero N Γ(T, ⊤) (by omega)
          infer_instance
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
        have hz := (exactAt_monomialCechComplex N Γ(T, ⊤) m hd r (by
          rw [Nat.card_eq_fintype_card, hd] at hq
          omega)).isZero_homology
        have : Subsingleton ((monomialCechComplex N Γ(T, ⊤) m).homology (r + 1)) :=
          (ModuleCat.isZero_iff_subsingleton).mp hz
        infer_instance
  exact Module.Finite.equiv e.symm

end ProjectiveSpace
end AlgebraicGeometry
