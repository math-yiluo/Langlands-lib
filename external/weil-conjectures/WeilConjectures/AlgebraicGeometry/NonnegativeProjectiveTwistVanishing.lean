/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Positive cohomology of nonnegative projective twists over a ring -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

namespace D2TwistCech

-- All comparison data below are explicit constructions. Choosing preimages in the
-- bijectivity proof proves a proposition and does not define any sheaf or complex.

open ProjectiveSpace Scheme.Modules Opposite MvPolynomial

variable {n : Type u} [Fintype n]

/-- The scalar action supplied by the structure morphism to `Spec k`. -/
private noncomputable def baseRingHom (n : Type u) (k : Type u) [CommRing k] :
    k →+* Γ(ℙ(n; Spec (.of k)), ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop).hom

variable (k : Type u) [CommRing k] (m : ℤ)

/-- Send monomial coefficients to sections, using the ring structure morphism. -/
private noncomputable def twistMonomialLinearMap (s : Set n) :
    (laurentExponents s m →₀ k) →ₗ[k] (ModuleCat.restrictScalars
      (baseRingHom n k)).obj
        ((twist n (Spec (.of k)) m).presheafModuleCat.obj
          (op (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s))) :=
  Finsupp.linearCombination k fun e ↦ twistMonomialSection (Spec (.of k)) s e

variable {k m}

/-- The Laurent-monomial section basis gives bijectivity for the ring scalar map. -/
private lemma bijective_twistMonomialLinearMap {s : Set n} (hs : s.Nonempty) :
    Function.Bijective (twistMonomialLinearMap k m s) ∧ True := by
  exact ⟨bijective_sum_twistMonomialSection k hs m, trivial⟩

/-- Restriction preserves each Laurent monomial and its coefficient. -/
private lemma ring_twistMonomialLinearMap_mapDomain
    {n : Type u} [Fintype n] {k : Type u} [CommRing k] {m : ℤ} {s t : Set n} (hts : t ⊆ s)
    (c : laurentExponents t m →₀ k) :
    twistMonomialLinearMap k m s (c.mapDomain (Set.inclusion (laurentExponents_mono hts m))) =
      (twist n (Spec (.of k)) m).presheafModuleCat.map (homOfLE ((toProjInt n _).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistMonomialLinearMap k m t c) := by
  rw [twistMonomialLinearMap, twistMonomialLinearMap, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun e _ ↦ ?_
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  erw [(((twist n (Spec (.of k)) m).presheafModuleCat.map _).hom).map_smul]
  congr 1
  exact (twist_presheaf_map_twistMonomialSection hts e).symm

variable (k m) in
/-- Assemble the monomial sections over all standard intersections. -/
private noncomputable def monomialCechToCechFun (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
      (twist n (Spec (.of k)) m).presheafModuleCat).X p :=
  (ModuleCat.piIsoPi (fun σ : Fin (p + 1) → n ↦
      (twist n (Spec (.of k)) m).presheafModuleCat.obj
        (op (∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (σ l))))).inv fun σ ↦
    (twist n (Spec (.of k)) m).presheafModuleCat.map
      (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
        (preimage_basicOpenInt_range _ σ).ge)).op
      (twistMonomialLinearMap k m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ)))

/-- The assembled section has the prescribed component on each intersection. -/
private lemma ring_cechComplexFunctorπ_monomialCechToCechFun
    {n : Type u} [Fintype n] {k : Type u} [CommRing k] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (σ : Fin (p + 1) → n) :
    TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ (monomialCechToCechFun k m p c) =
      (twist n (Spec (.of k)) m).presheafModuleCat.map
        (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
          (preimage_basicOpenInt_range _ σ).ge)).op
        (twistMonomialLinearMap k m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ))) :=
  TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv _ _ _ σ

variable (k m) in
/-- The section comparison is linear over the base ring. -/
private noncomputable def monomialCechToCech (p : ℕ) :
    ProjectiveSpace.MonomialCechCochain n k m p →ₗ[k] (ModuleCat.restrictScalars
      (baseRingHom n k)).obj
        (((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
          (twist n (Spec (.of k)) m).presheafModuleCat).X p) where
  toFun := monomialCechToCechFun k m p
  map_add' c c' := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ
      (monomialCechToCechFun k m p c + monomialCechToCechFun k m p c')
    rw [map_add, ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun]
    simp only [Pi.add_apply, map_add]
  map_smul' r c := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ
      (baseRingHom n k r •
        monomialCechToCechFun k m p c)
    rw [(TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ).hom.map_smul,
      ring_cechComplexFunctorπ_monomialCechToCechFun,
      ring_cechComplexFunctorπ_monomialCechToCechFun, Pi.smul_apply,
      LinearEquiv.map_smul, LinearMap.map_smul,
      ModuleCat.restrictScalars.smul_def]
    exact ((twist n (Spec (.of k)) m).presheafModuleCat.map _).hom.map_smul _ _

/-- Passing from supported coefficients to subtype indices preserves coefficients. -/
private lemma ring_supportedEquivFinsupp_apply
    {n : Type u} {k : Type u} [CommRing k] (s : Set (n → ℤ))
    (x : Finsupp.supported k k s) (e : s) :
    Finsupp.supportedEquivFinsupp s x e = (x : (n → ℤ) →₀ k) e := by
  simp

/-- The coefficient differential is the alternating face sum. -/
private lemma ring_supportedEquivFinsupp_monomialCechComplex_d
    {n : Type u} [Fintype n] {k : Type u} [CommRing k] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (τ : Fin (p + 2) → n) :
    Finsupp.supportedEquivFinsupp (laurentExponents (Set.range τ) m)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c τ) =
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
    {n : Type u} [Fintype n] {k : Type u} [CommRing k] {m : ℤ} (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
      (twist n (Spec (.of k)) m).presheafModuleCat).d p (p + 1)
        (monomialCechToCechFun k m p c) =
      monomialCechToCechFun k m (p + 1)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c) := by
  refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
    (twist n (Spec (.of k)) m).presheafModuleCat fun τ ↦ ?_
  rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, ring_cechComplexFunctorπ_monomialCechToCechFun,
    ring_supportedEquivFinsupp_monomialCechComplex_d, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : (∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (τ l)) ≤
      toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n (Set.range (τ ∘ i.succAbove)) :=
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
    Function.Bijective (monomialCechToCech k m (n := n) p) ∧ True := by
  constructor
  · have hle (σ : Fin (p + 1) → n) : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n (Set.range σ) ≤
        ∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (σ l) :=
      (preimage_basicOpenInt_range _ σ).le.trans (TopCat.Presheaf.iInf_le_piObj _ σ)
    have hne (σ : Fin (p + 1) → n) : (Set.range σ).Nonempty := Set.range_nonempty σ
    constructor
    · intro c c' hcc
      change monomialCechToCechFun k m p c = monomialCechToCechFun k m p c' at hcc
      funext σ
      have hπ := congrArg (fun x ↦ (twist n (Spec (.of k)) m).presheafModuleCat.map
        (homOfLE (hle σ)).op (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
          (twist n (Spec (.of k)) m).presheafModuleCat p σ x)) hcc
      simp only [ring_cechComplexFunctorπ_monomialCechToCechFun] at hπ
      rw [TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _),
        TopCat.Presheaf.map_apply_self, TopCat.Presheaf.map_apply_self] at hπ
      exact (Finsupp.supportedEquivFinsupp _).injective
        (((bijective_twistMonomialLinearMap (hne σ)).1).1 hπ)
    · intro x
      choose y hy using fun σ : Fin (p + 1) → n ↦
        ((bijective_twistMonomialLinearMap (k := k) (m := m) (hne σ)).1).2
          ((twist n (Spec (.of k)) m).presheafModuleCat.map (homOfLE (hle σ)).op
            (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
              (twist n (Spec (.of k)) m).presheafModuleCat p σ x))
      refine ⟨fun σ ↦ (Finsupp.supportedEquivFinsupp (M := k) (R := k)
        (laurentExponents (Set.range σ) m)).symm (y σ), ?_⟩
      refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
        (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
      change TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
        (twist n (Spec (.of k)) m).presheafModuleCat p σ (monomialCechToCechFun k m p _) = _
      rw [ring_cechComplexFunctorπ_monomialCechToCechFun, LinearEquiv.apply_symm_apply, hy,
        TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_apply_self]
  · trivial

variable (n k m) in
/-- The twist Čech complex is the monomial complex over any commutative ring. -/
private noncomputable def cechComplexTwistIso :
    ((ModuleCat.restrictScalars
        (baseRingHom n k)).mapHomologicalComplex _).obj
      ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
        (twist n (Spec (.of k)) m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n k m :=
  (HomologicalComplex.Hom.isoOfComponents (fun p ↦
    (LinearEquiv.ofBijective (monomialCechToCech k m p)
      (bijective_monomialCechToCech p).1).toModuleIso) (by
    rintro p _ rfl
    ext c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.mapHomologicalComplex_obj_d,
      LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
    exact ring_monomialCechToCechFun_d p c)).symm

/-- Affine Čech comparison identifies ordinary twist cohomology with monomial homology. -/
private theorem nonempty_H_twist_addEquiv_homology (A : Type u) [CommRing A]
    (m : ℤ) (q : ℕ) :
    Nonempty ((ProjectiveSpace.twist n (Spec (.of A)) m).H q ≃+
      (ProjectiveSpace.monomialCechComplex n A m).homology q) := by
  let φ := baseRingHom n A
  let K := (cechComplexFunctor (ProjectiveSpace.standardOpen n (Spec (.of A)))).obj
    (ProjectiveSpace.twist n (Spec (.of A)) m).presheafModuleCat
  obtain ⟨e₁⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (ProjectiveSpace.standardOpen n (Spec (.of A)))
    (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (ProjectiveSpace.iSup_standardOpen n _)
    (ProjectiveSpace.twist n (Spec (.of A)) m) q
  let e₂ := cechComplexTwistIso n A m
  let e₃ : (ProjectiveSpace.twist n (Spec (.of A)) m).H q ≃+
      (ModuleCat.restrictScalars φ).obj (K.homology q) := e₁.symm.toAddEquiv
  exact ⟨e₃.trans ((ModuleCat.restrictScalarsHomologyIso φ K q).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso e₂).toLinearEquiv.toAddEquiv⟩

end D2TwistCech

namespace Scheme.Modules

/-- Nonnegative twists have no positive cohomology over any commutative ring.
Source: Stacks Project, Tag 01XT, the projective-space twist computation.
(blueprint: lem-pc-d2-nonnegative-projective-twist-vanishing)

Proof: The standard affine coordinate cover computes cohomology, since the twist is
quasi-coherent and all finite intersections are affine. Identify its Cech complex with
the Laurent-monomial complex of total degree m using the local bases of O(m).
For each exponent vector having a nonnegative coordinate, inserting that coordinate
contracts the positive-degree complex of allowed intersections. The only possible
remaining positive-degree classes have all N+1 exponents strictly negative, and hence
strictly negative total degree. This is impossible for m ≥ 0. Thus ordinary sheaf
cohomology is zero in every positive degree; the comparison with module right-derived
sections gives IsZero. For N=0 the same contraction applies to the one-coordinate cover
(and projective space is affine). The zero ring also causes no exception, as every
coefficient module and every term is zero. -/
theorem isZero_moduleCohomology_projective_twist_of_nonneg
    (A : Type u) [CommRing A] (N : ℕ) (m : ℤ) (hm : 0 ≤ m)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((RingedSpace.moduleCohomology
      (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).toRingedSpace q).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) m)) := by
  classical
  let n := ULift.{u} (Fin (N + 1))
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have hex : (ProjectiveSpace.monomialCechComplex n A m).ExactAt (p + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro c hc
    refine ⟨ProjectiveSpace.monomialCechHomotopy p c,
      ProjectiveSpace.MonomialCechCochain.ext_coeff fun σ e ↦ ?_⟩
    change ProjectiveSpace.MonomialCechCochain.coeff (m := m)
      ((ProjectiveSpace.monomialCechComplex n A m).d p (p + 1)
        (ProjectiveSpace.monomialCechHomotopy p c)) σ e = c.coeff σ e
    by_cases he : ∃ i, 0 ≤ e i
    · have hc' : (ProjectiveSpace.monomialCechComplex n A m).d (p + 1) (p + 2) c = 0 := hc
      rw [← ProjectiveSpace.monomialCechComplex_d_homotopy_add p c σ he, hc', map_zero]
      exact (add_zero _).symm
    · have hneg : ∀ i, e i < 0 := by simpa using he
      have hsum : ∑ i, e i < 0 := Finset.sum_neg (fun i _ ↦ hneg i) (by simp [n])
      have hne : ∑ i, e i ≠ m := by omega
      rw [c.coeff_eq_zero_of_sum_ne σ hne,
        ProjectiveSpace.monomialCechComplex_d_apply]
      simp [ProjectiveSpace.monomialCechHomotopy_coeff_of_forall _ _ hneg]
  have : Subsingleton ((ProjectiveSpace.monomialCechComplex n A m).homology (p + 1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp hex.isZero_homology
  obtain ⟨e⟩ := D2TwistCech.nonempty_H_twist_addEquiv_homology (n := n) A m (p + 1)
  have : Subsingleton ((ProjectiveSpace.twist n (Spec (.of A)) m).H (p + 1)) :=
    e.toEquiv.subsingleton
  obtain ⟨em, _⟩ := exists_moduleCohomology_source_comparison ℙ(n; Spec (.of A)) (p + 1)
  exact (ModuleCat.isZero_iff_subsingleton).mpr (em _).toEquiv.subsingleton

end Scheme.Modules

end AlgebraicGeometry
