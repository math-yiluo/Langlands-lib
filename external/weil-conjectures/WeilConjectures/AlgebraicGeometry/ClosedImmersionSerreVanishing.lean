/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-! # Serre vanishing for the restricted projective-space twists

Source: Stacks Project, Tags 01XS, 01YS (4), and 0B5T (4).
(blueprint: lem-weil-pbc-closed-immersion-serre-vanishing)

The private Čech comparison adapts the construction in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections` from fields to rings.
Its Laurent-monomial section basis already works over any commutative ring. We use the
explicit structure ring homomorphism, rather than the field-only `globalSectionsRingHom`.
The private Serre induction likewise adapts the field proof in
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre`; the finite twist presentation and the
cohomological degree bound already apply over Noetherian rings.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

namespace RingTwistCech

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

omit [Fintype n] in
/-- Nonnegative twists have zero positive cohomology, by the monomial calculation. -/
private theorem subsingleton_H_twist_of_pos (A : Type u) [CommRing A]
    [Finite n] {N : ℕ} (hn : Nat.card n = N + 1) {q : ℕ} (hq : 0 < q)
    {m : ℤ} (hm : 0 ≤ m) :
    Subsingleton ((ProjectiveSpace.twist n (Spec (.of A)) m).H q) := by
  have := Fintype.ofFinite n
  by_cases hqN : q = N
  · subst q
    obtain ⟨e⟩ := nonempty_H_twist_addEquiv_homology (n := n) A m N
    have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_top (n := n) (A := A) (m := m)
      (by rwa [← Nat.card_eq_fintype_card]) hq.ne' (by omega)
    exact e.toEquiv.subsingleton
  · rcases lt_or_gt_of_ne hqN with hlt | hlt
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      obtain ⟨e⟩ := nonempty_H_twist_addEquiv_homology (n := n) A m (q + 1)
      have hz := (ProjectiveSpace.exactAt_monomialCechComplex n A m
        (by rwa [← Nat.card_eq_fintype_card]) q hlt).isZero_homology
      have : Subsingleton ((ProjectiveSpace.monomialCechComplex n A m).homology (q + 1)) :=
        (ModuleCat.isZero_iff_subsingleton).mp hz
      exact e.toEquiv.subsingleton
    · exact ProjectiveSpace.subsingleton_H_of_lt n A hn _ hlt

/-- Serre vanishing over a Noetherian ring, by descending induction for all modules at once. -/
private theorem exists_subsingleton_H_tensor_twist (A : Type u) [CommRing A]
    [IsNoetherianRing A] (N : ℕ) (F : (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, 0 < q →
      Subsingleton ((F ⊗ ProjectiveSpace.twist (ULift.{u} (Fin (N + 1)))
        (Spec (.of A)) d).H q) := by
  let n := ULift.{u} (Fin (N + 1))
  have hn : Nat.card n = N + 1 := by simp [n]
  suffices key : ∀ j : ℕ, ∀ (G : (ℙ(n; Spec (.of A))).Modules)
      [G.IsQuasicoherent] [G.IsFinitePresentation],
      ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ q : ℕ, N < q + j → 0 < q →
        Subsingleton ((G ⊗ ProjectiveSpace.twist n (Spec (.of A)) d).H q) by
    obtain ⟨d₀, h⟩ := key (N + 1) F
    exact ⟨d₀, fun d hd q hq ↦ h d hd q (by omega) hq⟩
  intro j
  induction j with
  | zero =>
    intro G _ _
    refine ⟨0, fun d _ q hq _ ↦ ?_⟩
    have := isQuasicoherent_tensorObj G (ProjectiveSpace.twist n (Spec (.of A)) d)
    exact ProjectiveSpace.subsingleton_H_of_lt n A hn _ (by omega)
  | succ j ih =>
    intro G _ _
    obtain ⟨ι, _, m, f, hf, hK₁, hK₂⟩ := ProjectiveSpace.exists_epi_sigma_twist A G
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    obtain ⟨d₁, h₁⟩ := ih G
    obtain ⟨d₂, h₂⟩ := ih (kernel f)
    refine ⟨max (max d₁ d₂) (M : ℤ), fun d hd q hq hq0 ↦ ?_⟩
    have hd₁ : d₁ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hd₂ : d₂ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hdm : ∀ i, (m i : ℤ) ≤ d := fun i ↦
      le_trans (Nat.cast_le.mpr (hM ⟨i, rfl⟩)) (le_trans (le_max_right _ _) hd)
    by_cases hqj : N < q + j
    · exact h₁ d hd₁ q hqj hq0
    let T := ProjectiveSpace.twist n (Spec (.of A)) d
    obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A)) d (-d)
    let E := BraidedCategory.tensorRightEquivalence T
      (ProjectiveSpace.twist n (Spec (.of A)) (-d))
      (e₁ ≪≫ eqToIso (congrArg _ (add_neg_cancel d)) ≪≫
        (ProjectiveSpace.unitIsoTwistZero n (Spec (.of A))).symm)
    have : (tensorRight T).IsEquivalence := E.isEquivalence_functor
    have hS : (ShortComplex.kernelSequence f).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact f) inferInstance hf
    have hS' := hS.map_of_exact (tensorRight T)
    let B := fun i ↦ ProjectiveSpace.twist n (Spec (.of A)) (-(m i : ℤ))
    have : ∀ i, Subsingleton ((B i ⊗ T).H q) := fun i ↦ by
      obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso n (Spec (.of A))
        (-(m i : ℤ)) d
      have := subsingleton_H_twist_of_pos A hn hq0 (m := -(m i : ℤ) + d)
        (by have := hdm i; omega)
      exact subsingleton_H_of_iso e.symm q
    have hsum : Subsingleton ((∐ fun i ↦ B i ⊗ T).H q) :=
      subsingleton_H_sigma (fun i ↦ B i ⊗ T) q
    have h₂' : Subsingleton (((tensorRight T).obj (kernel f)).H (q + 1)) :=
      h₂ d hd₂ (q + 1) (by omega) (by omega)
    have h₃ : Subsingleton (((tensorRight T).obj (∐ B)).H q) :=
      @subsingleton_H_of_iso _ _ _ (PreservesCoproduct.iso (tensorRight T) B).symm q hsum
    exact @subsingleton_H_of_shortExact _ _ hS' q h₃ h₂'

end RingTwistCech

namespace Scheme.Modules

/-- Serre vanishing for a finitely presented quasi-coherent module on a closed subscheme
of finite-dimensional projective space over a Noetherian ring.
Source: Stacks Project, Cohomology of Schemes, Tags 01YS and 0B5T (4).
(blueprint: lem-weil-pbc-closed-immersion-serre-vanishing)

Proof: Projective space is locally Noetherian, and its closed subscheme X is locally
Noetherian. Hence F and i_*F are coherent. For G = i_*F, choose an epimorphism from a
finite direct sum of negative twists to G; its kernel is coherent. The standard affine
cover by N+1 opens computes quasi-coherent cohomology, and gives vanishing above degree N.
Descend in cohomological degree, for all coherent G at once. Tensor the epimorphism and
its kernel sequence by O(t), which is invertible and therefore preserves exactness.
Positive-degree cohomology of each summand O(t-a) vanishes once t is sufficiently large;
this follows from the monomial Cech computation of nonnegative twists, valid over any
base ring. The next-degree cohomology of the twisted kernel vanishes for large t by the
induction hypothesis. The long exact sequence therefore kills the given-degree
cohomology of G(t). There are only finitely many relevant positive degrees, so take the
maximum of their bounds and zero. The projection formula identifies i_*(F tensor i^*O(t))
with G(t), and the affine-morphism cohomology comparison for the closed immersion i
identifies its cohomology with that on X. This gives one natural-number bound for all
positive degrees. No arbitrary ample module or residue-class argument is used here. -/
theorem exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ (p t : ℕ), 0 < p → t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  have : IsLocallyNoetherian ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A)) ↘ Spec (.of A))
  have := isQuasicoherent_pushforward_of_isClosedImmersion i F
  have := isFinitePresentation_pushforward_of_isClosedImmersion i F
  obtain ⟨m₀, hv⟩ := RingTwistCech.exists_subsingleton_H_tensor_twist A N
    ((pushforward i).obj F)
  refine ⟨m₀.toNat, ?_⟩
  intro p t hp ht
  have hm : m₀ ≤ (t : ℤ) := by omega
  have := hv t hm p hp
  obtain ⟨e, _⟩ := exists_moduleCohomology_source_comparison
    ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A)) p
  have hz : IsZero ((RingedSpace.moduleCohomology
      (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).toRingedSpace p).obj
      (tensorObj ((pushforward i).obj F)
        (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) t))) := by
    exact (ModuleCat.isZero_iff_subsingleton).mpr (e _).toEquiv.subsingleton
  obtain ⟨pf⟩ := nonempty_pushforward_tensorObj_pullback_iso i F
    (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) t)
  have hz' := hz.of_iso ((RingedSpace.moduleCohomology
    (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).toRingedSpace p).mapIso pf)
  have : (tensorObj F (ProjectiveSpace.twistRestrict i t)).IsQuasicoherent :=
    isQuasicoherent_tensorObj F (ProjectiveSpace.twistRestrict i t)
  have : IsIso (moduleCohomologyEdgeMap i
      (tensorObj F (ProjectiveSpace.twistRestrict i t)) p) :=
    ((affine_morphism_cohomology_edge i _).2 p).1
  have : Subsingleton ((RingedSpace.moduleCohomology
      (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))).toRingedSpace p).obj
      ((pushforward i).obj (tensorObj F (ProjectiveSpace.twistRestrict i t)))) :=
    (ModuleCat.isZero_iff_subsingleton).mp hz'
  let ec := (asIso (moduleCohomologyEdgeMap i
    (tensorObj F (ProjectiveSpace.twistRestrict i t)) p)).symm
  exact (ModuleCat.isZero_iff_subsingleton).mpr
    ec.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Scheme.Modules

end AlgebraicGeometry

