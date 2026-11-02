import Langlands.Algebra.ExtendScalarsTensor
import Langlands.Cohomology.PerfectResidueAcyclicity
import Langlands.Cohomology.ModuleComplex.BaseChangeHomology
import Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Main
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Strictly perfect complexes whose geometric fibres are concentrated in degree zero
-/

universe u

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- Descending induction: if every reduction of a strictly perfect complex at a maximal ideal is
exact in all positive degrees, then the complex is exact in all positive degrees and the image of
its degree-zero differential is projective. -/
theorem exactAt_pos_of_residue_exactAt_pos
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (hres : ∀ m : Ideal R, m.IsMaximal → ∀ i : ℤ, 0 < i →
      ((baseChange (Ideal.Quotient.mk m)).obj K).ExactAt i) :
    Module.Projective R (LinearMap.range (K.d 0 (0 + 1)).hom) ∧
      ∀ j : ℤ, 0 < j → K.ExactAt j := by
  obtain ⟨⟨-, b, -, hb⟩, hfin⟩ := hK
  let P : ℤ → Prop := fun i ↦
    Module.Projective R (LinearMap.range (K.d i (i + 1)).hom) ∧ ∀ j, i < j → K.ExactAt j
  let b' := max b 0
  have hb' : K.IsStrictlyLE b' := K.isStrictlyLE_of_le b b' (le_max_left _ _)
  have base : P b' := by
    refine ⟨?_, fun j hj ↦ HomologicalComplex.ExactAt.of_isZero (K.isZero_of_isStrictlyLE b' j hj)⟩
    have : Subsingleton (K.X (b' + 1)) :=
      ModuleCat.isZero_iff_subsingleton.1 (K.isZero_of_isStrictlyLE b' (b' + 1))
    infer_instance
  have step : ∀ k, 0 ≤ k → P (k + 1) → P k := by
    rintro k hk ⟨hproj, hex⟩
    have := hproj
    have := (hfin (k + 1)).1
    have := (hfin (k + 1)).2
    obtain ⟨π, hπ⟩ := exists_retraction_ker K (k + 1) (k + 1 + 1)
    have hle := ker_le_range_of_residue_exactAt K k π hπ
      (fun m hm ↦ hres m hm (k + 1) (by omega))
    have hrange : LinearMap.range (K.d k (k + 1)).hom =
        LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom := by
      refine le_antisymm ?_ hle
      rintro _ ⟨y, rfl⟩
      change (K.d (k + 1) (k + 1 + 1)).hom ((K.d k (k + 1)).hom y) = 0
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
      rfl
    have : Module.Projective R (LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom) :=
      Module.Projective.of_split (LinearMap.ker (K.d (k + 1) (k + 1 + 1)).hom).subtype π
        (LinearMap.ext hπ)
    refine ⟨Module.Projective.of_equiv' (LinearEquiv.ofEq _ _ hrange.symm), fun j hj ↦ ?_⟩
    rcases lt_or_eq_of_le (show k + 1 ≤ j by omega) with h | rfl
    · exact hex j h
    · rw [HomologicalComplex.exactAt_iff' K k (k + 1) (k + 1 + 1) (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_ker_sub_range]
      exact hle
  have hP : ∀ t : ℕ, (t : ℤ) ≤ b' → P (b' - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using base
    | succ t ih =>
      intro ht
      have h := ih (by omega)
      have := step (b' - (t + 1 : ℕ)) (by omega) (by
        rwa [show b' - ((t + 1 : ℕ) : ℤ) + 1 = b' - (t : ℤ) by push_cast; ring])
      exact this
  have h0 := hP b'.toNat (by omega)
  rw [show b' - (b'.toNat : ℤ) = 0 by omega] at h0
  exact ⟨h0.1, h0.2⟩



/-- The geometric fibres of a complex `K` of `R`-modules have cohomology concentrated in degree
zero, of dimension `r`: for every algebraically closed field `k` and every ring map `φ : R → k`,
the cohomology of `k ⊗_R K` vanishes outside degree zero and has dimension `r` in degree zero. -/
def GeometricFibresDegreeZero (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : R →+* k),
    (∀ i : ℤ, i ≠ 0 → IsZero (((baseChange φ).obj K).homology i)) ∧
      Module.finrank k (((baseChange φ).obj K).homology 0) = r

open FibreH0Spread

/-- A term of a model whose rank is zero vanishes. -/
lemma isZero_X_of_rank_eq_zero {A : Type u} [CommRing A]
    {P : CochainComplex (ModuleCat.{u} A) ℤ} {n : ℤ → ℕ}
    (hn : ∀ i, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))) {i : ℤ} (hi : n i = 0) :
    IsZero (P.X i) := by
  have : Subsingleton (Fin (n i) → A) := by
    rw [hi]
    infer_instance
  have : Subsingleton (P.X i) := (hn i).some.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Near every prime, a strictly perfect complex whose geometric fibres are concentrated in degree
zero with dimension `r` has a finite free model concentrated in degree zero, of rank `r`, after
inverting one element outside the prime; the rank is also the dimension over the residue field
of the prime. -/
lemma exists_degreeZero_model {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    {r : ℕ} (h : GeometricFibresDegreeZero K r) (p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∃ n : ℤ → ℕ, HasModel (algebraMap R (Localization.Away s)) K n ∧
      n 0 = r ∧ (∀ i : ℤ, i ≠ 0 → n i = 0) ∧
      n 0 = Module.finrank p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology 0) := by
  obtain ⟨s, hs, n, ⟨P, hP, ⟨e⟩, hn⟩, hrank⟩ := exists_hasModel_rank hK p
  have hu : IsUnit (algebraMap R p.ResidueField s) :=
    isUnit_iff_ne_zero.2 (fun h0 ↦ hs (Ideal.algebraMap_residueField_eq_zero.1 h0))
  let ρ : Localization.Away s →+* p.ResidueField := IsLocalization.Away.lift s hu
  have hρ : ρ.comp (algebraMap R (Localization.Away s)) = algebraMap R p.ResidueField :=
    IsLocalization.Away.lift_comp s hu
  let k := AlgebraicClosure p.ResidueField
  obtain ⟨-, hk⟩ := fibre_data e hn ρ (algebraMap R p.ResidueField) hρ hrank
    (algebraMap p.ResidueField k) _ rfl
  obtain ⟨hz, hr⟩ := h k (((algebraMap p.ResidueField k).comp ρ).comp
    (algebraMap R (Localization.Away s)))
  refine ⟨s, hs, n, ⟨P, hP, ⟨e⟩, hn⟩, (hk 0).trans hr, fun i hi ↦ ?_, hrank 0⟩
  have : Subsingleton (((baseChange (((algebraMap p.ResidueField k).comp ρ).comp
      (algebraMap R (Localization.Away s)))).obj K).homology i) :=
    ModuleCat.isZero_iff_subsingleton.1 (hz i hi)
  rw [hk i]
  exact Module.finrank_zero_of_subsingleton

/-- If a model has rank zero in degree `i`, every scalar extension of the modelled complex through
the model has vanishing cohomology in degree `i`. -/
lemma isZero_homology_of_hasModel {A T : Type u} [CommRing A] [CommRing T] {α : R →+* A}
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ → ℕ} (hm : HasModel α K n) (β : A →+* T)
    (γ : R →+* T) (hγ : β.comp α = γ) {i : ℤ} (hi : n i = 0) :
    IsZero (((baseChange γ).obj K).homology i) := by
  obtain ⟨P, -, ⟨e⟩, hn⟩ := hm
  obtain ⟨eH⟩ := nonempty_homology_equiv_of_model e β γ hγ i
  have hX : IsZero (((baseChange β).obj P).X i) :=
    (ModuleCat.extendScalars β).map_isZero (isZero_X_of_rank_eq_zero hn hi)
  have : Subsingleton (((baseChange β).obj P).homology i) :=
    ModuleCat.isZero_iff_subsingleton.1
      (ShortComplex.isZero_homology_of_isZero_X₂ (((baseChange β).obj P).sc i) hX)
  have : Subsingleton (((baseChange γ).obj K).homology i) := eH.symm.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Every reduction at a maximal ideal of a strictly perfect complex whose geometric fibres are
concentrated in degree zero is exact outside degree zero. -/
lemma residue_exactAt {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    {r : ℕ} (h : GeometricFibresDegreeZero K r) (m : Ideal R) (hm : m.IsMaximal) (i : ℤ)
    (hi : i ≠ 0) : ((baseChange (Ideal.Quotient.mk m)).obj K).ExactAt i := by
  have := hm.isPrime
  obtain ⟨s, hs, n, hmod, -, hz, -⟩ := exists_degreeZero_model hK h m
  let := Ideal.Quotient.field m
  have hu : IsUnit (Ideal.Quotient.mk m s) :=
    isUnit_iff_ne_zero.2 (fun h0 ↦ hs (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_homology_of_hasModel hmod (IsLocalization.Away.lift s hu) _
    (IsLocalization.Away.lift_comp s hu) (hz i hi)


/-- A strictly perfect complex whose geometric fibres are concentrated in degree zero is exact in
all positive degrees, and the image of its degree-zero differential is projective. -/
theorem exactAt_pos_of_geometricFibresDegreeZero {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r) :
    Module.Projective R (LinearMap.range (K.d 0 (0 + 1)).hom) ∧
      ∀ j : ℤ, 0 < j → K.ExactAt j :=
  exactAt_pos_of_residue_exactAt_pos hK (fun m hm i hi ↦ residue_exactAt hK h m hm i hi.ne')

/-- The terms of the canonical truncation `τ_{≤ 0} K` of such a complex are flat. -/
lemma flat_truncLE_zero_X {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    {r : ℕ} (h : GeometricFibresDegreeZero K r) (i : ℤ) :
    Module.Flat R ((K.truncLE 0).X i) := by
  obtain ⟨hproj, -⟩ := exactAt_pos_of_geometricFibresDegreeZero hK h
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have := (hK.2 i).2
    exact Module.Flat.of_linearEquiv (K.truncLEXIso 0 i hi).toLinearEquiv
  · have := (hK.2 0).2
    obtain ⟨π, hπ⟩ := exists_retraction_ker K 0 (0 + 1)
    have : Module.Projective R (LinearMap.ker (K.d 0 (0 + 1)).hom) :=
      Module.Projective.of_split (LinearMap.ker (K.d 0 (0 + 1)).hom).subtype π
        (LinearMap.ext hπ)
    have : Module.Flat R (K.sc' (-1) 0 (0 + 1)).moduleCatLeftHomologyData.K :=
      (inferInstance : Module.Flat R (LinearMap.ker (K.d 0 (0 + 1)).hom))
    exact Module.Flat.of_linearEquiv (K.truncLEXIsoCycles 0 ≪≫
      K.cyclesIsoSc' (-1) 0 (0 + 1) (by simp) (by simp) ≪≫
      (K.sc' (-1) 0 (0 + 1)).moduleCatCyclesIso).toLinearEquiv
  · have : Subsingleton ((K.truncLE 0).X i) :=
      ModuleCat.isZero_iff_subsingleton.1 ((K.truncLE 0).isZero_of_isStrictlyLE 0 i hi)
    infer_instance

/-- For a strictly perfect complex whose geometric fibres are concentrated in degree zero, the
comparison `S ⊗_R H^0(K) ⟶ H^0(S ⊗_R K)` is an isomorphism for every ring map `R → S`. -/
theorem isIso_baseChangeDerivedHomologyMap_zero {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r)
    {S : Type u} [CommRing S] (φ : R →+* S) :
    IsIso (baseChangeDerivedHomologyMap φ K 0) := by
  obtain ⟨-, hex⟩ := exactAt_pos_of_geometricFibresDegreeZero hK h
  have : K.IsLE 0 := (K.isLE_iff 0).2 hex
  obtain ⟨⟨-, b, -, hb⟩, hfin⟩ := id hK
  have : K.IsStrictlyLE (max b 0) := K.isStrictlyLE_of_le b _ (le_max_left _ _)
  have : (K.truncLE 0).IsStrictlyLE (max b 0) :=
    (K.truncLE 0).isStrictlyLE_of_le 0 _ (le_max_right _ _)
  have := quasiIso_baseChange_map_of_flat φ (K.ιTruncLE 0) (max b 0)
    (flat_truncLE_zero_X hK h)
    (fun n ↦ have := (hfin n).2; inferInstance)
  rw [← isIso_baseChangeDerivedHomologyMap_iff φ 0 (K.ιTruncLE 0) inferInstance inferInstance]
  exact isIso_baseChangeDerivedHomologyMap_of_isZero φ _ 0
    ((K.truncLE 0).isZero_of_isStrictlyLE 0 (0 + 1))

/-- For a strictly perfect complex whose geometric fibres are concentrated in degree zero, the
comparison `S ⊗_R H^0(K) ⟶ H^0(S ⊗_R K)` on homology of complexes is an isomorphism for every
ring map `R → S`. -/
theorem isIso_baseChangeHomologyMap_zero {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r)
    {S : Type u} [CommRing S] (φ : R →+* S) :
    IsIso (baseChangeHomologyMap φ K 0) := by
  have h₁ := isIso_baseChangeDerivedHomologyMap_zero hK h φ
  rw [baseChangeDerivedHomologyMap_eq] at h₁
  have h₂ := IsIso.of_isIso_comp_left ((ModuleCat.extendScalars φ).map
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).hom.app K))
    (baseChangeHomologyMap φ K 0 ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) 0).inv.app ((baseChange φ).obj K))
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) 0).inv.app ((baseChange φ).obj K))

/-- For a strictly perfect complex whose geometric fibres are concentrated in degree zero and an
`R`-algebra `S`, the `S`-linear equivalence `S ⊗[R] H^0(K) ≃ H^0(S ⊗_R K)` given by the
base-change comparison. -/
def tensorHomologyZeroEquiv {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r)
    (S : Type u) [CommRing S] [Algebra R S] :
    S ⊗[R] K.homology 0 ≃ₗ[S] ((baseChange (algebraMap R S)).obj K).homology 0 :=
  have := isIso_baseChangeHomologyMap_zero hK h (algebraMap R S)
  (Langlands.Scheme.Modules.extendScalarsAlgebraEquiv
    (CommRingCat.of R) (CommRingCat.of S) (K.homology 0)).symm ≪≫ₗ
    (asIso (baseChangeHomologyMap (algebraMap R S) K 0)).toLinearEquiv

/-- Near every prime, the degree-zero cohomology of such a complex becomes free of rank `r` after
inverting one element outside the prime. -/
lemma exists_away_tensor_homology_equiv {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r) (p : Ideal R)
    [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ Nonempty (Localization.Away s ⊗[R] K.homology 0 ≃ₗ[Localization.Away s]
      (Fin r → Localization.Away s)) := by
  obtain ⟨s, hs, n, ⟨P, -, ⟨e⟩, hn⟩, hr, hz, -⟩ := exists_degreeZero_model hK h p
  have hX : ∀ i : ℤ, i ≠ 0 →
      IsZero (((baseChange (RingHom.id (Localization.Away s))).obj P).X i) :=
    fun i hi ↦ (ModuleCat.extendScalars _).map_isZero (isZero_X_of_rank_eq_zero hn (hz i hi))
  have hd : ∀ i j : ℤ, ((baseChange (RingHom.id (Localization.Away s))).obj P).d i j = 0 := by
    intro i j
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst hi hj
        exact HomologicalComplex.shape _ _ _ (by simp)
      · exact (hX j hj).eq_of_tgt _ _
    · exact (hX i hi).eq_of_src _ _
  obtain ⟨E⟩ := nonempty_homology_equiv_fin e hn (RingHom.id _)
    (algebraMap R (Localization.Away s)) (RingHom.id_comp _) hd 0
  rw [hr] at E
  exact ⟨s, hs, ⟨tensorHomologyZeroEquiv hK h (Localization.Away s) ≪≫ₗ E⟩⟩

/-- The degree-zero cohomology of a strictly perfect complex whose geometric fibres are
concentrated in degree zero with dimension `r` is a finite projective module of constant rank
`r`. -/
theorem homology_zero_finite_projective_rank {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r) :
    Module.Finite R (K.homology 0) ∧ Module.Projective R (K.homology 0) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (K.homology 0) p = r := by
  let t : Set R := {s | Nonempty (Localization.Away s ⊗[R] K.homology 0 ≃ₗ[Localization.Away s]
    (Fin r → Localization.Away s))}
  have spn : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have := hm.isPrime
    obtain ⟨s, hs, hE⟩ := exists_away_tensor_homology_equiv hK h m
    exact hs (hle (Ideal.subset_span hE))
  have hflat : Module.Flat R (K.homology 0) := by
    refine Module.flat_of_isLocalized_span R (K.homology 0) t spn _
      (fun g ↦ TensorProduct.mk R (Localization.Away g.1) (K.homology 0) 1) (fun g ↦ ?_)
    have : Module.Flat (Localization.Away g.1) (Localization.Away g.1 ⊗[R] K.homology 0) :=
      Module.Flat.of_linearEquiv g.2.some
    exact Module.Flat.trans R (Localization.Away g.1) _
  have hfp : Module.FinitePresentation R (K.homology 0) :=
    Module.FinitePresentation.of_localizationSpan' t spn
      (Rₚ := fun g : t ↦ Localization.Away g.1)
      (fun g ↦ TensorProduct.mk R (Localization.Away g.1) (K.homology 0) 1)
      (fun g ↦ .of_equiv g.2.some.symm)
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq p]
  obtain ⟨-, -, n, -, hr, -, hrank⟩ := exists_degreeZero_model hK h p.asIdeal
  rw [← hr, hrank]
  exact (tensorHomologyZeroEquiv hK h p.asIdeal.ResidueField).finrank_eq

/-- Cohomology and base change for a strictly perfect complex whose geometric fibres are
concentrated in degree zero with dimension `r`: its degree-zero cohomology is finite projective of
constant rank `r`, and its formation commutes with every base change `R → S`. -/
theorem homology_zero_of_geometricFibresDegreeZero {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {r : ℕ} (h : GeometricFibresDegreeZero K r) :
    Module.Finite R (K.homology 0) ∧ Module.Projective R (K.homology 0) ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (K.homology 0) p = r) ∧
      ∀ (S : Type u) [CommRing S] (φ : R →+* S), IsIso (baseChangeDerivedHomologyMap φ K 0) :=
  ⟨(homology_zero_finite_projective_rank hK h).1, (homology_zero_finite_projective_rank hK h).2.1,
    (homology_zero_finite_projective_rank hK h).2.2,
    fun _ _ φ ↦ isIso_baseChangeDerivedHomologyMap_zero hK h φ⟩

end Langlands.Cohomology.ModuleComplex
