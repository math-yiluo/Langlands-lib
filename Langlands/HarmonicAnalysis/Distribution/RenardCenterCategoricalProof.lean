import Langlands.HarmonicAnalysis.Distribution.RenardCenterStatements
import Langlands.Algebra.NondegenerateModuleNaturalEndClassificationProof

/-! # Renard II.3.13 Corollary: the categorical comparison (algebraic part) -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardCenter

open Langlands.Algebra

universe uA uM

section CommutantBijective

variable {A : Type uA} [NonUnitalRing A]

/-- The published family action into natural endomorphisms is injective. -/
theorem familyNaturalEnd_injective (hA : IsIdempotented A) :
    Function.Injective (IdempotentedRingRightLimit.familyNaturalEnd.{uA, max uA uM} hA) := by
  intro x y h
  have hx := NondegenerateModuleNaturalEndClassificationProof.familyRecovery.{uA, uM} hA x
  have hy := NondegenerateModuleNaturalEndClassificationProof.familyRecovery.{uA, uM} hA y
  have h' : IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA x =
      IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, max uA uM} hA y := h
  rw [← hx, ← hy, h']

/-- I.1.7: the commutant acts faithfully on the actual categorical center. -/
theorem fromCommutantRingHom_injective (hA : IsIdempotented A) :
    Function.Injective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) := by
  intro x y h
  apply Subtype.ext
  apply familyNaturalEnd_injective.{uA, uM} hA
  have h1 := congrArg NondegenerateModuleCenter.forget h
  exact h1

/-- I.1.7: every central transformation comes from the commutant. -/
theorem fromCommutantRingHom_surjective (hA : IsIdempotented A) :
    Function.Surjective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) := by
  intro z
  let θ := NondegenerateModuleCenter.forget z
  let x := NondegenerateModuleNaturalEndEvaluation.toFamilyRingHom.{uA, uM} hA θ
  have hθ : IdempotentedRingRightLimit.familyNaturalEnd.{uA, max uA uM} hA x = θ :=
    NondegenerateModuleNaturalEndClassificationProof.naturalEndRecovery.{uA, uM} hA θ
  have hx : x ∈ NondegenerateModuleCenter.commutantSubring hA := by
    rw [NondegenerateModuleCenter.mem_commutantSubring_iff]
    intro a
    apply familyNaturalEnd_injective.{uA, uM} hA
    change IdempotentedRingRightLimit.familyNaturalEnd hA
        (IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) x) =
      IdempotentedRingRightLimit.familyNaturalEnd hA
        (IdempotentedRingRightLimit.product hA x (IdempotentedRingRightLimit.canonical a))
    rw [IdempotentedRingRightLimit.familyNaturalEnd_product,
      IdempotentedRingRightLimit.familyNaturalEnd_product, hθ]
    apply NatTrans.ext
    funext M
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    change IdempotentedRingRightLimitAction.act M.property (IdempotentedRingRightLimit.canonical a)
        ((z.app M).hom.toAddMonoidHom m) =
      (z.app M).hom.toAddMonoidHom
        (IdempotentedRingRightLimitAction.act M.property (IdempotentedRingRightLimit.canonical a) m)
    have h1 := IdempotentedRingRightLimitAction.canonical_act hA M.property a
      ((z.app M).hom.toAddMonoidHom m)
    have h2 := IdempotentedRingRightLimitAction.canonical_act hA M.property a (m : M.obj)
    exact h1.trans (((z.app M).hom.map_smul' a m).symm.trans
      (congrArg (z.app M).hom.toAddMonoidHom h2.symm))
  refine ⟨⟨x, hx⟩, ?_⟩
  apply NondegenerateModuleCenter.forgetRingHom_injective
  exact hθ

theorem fromCommutantRingHom_bijective (hA : IsIdempotented A) :
    Function.Bijective (NondegenerateModuleCenter.fromCommutantRingHom.{uA, max uA uM} hA) :=
  ⟨fromCommutantRingHom_injective.{uA, uM} hA, fromCommutantRingHom_surjective.{uA, uM} hA⟩

end CommutantBijective

section Assembly

universe uG

open MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- Under the completion comparison, an actual Hecke density goes to its canonical image. -/
theorem comparison_hecke {hA : IsIdempotented (Hecke.HeckeAlgebra μ)}
    {pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ}
    {E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)}
    (hE : RenardCompletion.ComparisonSpecification μ hA pr E)
    (H : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ)
    (hH : (H : Distribution G) = heckeDistribution μ h) :
    E H = IdempotentedRingRightLimit.canonical h := by
  obtain ⟨H', hH', hEH'⟩ := hE.2.2.2.2.1 h
  have hHH' : H = H' := Subtype.ext (hH.trans hH'.symm)
  rw [hHH', hEH']

/-- Commutation of the completion coordinate with the canonical Hecke image is
commutation of the two full Hecke products. -/
theorem comparison_commutes_iff {hA : IsIdempotented (Hecke.HeckeAlgebra μ)}
    {pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ}
    {E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)}
    (hpr : RenardEssentialProducts.RightProductSpecification μ pr)
    (hE : RenardCompletion.ComparisonSpecification μ hA pr E)
    (T : rightEssentiallyCompact μ) :
    (∀ a : Hecke.HeckeAlgebra μ,
      IdempotentedRingRightLimit.product hA (IdempotentedRingRightLimit.canonical a) (E T) =
        IdempotentedRingRightLimit.product hA (E T) (IdempotentedRingRightLimit.canonical a)) ↔
    ∀ h : Hecke.HeckeAlgebra μ,
      rightHeckeConvolution μ (T : Distribution G) h =
        leftHeckeConvolution μ h (T : Distribution G) := by
  constructor
  · intro hcomm h
    obtain ⟨H, hH, h1, h2⟩ := hpr.1.2.2.2 T h
    have hEH := comparison_hecke hE H h hH
    have hpTH : pr T H = pr H T := by
      apply E.injective
      rw [hE.2.2.1, hE.2.2.1, hEH]
      exact (hcomm h).symm
    rw [← h1, ← h2, hpTH]
  · intro hcomm a
    obtain ⟨H, hH, h1, h2⟩ := hpr.1.2.2.2 T a
    have hEH := comparison_hecke hE H a hH
    have hpTH : pr T H = pr H T := Subtype.ext (by rw [h1, h2, hcomm a])
    rw [← hEH, ← hE.2.2.1, ← hE.2.2.1, hpTH]

/-- A commutant element gives a right-essentially-compact distribution commuting
with both full Hecke actions. -/
theorem symm_commutes_hecke {hA : IsIdempotented (Hecke.HeckeAlgebra μ)}
    {pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ}
    {E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)}
    (hpr : RenardEssentialProducts.RightProductSpecification μ pr)
    (hE : RenardCompletion.ComparisonSpecification μ hA pr E)
    (x : NondegenerateModuleCenter.Commutant hA) (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (E.symm x.val : Distribution G) h =
      leftHeckeConvolution μ h (E.symm x.val : Distribution G) := by
  refine (comparison_commutes_iff hpr hE (E.symm x.val)).mp ?_ h
  intro a
  rw [E.apply_symm_apply]
  exact NondegenerateModuleCenter.commutes hA x a

/-- The completion comparison identifies the Hecke commutant with the
conjugation-invariant two-sided essentially compact distributions. -/
theorem exists_commutantInvariant {hA : IsIdempotented (Hecke.HeckeAlgebra μ)}
    {pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ}
    {E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)}
    (hpr : RenardEssentialProducts.RightProductSpecification μ pr)
    (hE : RenardCompletion.ComparisonSpecification μ hA pr E)
    (hC : CentralitySpecification μ pr) :
    ∃ Φ : NondegenerateModuleCenter.Commutant hA →
        {T : essentiallyCompact μ // IsConjugationInvariant (T : Distribution G)},
      Function.Bijective Φ ∧
        ∀ x, ((Φ x).val : Distribution G) = (E.symm x.val : Distribution G) := by
  have hinv : ∀ x : NondegenerateModuleCenter.Commutant hA,
      IsConjugationInvariant (E.symm x.val : Distribution G) := fun x =>
    ((hC (E.symm x.val)).2.1).mp (symm_commutes_hecke hpr hE x)
  refine ⟨fun x => ⟨⟨(E.symm x.val : Distribution G), (hC (E.symm x.val)).2.2 (hinv x)⟩,
    hinv x⟩, ⟨?_, ?_⟩, fun x => rfl⟩
  · intro x y hxy
    have h1 : ((E.symm x.val : rightEssentiallyCompact μ) : Distribution G) =
        (E.symm y.val : Distribution G) :=
      congrArg (fun S : {T : essentiallyCompact μ //
        IsConjugationInvariant (T : Distribution G)} => (S.val : Distribution G)) hxy
    exact Subtype.ext (E.symm.injective (Subtype.ext h1))
  · rintro ⟨T, hT⟩
    have hTr : (T : Distribution G) ∈ rightEssentiallyCompact μ :=
      (Submodule.mem_inf.mp T.2).1
    let Tr : rightEssentiallyCompact μ := ⟨T, hTr⟩
    have hH := ((hC Tr).2.1).mpr hT
    have hcomm := (comparison_commutes_iff hpr hE Tr).mpr hH
    have hmem : E Tr ∈ NondegenerateModuleCenter.commutantSubring hA := by
      rw [NondegenerateModuleCenter.mem_commutantSubring_iff]
      exact hcomm
    refine ⟨⟨E Tr, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((E.symm (E Tr) : rightEssentiallyCompact μ) : Distribution G) = T
    rw [E.symm_apply_apply]

/-- II.3.13 Corollary, abstract assembly: from the right, left and two-sided
products, the completion comparison and the centrality specification, the
actual categorical center is identified with the conjugation-invariant
essentially compact distributions, compatibly with all structure. -/
theorem exists_categoricalComparison {hA : IsIdempotented (Hecke.HeckeAlgebra μ)}
    {pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ}
    {pl : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ}
    {p : essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ}
    {E : rightEssentiallyCompact μ ≃+ IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)}
    (hpr : RenardEssentialProducts.RightProductSpecification μ pr)
    (hp : RenardEssentialProducts.TwoSidedProductSpecification μ pr pl p)
    (hE : RenardCompletion.ComparisonSpecification μ hA pr E)
    (hC : CentralitySpecification μ pr) :
    ∃ C : NondegenerateModuleCenter.{uG, max uG uM} (Hecke.HeckeAlgebra μ) ≃
        {T : essentiallyCompact μ // IsConjugationInvariant (T : Distribution G)},
      CategoricalComparisonSpecification.{uG, uM} μ hA p E C := by
  let _ := NondegenerateModuleCenter.ring.{uG, max uG uM} (Hecke.HeckeAlgebra μ)
  let _ := NondegenerateModuleCenter.commutantRing hA
  obtain ⟨Φ, hΦ, hΦv⟩ := exists_commutantInvariant hpr hE hC
  let F := NondegenerateModuleCenter.fromCommutantRingHom.{uG, max uG uM} hA
  have hF : Function.Bijective F := fromCommutantRingHom_bijective.{uG, uM} hA
  let Fe := Equiv.ofBijective F hF
  have hFe : ∀ z, F (Fe.symm z) = z := Fe.apply_symm_apply
  have hsymm_add : ∀ z w, Fe.symm (z + w) = Fe.symm z + Fe.symm w := by
    intro z w
    apply hF.1
    rw [hFe, map_add F, hFe, hFe]
  have hsymm_mul : ∀ z w, Fe.symm (z * w) = Fe.symm z * Fe.symm w := by
    intro z w
    apply hF.1
    rw [hFe, map_mul F, hFe, hFe]
  have hsymm_one : Fe.symm 1 = 1 := by
    apply hF.1
    rw [hFe, map_one F]
  refine ⟨Fe.symm.trans (Equiv.ofBijective Φ hΦ), ?_, ?_, ?_, ?_⟩
  · intro z w
    change ((Φ (Fe.symm (z + w))).val : Distribution G) =
      ((Φ (Fe.symm z)).val : Distribution G) + ((Φ (Fe.symm w)).val : Distribution G)
    rw [hΦv, hΦv, hΦv, hsymm_add]
    have hval : ((Fe.symm z + Fe.symm w : NondegenerateModuleCenter.Commutant hA) :
        IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)) =
        (Fe.symm z).val + (Fe.symm w).val := rfl
    rw [hval, map_add, Submodule.coe_add]
  · intro z w
    change Φ (Fe.symm (z * w)) = p (Φ (Fe.symm z)).val (Φ (Fe.symm w)).val
    rw [hsymm_mul]
    set x := Fe.symm z
    set y := Fe.symm w
    apply Subtype.ext
    obtain ⟨tr, ur, tl, ul, htr, hur, -, -, hpTU, -⟩ := hp.2 (Φ x).val (Φ y).val
    have htr' : tr = E.symm x.val := Subtype.ext (htr.trans (hΦv x))
    have hur' : ur = E.symm y.val := Subtype.ext (hur.trans (hΦv y))
    rw [hpTU, htr', hur', hΦv]
    congr 1
    apply E.injective
    rw [hE.2.2.1, E.apply_symm_apply, E.apply_symm_apply, E.apply_symm_apply]
    rfl
  · change ((Φ (Fe.symm 1)).val : Distribution G) = dirac 1
    rw [hΦv, hsymm_one]
    obtain ⟨d, hd, hEd⟩ := hE.2.2.2.1
    change ((E.symm IdempotentedRingRightLimit.unit : rightEssentiallyCompact μ) :
      Distribution G) = dirac 1
    rw [← hEd, E.symm_apply_apply, hd]
  · intro z
    exact ⟨E.symm (Fe.symm z).val, (hΦv (Fe.symm z)).symm, Fe.symm z,
      (E.apply_symm_apply _).symm, hFe z⟩

/-- The categorical-center statement follows from the essential products, the
completion comparison and the centrality specification for every right product. -/
theorem categoricalCenterStatement_of
    (hEP : RenardEssentialProducts.Statements.{uG})
    (hCO : RenardCompletion.Statements.{uG})
    (hcent : ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
      (pr : rightEssentiallyCompact μ →ₗ[ℂ]
        rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ),
      RenardEssentialProducts.RightProductSpecification μ pr → CentralitySpecification μ pr) :
    CategoricalCenterStatement.{uG, uM} := by
  intro G _ _ _ _ _ _ _ _ μ _
  obtain ⟨hA, pr, hpr, E, hE, -⟩ := hCO G μ
  obtain ⟨-, ⟨pl, hpl, -⟩, hp⟩ := hEP G μ
  obtain ⟨p, hp', -⟩ := hp pr pl hpr hpl
  have hC := hcent G μ pr hpr
  exact ⟨hA, pr, pl, p, E, hpr, hpl, hp', hE, hC, exists_categoricalComparison hpr hp' hE hC⟩

end Assembly

end Langlands.HarmonicAnalysis.Distribution.RenardCenter
