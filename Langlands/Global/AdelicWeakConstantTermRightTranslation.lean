import Langlands.Global.AdelicLogSquareIntegrableCompactTranslation
import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation
import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicParabolicConstantTermAutomorphy
import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction

/-! # Infinite right translation of weighted forms and weak constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) {J : StandardIndex F G fam.i fam.ν}

/-- Right translation preserves the normalized split-component exponent and its degree bound. -/
theorem HasExponent.rightTranslate {lam : ComplexCharacterParameter F (fam.P J)}
    {f : AdelicGroupPoints F G → ℂ} (hf : fam.HasExponent J lam f)
    (t : AdelicGroupPoints F G) : fam.HasExponent J lam (fun g => f (g * t)) := by
  obtain ⟨n, h⟩ := hf
  refine ⟨n, fun g => ?_⟩
  obtain ⟨p, hp, he⟩ := h (g * t)
  exact ⟨p, hp, fun x hx => by simpa only [normalizedAction, mul_assoc] using he x hx⟩

variable {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}

/-- Right translation by an infinite point commutes with forming the unitary exponent sum. -/
theorem IsWeakConstantTerm.infiniteRightTranslate
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {Φ ψ : AdelicGroupPoints F G → ℂ}
    (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J Φ ψ)
    (a : InfiniteAdelicGroupPoints F G) :
    fam.IsWeakConstantTerm hsmooth (Kinf.map (MulAut.conj a).toMonoidHom) rho J
        (fun g => Φ (g * ofInfinite F G a)) (fun g => ψ (g * ofInfinite F G a)) := by
  obtain ⟨s, c, hdec, hψeq⟩ := hψ
  let t := ofInfinite F G a
  let c' (lam : ComplexCharacterParameter F (fam.P J)) (g : AdelicGroupPoints F G) := c lam (g * t)
  refine ⟨s, c', ⟨?_, ?_, ?_⟩, ?_⟩
  · funext g
    unfold constantTerm
    rw [subgroupConstantTerm_rightTranslate]
    have h := congrFun hdec.sum_eq (g * t)
    simpa only [constantTerm, Finset.sum_apply, c'] using h
  · intro lam hlam
    exact (hdec.automorphic lam hlam).infiniteRightTranslate
      (adelicDifferentialCommutator_of_smooth F G hsmooth) a
  · intro lam hlam
    exact (hdec.exponent lam hlam).rightTranslate fam t
  · funext g
    simp only [hψeq, unitaryExponentSum, Finset.sum_apply, c', t]

/-- Weak constant terms for the infinite part of an adelic maximal compact
transport to the infinite part of its conjugate. -/
def WeakConstantTermCompactTranslationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (K : Subgroup (AdelicGroupPoints F G)) (a : InfiniteAdelicGroupPoints F G)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {Φ ψ : AdelicGroupPoints F G → ℂ},
    let t := ofInfinite F G a
    let K' := K.map (MulAut.conj t).toMonoidHom
    IsMaximalCompactSubgroup F G K →
    fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    fam.IsWeakConstantTerm hsmooth (K'.comap (ofInfinite F G).toMonoidHom) rho J
      (fun g => Φ (g * t)) (fun g => ψ (g * t))

theorem weakConstantTermCompactTranslation : WeakConstantTermCompactTranslationStatement := by
  intro F _ _ G _ _ _ fam J K a N d rho hsmooth Φ ψ t K' hK hψ
  have hK' : IsMaximalCompactSubgroup F G K' := hK.map_conj t
  have hinf : K'.comap (ofInfinite F G).toMonoidHom =
      (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [hK'.comap_ofInfinite_eq_map_infinite, hK.comap_ofInfinite_eq_map_infinite]
    exact map_infinite_map_conj_ofInfinite K a
  exact hinf.symm ▸ hψ.infiniteRightTranslate fam a

end Langlands.Global.StandardParabolicFamily

end

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "Γ" => rationalSubgroup F G
local notation "Q" => RationalQuotient F G

omit [LocallyOfFiniteType G.X.hom] in
private theorem infiniteCompact_comap_conj {K : Subgroup (AdelicGroupPoints F G)}
    (a : InfiniteAdelicGroupPoints F G) :
    (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom).comap (ofInfinite F G).toMonoidHom := by
  ext t
  change t ∈ (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom ↔
    ofInfinite F G t ∈ K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_comap, MulAut.conj_symm_apply, map_mul, map_inv]
  rfl

/-- Infinite right translation preserves logarithmic square integrability with the same weight
exponent and conjugates the subgroup whose archimedean pullback acts in the automorphy condition. -/
theorem IsLogSquareIntegrableAutomorphicForm.infiniteRightTranslate
    {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc φ)
    (hG : IsConnectedReductive G) (a : InfiniteAdelicGroupPoints F G) :
    IsLogSquareIntegrableAutomorphicForm F G (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom)
      rho hsmooth hcalc (fun g => φ (g * ofInfinite F G a)) := by
  let A := ofInfinite F G a
  have hAut := (infiniteCompact_comap_conj (K := K) a) ▸ hφ.1.infiniteRightTranslate hcalc a
  refine ⟨hAut, ?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hφ.2.1
    refine ⟨ν, fun b hb g => ?_⟩
    dsimp only
    rw [mul_assoc, hν b hb]
  obtain ⟨m, hm⟩ := hφ.2.2
  refine ⟨m, ?_⟩
  let σ := rationalLogHeight F G rho
  let μQ := rationalQuotientHaarMeasure F G
  let r := LeftCosetSpace.rightTranslate Γ A
  let : (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant :=
    adelicHaarUnimodularity.{0}.2 F G hG
  have hr : MeasurePreserving r μQ μQ := measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G A
  have hm' := hm.comp_measurePreserving hr
  have hMeas : Measurable (fun y : Q => φ (y.out * A)) := by
    apply Continuous.measurable
    apply (LeftCosetSpace.continuous_iff Γ).mpr
    have hinv : ∀ u ∈ Γ, ∀ g, φ ((u * g) * A) = φ (g * A) := by
      intro u hu g
      rw [mul_assoc, hφ.1.1 u hu]
    have he : (fun y : Q => φ (y.out * A)) ∘ LeftCosetSpace.mk Γ = fun g => φ (g * A) :=
      funext fun g => LeftCosetSpace.out_mk_of_invariant Γ (fun x => φ (x * A)) hinv g
    rw [he]
    exact hφ.1.2.1.1.comp (continuous_id.mul continuous_const)
  have hσ : Measurable σ := measurable_rationalLogHeight rho
  obtain ⟨C, -, hbound⟩ := exists_rationalLogHeight_rightTranslate_le rho A
  refine hm'.of_le_mul (c := C ^ m)
    (hMeas.div ((Complex.measurable_ofReal.comp hσ).pow_const m)).aestronglyMeasurable ?_
  filter_upwards with y
  have hd : r y = LeftCosetSpace.mk Γ (y.out * A) :=
    (congrArg r (Quotient.out_eq y).symm).trans (LeftCosetSpace.rightTranslate_mk Γ A y.out)
  have hvalue : φ (r y).out = φ (y.out * A) := by
    rw [hd, LeftCosetSpace.out_mk_of_invariant Γ φ hφ.1.1]
  have hy : 0 < σ y := zero_lt_one.trans_le (one_le_rationalLogHeight rho y)
  have hry : 0 < σ (r y) := zero_lt_one.trans_le (one_le_rationalLogHeight rho (r y))
  change ‖φ (y.out * A) / (σ y : ℂ) ^ m‖ ≤ C ^ m * ‖φ (r y).out / (σ (r y) : ℂ) ^ m‖
  rw [hvalue, Complex.norm_div, Complex.norm_div, norm_pow, norm_pow,
    Complex.norm_of_nonneg hy.le, Complex.norm_of_nonneg hry.le]
  have hRatio : σ (r y) ^ m / σ y ^ m ≤ C ^ m := by
    apply (div_le_iff₀ (pow_pos hy _)).mpr
    rw [← mul_pow]
    exact pow_le_pow_left₀ hry.le (hbound y) _
  calc
    _ = (σ (r y) ^ m / σ y ^ m) * (‖φ (y.out * A)‖ / σ (r y) ^ m) := by
      field_simp [hy.ne', hry.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hRatio (div_nonneg (norm_nonneg _) (pow_nonneg hry.le _))

variable [IsAffineHom G.X.hom]

/-- Infinite right translation preserves the weighted form and weak constant-term conditions
for the conjugate subgroup. -/
def AdelicWeakConstantTermRightTranslationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (a : InfiniteAdelicGroupPoints F G)
      (φ : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc φ →
      let L := K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom
      let f : AdelicGroupPoints F G → ℂ := fun g => φ (g * ofInfinite F G a)
      IsLogSquareIntegrableAutomorphicForm F G L rho hsmooth hcalc f ∧
        ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F G → ℂ),
          fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φ ψ →
          fam.IsWeakConstantTerm hsmooth (L.comap (ofInfinite F G).toMonoidHom) rho J f
            (fun g => ψ (g * ofInfinite F G a))

theorem adelicWeakConstantTermRightTranslation : AdelicWeakConstantTermRightTranslationStatement := by
  intro F _ _ G _ _ _ hG fam K N d rho hsmooth hcalc a φ hφ
  refine ⟨hφ.infiniteRightTranslate hG a, fun J ψ hψ => ?_⟩
  exact (infiniteCompact_comap_conj (K := K) a) ▸ hψ.infiniteRightTranslate fam a

end Langlands.Global
