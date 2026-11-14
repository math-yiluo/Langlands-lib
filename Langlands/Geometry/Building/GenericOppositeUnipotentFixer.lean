import Langlands.Geometry.Building.GenericOrderedFixerFactors
import Langlands.Geometry.Building.GenericApartmentPairNormalizer
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction
import Langlands.GroupScheme.Rational.RootGeneratedBruhatWord
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.BruhatPointReduction
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # Opposite unipotent products fixing an apartment point, without apartment axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Aubert.General.RationalPointFamily (SimpleRoot schemeWeylCharacterAction
  schemeWeylCharacterAction_mk)

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

section Form

variable (i) [Fintype (relativeRoots i)]

/-- The linear form `v ↦ ∑_α ⟨α, ν⟩ α(v)` on the translation space, summed over all actual
relative roots. -/
def cocharacterRootForm (ν : cocharacterLattice S) : TranslationSpace i →ₗ[ℝ] ℝ :=
  ∑ α : relativeRoots i, (latticePairing S α.1 ν : ℝ) • rootForm i α

variable {i}

omit [Mono i.hom.hom.left] in
theorem cocharacterRootForm_apply (ν : cocharacterLattice S) (v : TranslationSpace i) :
    cocharacterRootForm i ν v =
      ∑ α : relativeRoots i, (latticePairing S α.1 ν : ℝ) * rootForm i α v := by
  simp [cocharacterRootForm, LinearMap.sum_apply]

/-- The translation of `s ⊗ ν` moved by a normalizer element that sends a root `c` with
`⟨c, ν⟩ ≠ 0` to `-c` strictly decreases the form `cocharacterRootForm i ν`, for `s > 0`. -/
theorem cocharacterRootForm_translationAction_sub_lt (ν : cocharacterLattice S)
    (m : normalizerPoints i) {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (hcν : latticePairing S c ν ≠ 0) (hm : weylAction i m⁻¹ c = -c) {s : ℝ} (hs : 0 < s) :
    cocharacterRootForm i ν
      (translationAction i m (Submodule.Quotient.mk (s ⊗ₜ[ℤ] ν)) -
        Submodule.Quotient.mk (s ⊗ₜ[ℤ] ν)) < 0 := by
  classical
  set π := relativeWeylRootPermutation i (QuotientGroup.mk m⁻¹) with hπ
  let f : relativeRoots i → ℝ := fun α => (latticePairing S α.1 ν : ℝ)
  have hform (α : relativeRoots i) :
      rootForm i α (Submodule.Quotient.mk (s ⊗ₜ[ℤ] ν)) = s * f α := by
    rw [rootForm_mk, eval_tmul]
  have htrans (α : relativeRoots i) :
      rootForm i α (translationAction i m (Submodule.Quotient.mk (s ⊗ₜ[ℤ] ν))) =
        s * f (π α) := by
    rw [RootTranslationMetric.rootForm_translationAction, hform]
  rw [cocharacterRootForm_apply]
  simp only [map_sub, htrans, hform]
  -- the sum is `s * (∑ f α f (π α) - ∑ f α ^ 2)`
  have hsq : ∑ α : relativeRoots i, f (π α) ^ 2 = ∑ α : relativeRoots i, f α ^ 2 :=
    Equiv.sum_comp π (fun α => f α ^ 2)
  let c₀ : relativeRoots i := ⟨c, hc⟩
  have hπc : f (π c₀) = -f c₀ := by
    have h1 : ((π c₀ : relativeRoots i) : characterLattice S) = -c := by
      rw [hπ, relativeWeylRootPermutation_apply, relativeWeylCharacterAction_mk]
      exact hm
    show (latticePairing S ((π c₀ : relativeRoots i) : characterLattice S) ν : ℝ) =
      -(latticePairing S c ν : ℝ)
    rw [h1, map_neg, LinearMap.neg_apply, Int.cast_neg]
  have hpos : 0 < ∑ α : relativeRoots i, (f α - f (π α)) ^ 2 := by
    apply Finset.sum_pos' (fun α _ => sq_nonneg _)
    refine ⟨c₀, Finset.mem_univ _, ?_⟩
    rw [hπc, sub_neg_eq_add, ← two_mul]
    have : f c₀ ≠ 0 := by
      show (latticePairing S c ν : ℝ) ≠ 0
      exact_mod_cast hcν
    positivity
  have hexpand : ∑ α : relativeRoots i, (f α - f (π α)) ^ 2 =
      2 * (∑ α : relativeRoots i, f α ^ 2 - ∑ α : relativeRoots i, f α * f (π α)) := by
    have : ∀ α : relativeRoots i, (f α - f (π α)) ^ 2 =
        f α ^ 2 + f (π α) ^ 2 - 2 * (f α * f (π α)) := fun α => by ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsq, ← Finset.mul_sum]
    ring
  have hlt : ∑ α : relativeRoots i, f α * f (π α) < ∑ α : relativeRoots i, f α ^ 2 := by
    linarith
  have hrw : ∑ α : relativeRoots i, f α * (s * f (π α) - s * f α) =
      s * (∑ α : relativeRoots i, f α * f (π α) - ∑ α : relativeRoots i, f α ^ 2) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  change ∑ α : relativeRoots i, f α * (s * f (π α) - s * f α) < 0
  rw [hrw]
  exact mul_neg_of_pos_of_neg hs (by linarith)

end Form

variable (D : KPApartmentData i ω)

/-- **Rank-one fold.** Let `e ∈ U_c(k)` not fix the image of `x`, for a relative root `c`
negative on `ν`. Then `e · x = p · (m · x)` with `p ∈ U_{-c}(k)` and `m` a normalizer point,
and `m · x - x` has negative value under `cocharacterRootForm i ν`. -/
theorem exists_fold [Fintype (relativeRoots i)] (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (x : D.Apartment)
    {c : characterLattice S} (hc : c ∈ relativeRoots i) (hcν : latticePairing S c ν < 0)
    {e : rationalPoints G} (he : e ∈ rootGroupPoints i c) (hex : e ∉ D.filtration x c 0) :
    ∃ p ∈ rootGroupPoints i (-c), ∃ m : normalizerPoints i,
      e • D.apartmentMap x = p • D.apartmentMap (m • x) ∧
        cocharacterRootForm i ν ((m • x) -ᵥ x) < 0 := by
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hex (Subgroup.one_mem _)
  obtain ⟨p, hp⟩ :=
    ((rootRankOneFactorization k G hG S i hi c hc e he he1).1).exists
  set m : normalizerPoints i := ⟨p.1 * e * p.2, hp.2.2⟩ with hm_def
  have hmc : weylAction i m c = -c := hp.weylAction_eq_neg i hT hc.1 he he1
  have hnc : -c ∈ relativeRoots i := hmc ▸ weylAction_mapsTo_relativeRoots i m hc
  obtain ⟨t₀, ht₀⟩ := D.exists_val_eq_coe x hc he he1
  have ht₀neg : t₀ < 0 := by
    by_contra hge
    exact hex ⟨he, by rw [ht₀]; exact_mod_cast not_lt.mp hge⟩
  -- the second opposite factor fixes `x`
  have hp2val := x.isValuation.opposite_snd hc he he1 hp.1 hp.2.1 hp.2.2
  rw [ht₀] at hp2val
  have hp2 : p.2 ∈ D.filtration x (-c) 0 := by
    refine ⟨hp.2.1, ?_⟩
    rw [withTop_eq_neg_of_add_eq_zero hp2val, WithTop.coe_le_coe]
    exact neg_nonneg.mpr ht₀neg.le
  have hp2fix : p.2⁻¹ • D.apartmentMap x = D.apartmentMap x :=
    (D.sharpFixer_le_reducedFixer x) (Subgroup.inv_mem _ (D.filtration_le_sharpFixer x hnc hp2))
  refine ⟨p.1⁻¹, Subgroup.inv_mem _ hp.1, m, ?_, ?_⟩
  · have hem : e = p.1⁻¹ * (m : rationalPoints G) * p.2⁻¹ := by
      change e = p.1⁻¹ * (p.1 * e * p.2) * p.2⁻¹
      group
    rw [hem, mul_smul, mul_smul, hp2fix, D.apartmentMap_smul]
  · -- the fixed point `z = x - s ν` of `m`
    have hcν0 : (latticePairing S c ν : ℝ) < 0 := by exact_mod_cast hcν
    set s : ℝ := t₀ / (latticePairing S c ν : ℝ) with hs_def
    have hs : 0 < s := div_pos_of_neg_of_neg ht₀neg hcν0
    set w : V S := s ⊗ₜ[ℤ] ν with hw_def
    set z : D.Apartment := (Submodule.Quotient.mk (-w) : TranslationSpace i) +ᵥ x with hz_def
    have hzval : z.val c e = 0 := by
      rw [hz_def, val_mk_vadd, RootFunctionFamily.vadd_apply, ht₀, map_neg, hw_def, eval_tmul,
        hs_def, div_mul_cancel₀ _ hcν0.ne]
      rw [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
    have hmz : m • z = z := smul_eq_self_of_val_eq_zero D hT hc he he1 hp hzval
    have hxz : x = (Submodule.Quotient.mk w : TranslationSpace i) +ᵥ z := by
      rw [hz_def, vadd_vadd, ← Submodule.Quotient.mk_add, add_neg_cancel,
        Submodule.Quotient.mk_zero, zero_vadd]
    have hmx : (m • x) -ᵥ x =
        translationAction i m (Submodule.Quotient.mk w) - Submodule.Quotient.mk w := by
      conv_lhs => rw [hxz, smul_vadd, hmz]
      rw [vadd_vsub_vadd_cancel_right]
    have hminv : weylAction i m⁻¹ c = -c := by
      have h := weylAction_inv_apply_apply (i := i) m c
      rw [hmc, map_neg] at h
      exact neg_eq_iff_eq_neg.mp h
    rw [hmx]
    exact cocharacterRootForm_translationAction_sub_lt ν m hc hcν.ne hminv hs


/-- **Iwasawa folding along a gallery.** Let `cs` be a Coxeter realization of the relative Weyl
group for the generic cocharacter `ν`. For a normalizer point `n` of Coxeter length `N`, every
`c ∈ n U(ν)(k) n⁻¹` and every apartment point `x`, there are `v ∈ U(ν)(k)` and an apartment
point `y` with `c · x = v · y`. Moreover either `y - x` is negative for
`cocharacterRootForm i ν`, or `y = x` and `c = v e` with `e ∈ U(-ν)(k)` fixing `x`. -/
theorem exists_iwasawa_fold [Fintype (relativeRoots i)] (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {M : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem M (relativeWeylGroup i)}
    (hcs : IsRelativeWeylCoxeterRealization i ν cs)
    (hfac : HasSimpleRootUnipotentFactorization i ν) :
    ∀ (N : ℕ) (n : normalizerPoints i), cs.length (QuotientGroup.mk n) = N →
      ∀ c : rationalPoints G,
        (n : rationalPoints G)⁻¹ * c * n ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) →
        ∀ x : D.Apartment,
          ∃ v ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
            ∃ y : D.Apartment, c • D.apartmentMap x = v • D.apartmentMap y ∧
              (cocharacterRootForm i ν (y -ᵥ x) < 0 ∨
                (y = x ∧ ∃ e ∈ (Dynamic.unipotent
                    (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)),
                  e • D.apartmentMap x = D.apartmentMap x ∧ c = v * e)) := by
  intro N
  induction N with
  | zero =>
    intro n hn c hc x
    have hw : (QuotientGroup.mk n : relativeWeylGroup i) = 1 := cs.length_eq_zero_iff.mp hn
    have hnZ : (n : rationalPoints G) ∈ centralizerPoints i := by
      have h := (QuotientGroup.eq_one_iff n).mp hw
      exact Subgroup.mem_subgroupOf.mp h
    have hnP := centralizerPoints_le_dynamicParabolic i (CommGroupScheme.groupHom ν) hnZ
    have hcU : c ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _)) := by
      have h := Dynamic.conj_mem_unipotent _ hnP hc
      have heq : (n : rationalPoints G) * ((n : rationalPoints G)⁻¹ * c * n) *
          (n : rationalPoints G)⁻¹ = c := by group
      rwa [heq] at h
    exact ⟨c, hcU, x, rfl, Or.inr ⟨rfl, 1, Subgroup.one_mem _, one_smul _ _, (mul_one c).symm⟩⟩
  | succ N ih =>
    intro n hn c hc x
    set w : relativeWeylGroup i := QuotientGroup.mk n with hw_def
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, cs.length_one] at hn
      exact Nat.succ_ne_zero N hn.symm
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hw1
    have hlen : cs.length (w * cs.simple a) = N := by
      rcases cs.length_mul_simple w a with h | h
      · exact absurd ha (by unfold CoxeterSystem.IsRightDescent; omega)
      · omega
    have haroot : a.1 ∈ relativeRoots i := a.2.1.1
    have hapos : 0 < latticePairing S a.1 ν := a.2.1.2
    -- the descent root is sent to a negative root
    have hneg : ¬ schemeWeylCharacterAction i w a.1 ∈ positiveRelativeRoots i ν := by
      rw [← hcs.2.2.1 w a]
      unfold CoxeterSystem.IsRightDescent at ha
      omega
    rw [hw_def, schemeWeylCharacterAction_mk] at hneg
    set c' := weylAction i n a.1 with hc'_def
    have hc'root : c' ∈ relativeRoots i := weylAction_mapsTo_relativeRoots i n haroot
    have hc'neg : latticePairing S c' ν < 0 := by
      rcases lt_or_gt_of_ne (hν c' hc'root) with h | h
      · exact h
      · exact absurd ⟨hc'root, h⟩ hneg
    -- a lift of the simple reflection
    obtain ⟨na, hna⟩ := QuotientGroup.mk_surjective (cs.simple a)
    have hrefl : IsRelativeReflection i a.1 (QuotientGroup.mk na) := by
      rw [hna]
      exact hcs.isRelativeReflection_simple a
    have hnaa : weylAction i na a.1 = -a.1 := by
      obtain ⟨f, hfa, hf⟩ := hcs.1 a
      have h := hf a.1
      rw [← hna, schemeWeylCharacterAction_mk, hfa] at h
      rw [h, two_smul, sub_add_cancel_left]
    -- factor `n⁻¹ c n = q x₀`
    obtain ⟨q, hq, hqa, x₀, hx₀, hqx⟩ := hfac a.1 a.2 na hrefl _ hc
    set f : rationalPoints G := (n : rationalPoints G) * q * (n : rationalPoints G)⁻¹ with hf_def
    set e : rationalPoints G := (n : rationalPoints G) * x₀ * (n : rationalPoints G)⁻¹
      with he_def
    have hcfe : c = f * e := by
      have : c = (n : rationalPoints G) * ((n : rationalPoints G)⁻¹ * c * n) *
          (n : rationalPoints G)⁻¹ := by group
      rw [this, hqx, hf_def, he_def]
      group
    set n' : normalizerPoints i := n * na⁻¹ with hn'_def
    have hn'len : cs.length (QuotientGroup.mk n') = N := by
      rw [hn'_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hna, cs.inv_simple]
      exact hlen
    have hn'coe : ((n' : normalizerPoints i) : rationalPoints G) =
        (n : rationalPoints G) * (na : rationalPoints G)⁻¹ := by
      rw [hn'_def, Subgroup.coe_mul, Subgroup.coe_inv]
    have hf' : ((n' : normalizerPoints i) : rationalPoints G)⁻¹ * f * n' ∈
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
      have heq : ((n' : normalizerPoints i) : rationalPoints G)⁻¹ * f * n' =
          na.val * q * na.val⁻¹ := by
        rw [hn'coe, hf_def]
        group
      rw [heq]
      exact hqa
    have he : e ∈ rootGroupPoints i c' := conj_mem_rootGroupPoints n hx₀
    have heU : e ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)) := by
      have hpos : 0 < latticePairing S c' (-ν) := by
        rw [map_neg]
        exact neg_pos.mpr hc'neg
      exact RelativeRoot.subgroup_le_dynamicUnipotent i (-ν) hpos _ he
    by_cases hefix : e • D.apartmentMap x = D.apartmentMap x
    · obtain ⟨v, hv, y, hcy, hor⟩ := ih n' hn'len f hf' x
      refine ⟨v, hv, y, ?_, ?_⟩
      · rw [hcfe, mul_smul, hefix, hcy]
      · rcases hor with hlt | ⟨hyx, e₁, he₁, hfix₁, hfeq⟩
        · exact Or.inl hlt
        · refine Or.inr ⟨hyx, e₁ * e, Subgroup.mul_mem _ he₁ heU, ?_, ?_⟩
          · rw [mul_smul, hefix, hfix₁]
          · rw [hcfe, hfeq, mul_assoc]
    · have hex : e ∉ D.filtration x c' 0 := fun h =>
        hefix ((D.sharpFixer_le_reducedFixer x) (D.filtration_le_sharpFixer x hc'root h))
      obtain ⟨p, hp, m, hem, hΛ⟩ := D.exists_fold hG hi ν x hc'root hc'neg he hex
      have hpU : ((n' : normalizerPoints i) : rationalPoints G)⁻¹ * p * n' ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
        have hmem := conj_mem_rootGroupPoints n'⁻¹ hp
        have hact : weylAction i n'⁻¹ (-c') = a.1 := by
          rw [hn'_def, mul_inv_rev, inv_inv, map_mul, LinearEquiv.mul_apply, map_neg,
            hc'_def, weylAction_inv_apply_apply, map_neg, hnaa, neg_neg]
        rw [hact, Subgroup.coe_inv, inv_inv] at hmem
        exact RelativeRoot.subgroup_le_dynamicUnipotent i ν hapos _ hmem
      have hfp : ((n' : normalizerPoints i) : rationalPoints G)⁻¹ * (f * p) * n' ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
        have heq : ((n' : normalizerPoints i) : rationalPoints G)⁻¹ * (f * p) * n' =
            (((n' : normalizerPoints i) : rationalPoints G)⁻¹ * f * n') *
              (((n' : normalizerPoints i) : rationalPoints G)⁻¹ * p * n') := by group
        rw [heq]
        exact Subgroup.mul_mem _ hf' hpU
      obtain ⟨v, hv, y, hcy, hor⟩ := ih n' hn'len (f * p) hfp (m • x)
      refine ⟨v, hv, y, ?_, Or.inl ?_⟩
      · rw [hcfe, mul_smul, hem, ← mul_smul, hcy]
      · rw [← vsub_add_vsub_cancel y (m • x) x, map_add]
        rcases hor with hlt | ⟨hyx, -⟩
        · linarith
        · rw [hyx, vsub_self, map_zero, zero_add]
          exact hΛ

/-- A normalizer point of maximal Coxeter length sends every positive relative root of the
generic cocharacter `ν` to a root that is negative on `ν`. -/
theorem pairing_weylAction_neg_of_length_max
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {M : CoxeterMatrix (SimpleRoot i ν)} {cs : CoxeterSystem M (relativeWeylGroup i)}
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) (n₀ : normalizerPoints i)
    (hmax : ∀ w : relativeWeylGroup i, cs.length w ≤ cs.length (QuotientGroup.mk n₀))
    {β : characterLattice S} (hβ : β ∈ positiveRelativeRoots i ν) :
    latticePairing S (weylAction i n₀ β) ν < 0 := by
  have hsimple : ∀ a : SimpleRoot i ν, latticePairing S (weylAction i n₀ a.1) ν ≤ 0 := by
    intro a
    have hnot : ¬ schemeWeylCharacterAction i (QuotientGroup.mk n₀) a.1 ∈
        positiveRelativeRoots i ν := by
      rw [← hcs.2.2.1 (QuotientGroup.mk n₀) a]
      exact not_lt.mpr (hmax _)
    rw [schemeWeylCharacterAction_mk] at hnot
    by_contra hpos
    exact hnot ⟨weylAction_mapsTo_relativeRoots i n₀ a.2.1.1, lt_of_not_ge hpos⟩
  have hle : latticePairing S (weylAction i n₀ β) ν ≤ 0 := by
    have hcl := positiveRelativeRoots_subset_closure_simpleRelativeRoots i ν hβ
    refine AddSubmonoid.closure_induction
      (motive := fun χ _ => latticePairing S (weylAction i n₀ χ) ν ≤ 0)
      (fun χ hχ => hsimple ⟨χ, hχ⟩) (by simp) (fun χ ψ _ _ hχ hψ => ?_) hcl
    rw [map_add, map_add, LinearMap.add_apply]
    omega
  exact lt_of_le_of_ne hle (hν _ (weylAction_mapsTo_relativeRoots i n₀ hβ.1))

/-- **Opposite unipotent factors of a point stabilizer.** Let `ν` be a generic cocharacter
of a maximal split torus of a connected reductive group over any field, and let
`D` be supplied apartment data. If `u⁻ ∈ U(-ν)(k)` and `u⁺ ∈ U(ν)(k)` and `u⁻ u⁺` fixes the
image of an apartment point `x` in the reduced building, then `u⁻` and `u⁺` both fix it. -/
theorem smul_apartmentMap_eq_of_mul_smul_apartmentMap_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {um up : rationalPoints G}
    (hum : um ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier
      (Over.mk (𝟙 _)))
    (hup : up ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
      (Over.mk (𝟙 _)))
    (x : D.Apartment) (h : (um * up) • D.apartmentMap x = D.apartmentMap x) :
    um • D.apartmentMap x = D.apartmentMap x ∧ up • D.apartmentMap x = D.apartmentMap x := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have hfin : (relativeRoots i).Finite := hT.finite_relativeRoots i
  let : Fintype (relativeRoots i) := hfin.fintype
  have hR : HasRelativeRootSystem i := relativeRootSystem k G hG S i hi
  have hneg : ∀ a ∈ relativeRoots i, -a ∈ relativeRoots i :=
    fun _ ha => hR.neg_mem_relativeRoots i hT ha
  obtain ⟨hWfin, -, M, cs, hcs⟩ := relativeWeylCoxeter k G hG S i hi ν hν
  have hfac : HasSimpleRootUnipotentFactorization i ν :=
    hasSimpleRootUnipotentFactorization_of_orderedRootPoints i ν hν hneg
      (hR.linearIndependent_simpleRelativeRoots i ν hT hν) hfin
      (hasOrderedRootPointFactorization_of_statement RelativeRoot.dynamicRootOrderedProduct
        k G hG S i hi ν)
  -- a normalizer point of maximal length
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (fun w : relativeWeylGroup i => cs.length w)
  obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective w₀
  have hneg₀ : ∀ β ∈ positiveRelativeRoots i ν, latticePairing S (weylAction i n₀ β) ν < 0 :=
    fun β hβ => pairing_weylAction_neg_of_length_max ν hν hcs n₀ hw₀ hβ
  -- conjugation by `n₀⁻¹` carries `U(-ν)(k)` into `U(ν)(k)`
  have hconj : ∀ g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier
      (Over.mk (𝟙 _)),
      (n₀ : rationalPoints G)⁻¹ * g * n₀ ∈
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    intro g hg
    obtain ⟨l, b, hinj, hrange⟩ :=
      RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots i (-ν) hfin
    obtain ⟨gs, hgs, rfl⟩ := hasOrderedRootPointFactorization_of_statement
      RelativeRoot.dynamicRootOrderedProduct k G hG S i hi (-ν) l b hinj hrange g hg
    have hconjeq : (n₀ : rationalPoints G)⁻¹ * (List.ofFn gs).prod * n₀ =
        MulAut.conj ((n₀ : rationalPoints G)⁻¹) (List.ofFn gs).prod := by
      rw [MulAut.conj_apply, inv_inv]
    rw [hconjeq, map_list_prod]
    refine list_prod_mem fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hz
    have hbr : b r ∈ RelativeRoot.indivisiblePositiveRoots i (-ν) := hrange ▸ ⟨r, rfl⟩
    have hbroot : b r ∈ relativeRoots i := hbr.1.1
    have hmem := conj_mem_rootGroupPoints n₀⁻¹ (hgs r)
    rw [Subgroup.coe_inv, inv_inv] at hmem
    rw [MulAut.conj_apply, inv_inv]
    refine RelativeRoot.subgroup_le_dynamicUnipotent i ν ?_ _ hmem
    set g' := weylAction i n₀⁻¹ (b r) with hg'
    have hg'root : g' ∈ relativeRoots i := weylAction_mapsTo_relativeRoots i n₀⁻¹ hbroot
    rcases lt_or_gt_of_ne (hν g' hg'root) with hlt | hgt
    · exfalso
      have hpos : -g' ∈ positiveRelativeRoots i ν :=
        ⟨hneg g' hg'root, by rw [map_neg, LinearMap.neg_apply]; omega⟩
      have h1 := hneg₀ _ hpos
      rw [map_neg, hg', weylAction_apply_inv_apply, map_neg, LinearMap.neg_apply] at h1
      have h2 := hbr.2
      rw [map_neg] at h2
      omega
    · exact hgt
  -- run the folding argument on `c = u⁻⁻¹`
  have hupx : up • D.apartmentMap x = um⁻¹ • D.apartmentMap x := by
    rw [eq_inv_smul_iff, ← mul_smul, h]
  obtain ⟨v, hv, y, hcy, hor⟩ := D.exists_iwasawa_fold hG hi ν hν hcs hfac
    (cs.length (QuotientGroup.mk n₀)) n₀ rfl um⁻¹ (hconj _ (Subgroup.inv_mem _ hum)) x
  rcases hor with hlt | ⟨hyx, e, he, hefix, hce⟩
  · exfalso
    have hyx : x = y := by
      apply D.eq_of_unipotent_smul_apartmentMap_eq hG hi ν hν
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hup)
      rw [mul_smul, hupx, hcy, inv_smul_smul]
    rw [hyx, vsub_self, map_zero] at hlt
    exact lt_irrefl _ hlt
  · have hv1 : v = 1 := by
      have hvneg : v ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (CommGroupScheme.groupHom ν ≫ i))).carrier (Over.mk (𝟙 _)) := by
        rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
        have hve : v = um⁻¹ * e⁻¹ := by rw [hce]; group
        rw [hve]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hum) (Subgroup.inv_mem _ he)
      exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
        (CommGroupScheme.groupHom ν ≫ i) hvneg (Dynamic.unipotent_le_parabolic _ _ hv)
    rw [hv1, one_mul] at hce
    have humx : um • D.apartmentMap x = D.apartmentMap x := by
      rw [← inv_inv um, hce, inv_smul_eq_iff, hefix]
    refine ⟨humx, ?_⟩
    rw [hupx, inv_smul_eq_iff, humx]

/-- **Ordered negative–central–positive factors of a point stabilizer.** Let `bn` and `bp`
enumerate injectively the indivisible roots positive on `-ν` and on `ν`. Let `t` be a
normalizer point acting trivially on characters and fixing `x`. If root points `gn j ∈ U_{bn j}(k)`
and `gp j ∈ U_{bp j}(k)` have product `(∏ gn) t (∏ gp)` fixing the image of `x`, then every
factor lies in its depth-zero filtration at `x`. -/
theorem mem_filtration_of_orderedProduct_mul_smul_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter i ν) (x : D.Apartment)
    {nneg npos : ℕ} (bn : Fin nneg → characterLattice S) (hbn : Function.Injective bn)
    (hrn : Set.range bn = RelativeRoot.indivisiblePositiveRoots i (-ν))
    (bp : Fin npos → characterLattice S) (hbp : Function.Injective bp)
    (hrp : Set.range bp = RelativeRoot.indivisiblePositiveRoots i ν)
    (gn : Fin nneg → rationalPoints G) (hgn : ∀ j, gn j ∈ rootGroupPoints i (bn j))
    (gp : Fin npos → rationalPoints G) (hgp : ∀ j, gp j ∈ rootGroupPoints i (bp j))
    (t : normalizerPoints i) (ht : weylAction i t = 1) (htx : t • x = x)
    (hfix : ((List.ofFn gn).prod * (t : rationalPoints G) * (List.ofFn gp).prod) •
      D.apartmentMap x = D.apartmentMap x) :
    (∀ j, gn j ∈ D.filtration x (bn j) 0) ∧ (∀ j, gp j ∈ D.filtration x (bp j) 0) := by
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have htx' : (t : rationalPoints G) • D.apartmentMap x = D.apartmentMap x := by
    rw [← D.apartmentMap_smul, htx]
  -- the conjugated positive factors
  set gp' : Fin npos → rationalPoints G :=
    fun j => (t : rationalPoints G) * gp j * (t : rationalPoints G)⁻¹ with hgp'_def
  have ht1 : ∀ a, weylAction i t a = a := fun a => by rw [ht]; rfl
  have hgp' (j : Fin npos) : gp' j ∈ rootGroupPoints i (bp j) := by
    have h := conj_mem_rootGroupPoints t (hgp j)
    rwa [ht1] at h
  have hprod' : (List.ofFn gp').prod =
      (t : rationalPoints G) * (List.ofFn gp).prod * (t : rationalPoints G)⁻¹ := by
    rw [← MulAut.conj_apply, map_list_prod, List.map_ofFn]
    rfl
  have hum : (List.ofFn gn).prod ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    have hr : bn r ∈ RelativeRoot.indivisiblePositiveRoots i (-ν) := hrn ▸ ⟨r, rfl⟩
    exact RelativeRoot.subgroup_le_dynamicUnipotent i (-ν) hr.2 _ (hgn r)
  have hup : (List.ofFn gp').prod ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    have hr : bp r ∈ RelativeRoot.indivisiblePositiveRoots i ν := hrp ▸ ⟨r, rfl⟩
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ν hr.2 _ (hgp' r)
  have hfix' : ((List.ofFn gn).prod * (List.ofFn gp').prod) • D.apartmentMap x =
      D.apartmentMap x := by
    have hinv : (t : rationalPoints G)⁻¹ • D.apartmentMap x = D.apartmentMap x := by
      rw [inv_smul_eq_iff, htx']
    rw [hprod', ← mul_assoc, ← mul_assoc, mul_smul, hinv, hfix]
  obtain ⟨hneg, hpos⟩ :=
    D.smul_apartmentMap_eq_of_mul_smul_apartmentMap_eq hG hi ν hν hum hup x hfix'
  refine ⟨fun j => D.mem_filtration_of_orderedProduct_smul_apartmentMap_eq hG hi x (-ν) hνneg
    bn hbn hrn gn hgn hneg j, fun j => ?_⟩
  have h := D.mem_filtration_of_orderedProduct_smul_apartmentMap_eq hG hi x ν hν
    bp hbp hrp gp' hgp' hpos j
  have hc := D.conj_mem_filtration t⁻¹ h
  have htinv : t⁻¹ • x = x := by rw [inv_smul_eq_iff, htx]
  have ht1' : weylAction i t⁻¹ (bp j) = bp j := by rw [map_inv, ht, inv_one]; rfl
  rw [htinv, ht1'] at hc
  have heq : ((t⁻¹ : normalizerPoints i) : rationalPoints G) * gp' j *
      ((t⁻¹ : normalizerPoints i) : rationalPoints G)⁻¹ = gp j := by
    rw [hgp'_def, Subgroup.coe_inv]
    group
  rwa [heq] at hc

end KPApartmentData

end Langlands.Geometry.Building
