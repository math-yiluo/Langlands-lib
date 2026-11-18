import Langlands.Representation.Jacquet.StandardUnitaryJacquetFixedLevel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientAnnulusAnnihilators

/-! # Uniform backward recovery for the original unitary constant-term family -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- The positive members of a finite set of nonnegative real numbers lie in
one annulus whose lower endpoint is positive and at most one. -/
theorem exists_positive_annulus_of_finite {R : Set ℝ≥0} (hR : R.Finite) :
    ∃ eta Λ : ℝ, 0 < eta ∧ eta ≤ 1 ∧ 1 ≤ Λ ∧
      ∀ r ∈ R, 0 < r → eta ≤ (r : ℝ) ∧ (r : ℝ) ≤ Λ := by
  classical
  let s : Finset ℝ≥0 :=
    insert 1 ((hR.subset (Set.inter_subset_left : R ∩ Set.Ioi 0 ⊆ R)).toFinset)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ r ∈ s, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · norm_num
    · exact ((Set.Finite.mem_toFinset _).mp hr).2
  refine ⟨(s.min' hs : ℝ), (s.max' hs : ℝ), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hpos _ (s.min'_mem hs)
  · exact_mod_cast s.min'_le 1 (Finset.mem_insert_self _ _)
  · exact_mod_cast s.le_max' 1 (Finset.mem_insert_self _ _)
  · intro r hr hr0
    have hr' : r ∈ s :=
      Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).mpr ⟨hr, hr0⟩)
    exact ⟨by exact_mod_cast s.min'_le r hr', by exact_mod_cast s.le_max' r hr'⟩

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

/-- A single positive annulus contains the exponent norms at `a` for the
ordinary normalized Jacquet actions of all original unitary induced fibers. -/
abbrev HasStandardUnitaryJacquetExponentAnnulus
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (a : rationalPoints A.toGrp) : Prop :=
    ∃ eta Λ : ℝ, 0 < eta ∧ eta ≤ 1 ∧ 1 ≤ Λ ∧
      ∀ ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            (((standardOrdinaryJacquetObject (i := i) (ν := ν)
              (J := RationalPointFamily.rootSet i ν J)
              (standardUnramifiedInducedObject hG hi hν I τ ψ)).representation).comp
                (standardComponentHom hA)) χ →
            eta ≤ ‖(χ a : ℂ)‖ ∧ ‖(χ a : ℂ)‖ ≤ Λ

/-- An irreducible admissible source gives one positive annulus at each
specified component point, for the full family of Jacquet exponents. -/
theorem exists_standardUnitaryJacquet_exponent_annulus
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible) (a : rationalPoints A.toGrp) :
    HasStandardUnitaryJacquetExponentAnnulus hG hi hν I J hA τ a := by
  obtain ⟨R, hR, hmem⟩ := exists_finite_standardUnitaryInducedJacquet_exponentNorms
    hG hi hν I J hA τ hτirr hτadm a
  obtain ⟨eta, Λ, heta, heta1, hΛ, hbound⟩ := exists_positive_annulus_of_finite hR
  refine ⟨eta, Λ, heta, heta1, hΛ, fun ψ hψ χ hχ => ?_⟩
  exact hbound _ (hmem ψ hψ χ hχ) (by
    exact_mod_cast norm_pos_iff.mpr (χ a).ne_zero)

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

include hKc hPK in
/-- At one common actual standard level, the chosen full constant terms
of all original unitary fibers admit a uniform bound by any finite later
segment along the specified component ray. -/
theorem exists_standardUnitaryConstantTerm_tail_bound
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible)
    (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (hLstd : StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L.toSubgroup)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hB : CompactOpenNormalBasis K0 B)
    (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)
    (a : rationalPoints A.toGrp) :
    ∃ D : ℝ, 0 < D ∧ ∀
      (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)),
      (∀ m, ‖(ψ.val m : ℂ)‖ = 1) →
      ∀ t : CoefficientTensor (standardUnramifiedInducedObject hG hi hν I τ ψ),
      let CT := standardConstantTerm hA
        (fun g => coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ ψ) t g)
      (∀ (k : L.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
        continuous_subtype_val) (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)),
        CT (m * k) = CT m) →
      ∀ (r : ℕ) (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)),
        ‖CT m‖ ≤ D ^ r *
          ∑ n ∈ Finset.range
            (r * (standardInducedFixedOrder hG hi hν I τ L *
              standardInducedFixedOrder hG hi hν I τ L) + 1),
            ‖CT (m * (standardComponentHom hA a) ^ (r + n))‖ := by
  classical
  obtain ⟨eta, Λ, heta0, heta1, hΛ, hbound⟩ :=
    exists_standardUnitaryJacquet_exponent_annulus hG hi hν I J hA τ hτirr hτadm a
  let d := standardInducedFixedOrder hG hi hν I τ L
  let D := ((d * d + 1 : ℕ) : ℝ) *
    ((eta ^ (d * d))⁻¹ * (2 ^ (d * d) * Λ ^ (d * d)))
  refine ⟨D, ?_, ?_⟩
  · dsimp only [D]
    have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
    positivity
  · intro ψ hψ t CT hinv r m
    let Vψ := standardUnramifiedInducedObject hG hi hν I τ ψ
    let Jψ := standardOrdinaryJacquetObject (i := i) (ν := ν)
      (J := RationalPointFamily.rootSet i ν J) Vψ
    let LM := L.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
      continuous_subtype_val
    have hLM : IsCompact (LM : Set (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))) :=
      (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).isClosedEmbedding_subtypeVal.isCompact_preimage hL
    let W := fixedVectors Jψ.representation LM.toSubgroup
    obtain ⟨hfd, hd⟩ := finiteDimensional_finrank_standardUnramifiedJacquet_fixed_le
      hG hi hν I hKc hPK J hA τ hτadm L hL hLstd ψ
    have : FiniteDimensional ℂ W := hfd
    have hW : ∀ b, ∀ y ∈ W, Jψ.representation (standardComponentHom hA b) y ∈ W :=
      fun b _ hy => apply_mem_fixedVectors_of_central Jψ.representation
        (standardComponentHom hA) (standardComponentHom_commute hA) LM.toSubgroup b hy
    have hV : Vψ.IsAdmissible := by
      exact CompactInduction.induced_isAdmissible
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
        K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
        (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
        (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
        ((SmoothRep.isAdmissible_twist_iff _ _ τ).mpr hτadm)
    obtain ⟨⟨ζ, hζ⟩, _⟩ :=
      standardCocharacter F G hG S i hi ν hν (RationalPointFamily.rootSet i ν J)
        (RationalPointFamily.rootSet_subset i ν J)
    let E := standardCasselmanPairingData hG hi hν hζ hB hA hmem
    have hAd : E.Admits Vψ.representation Vψ.isSmooth :=
      standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem Vψ.representation hV
    obtain ⟨b, hb⟩ := E.exists_isStablePairing hAd
    have hCT : CT ∈ coefficientSpaceFrom Jψ.representation W :=
      standardConstantTerm_mem_fixedJacquet_coefficientSpace hG hi hν hζ hB hA hmem
        Vψ hV hb t LM hLM hinv
    have hroots : ∀ χ, W ⊓ jointGenEigenspace
        (Jψ.representation.comp (standardComponentHom hA)) χ ≠ ⊥ →
        eta ≤ ‖χ a‖ ∧ ‖χ a‖ ≤ Λ := by
      intro χ hχ
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
      have h1 := map_one_of_mem_jointGenEigenspace
        (Jψ.representation.comp (standardComponentHom hA)) hy0 hy.2
      have hmul := map_mul_of_mem_jointGenEigenspace
        (Jψ.representation.comp (standardComponentHom hA)) hy0 hy.2
      let χu := jointCharacter χ h1 hmul
      have hgen : IsGeneralizedEigencharacter
          (Jψ.representation.comp (standardComponentHom hA)) χu := by
        refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨d, y, hy0, ?_⟩
        intro b
        change ((Jψ.representation (standardComponentHom hA b) - χ b • 1) ^ d) y = 0
        exact pow_eq_zero_of_mem_jointGenEigenspace_of_finrank_le
          (Jψ.representation.comp (standardComponentHom hA)) W hW hd hy.1 hy.2 b
      exact hbound ψ hψ χu hgen
    exact norm_le_sum_tail_of_coefficient_annulus Jψ.representation
      (standardComponentHom hA) a W hW hd heta0 heta1 hΛ hroots hCT r m

end Langlands.HarishChandraSchwartz
