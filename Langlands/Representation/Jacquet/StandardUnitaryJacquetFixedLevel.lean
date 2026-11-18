import Langlands.Representation.Exponents.StandardUnitaryInducedJacquetNorms
import Langlands.Representation.Jacquet.StandardCentralContraction

/-! # Uniform fixed levels in the original standard induced Jacquet family -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

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
  (I : Finset (RationalPointFamily.SimpleRoot i ν))

/-- The original normalized induction of an unramified twist of the original
literal standard Levi representation. -/
abbrev standardUnramifiedInducedObject
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)) :=
  (normalizedInductionFunctor
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))).obj
      (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))

/-- The untwisted induced fixed dimension at the given actual ambient level. -/
def standardInducedFixedOrder
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (L : OpenSubgroup (rationalPoints G)) : ℕ :=
  Jacquet.inducedFixedNilpotenceOrder
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) τ L

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  (J : Finset (RationalPointFamily.SimpleRoot i ν)) {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

include hKc hPK hA in
/-- At every actual standard Iwahori level the fixed dimension of the same
ordinary normalized Jacquet object is bounded uniformly across all unramified
source twists by the original untwisted induced fixed dimension. -/
theorem finiteDimensional_finrank_standardUnramifiedJacquet_fixed_le
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτ : τ.IsAdmissible)
    (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (hLstd : StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L.toSubgroup)
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    let Jψ := standardOrdinaryJacquetObject (i := i) (ν := ν)
      (J := RationalPointFamily.rootSet i ν J) (standardUnramifiedInducedObject hG hi hν I τ ψ)
    FiniteDimensional ℂ
        (fixedVectors Jψ.representation
          (L.toSubgroup.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype)) ∧
      Module.finrank ℂ
        (fixedVectors Jψ.representation
          (L.toSubgroup.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype)) ≤
        standardInducedFixedOrder hG hi hν I τ L := by
  intro Jψ
  obtain ⟨⟨ζ, hζ⟩, _⟩ :=
    standardCocharacter F G hG S i hi ν hν (RationalPointFamily.rootSet i ν J)
      (RationalPointFamily.rootSet_subset i ν J)
  have hc := hA.centralStrictElement_isIwahoriContraction i ν hi hζ L hLstd
  have hdim := Jacquet.finrank_fixed_normalizedJacquet_unramifiedInduction_le
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    τ (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) hτ
    (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))
    (standardOppositeUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν J))
    L hL hc ψ
  have := hdim.1
  let e := fixedVectorsEquiv
    (standardNormalizedJacquetOrdinaryEquiv (i := i) (ν := ν)
      (J := RationalPointFamily.rootSet i ν J) (standardUnramifiedInducedObject hG hi hν I τ ψ))
    (L.toSubgroup.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype)
  refine ⟨Module.Finite.of_injective e.symm.toLinearMap e.symm.injective, ?_⟩
  exact e.finrank_eq.symm.le.trans hdim.2

omit hKc hPK in
/-- In the original standard family, all strictly contracting generalized
exponent norms at the specified actual component point have a common bound
strictly below one. -/
theorem exists_standardUnitaryJacquet_contracting_norm_bound
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible) (a : rationalPoints A.toGrp) :
    ∃ θ : ℝ≥0, θ < 1 ∧
      ∀ ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I),
        (∀ m, ‖(ψ.val m : ℂ)‖ = 1) → ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsGeneralizedEigencharacter
            (((standardOrdinaryJacquetObject (i := i) (ν := ν)
              (J := RationalPointFamily.rootSet i ν J)
              (standardUnramifiedInducedObject hG hi hν I τ ψ)).representation).comp
                (standardComponentHom hA)) χ →
            ‖(χ a : ℂ)‖₊ < 1 → ‖(χ a : ℂ)‖₊ ≤ θ := by
  classical
  obtain ⟨R, hR, hmem⟩ := exists_finite_standardUnitaryInducedJacquet_exponentNorms
    hG hi hν I J hA τ hτirr hτadm a
  let S : Finset ℝ≥0 := (hR.subset (Set.inter_subset_left : R ∩ Set.Iio 1 ⊆ R)).toFinset
  refine ⟨S.sup id, (Finset.sup_lt_iff (by norm_num)).mpr ?_, ?_⟩
  · intro s hs
    exact ((Set.Finite.mem_toFinset _).mp hs).2
  · intro ψ hψ χ hχ hχnorm
    apply Finset.le_sup (f := id)
    exact (Set.Finite.mem_toFinset _).mpr ⟨hmem ψ hψ χ hχ, hχnorm⟩

include hKc hPK in
/-- For the original standard induced coefficient tensors, a common actual
standard right-invariance level and contraction of every nonunitary Jacquet
exponent give the existing uniform split-annihilator property. The fixed
degrees, common root gap, admissibility, stable pairing and fixed-source
constant-term realization are all derived. -/
theorem hasUniformSplitAnnihilators_standardUnramifiedConstantTerms
    {κ : Type*}
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτirr : τ.IsIrreducible) (hτadm : τ.IsAdmissible)
    (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (hLstd : StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L.toSubgroup)
    {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
    (hB : CompactOpenNormalBasis K0 B)
    (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)
    (ψ : κ → unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I))
    (hψ : ∀ ω m, ‖((ψ ω).val m : ℂ)‖ = 1)
    (t : ∀ ω, CoefficientTensor (standardUnramifiedInducedObject hG hi hν I τ (ψ ω)))
    (a : rationalPoints A.toGrp) :
    let Vψ := fun ω => standardUnramifiedInducedObject hG hi hν I τ (ψ ω)
    let Jψ := fun ω => standardOrdinaryJacquetObject (i := i) (ν := ν)
      (J := RationalPointFamily.rootSet i ν J) (Vψ ω)
    let CT := fun ω => standardConstantTerm hA (fun g => coefficientTensorMap (Vψ ω) (t ω) g)
    (∀ ω (k : L.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
      continuous_subtype_val) (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)),
        CT ω (m * k) = CT ω m) →
    (∀ ω (χ : rationalPoints A.toGrp →* ℂˣ),
      IsGeneralizedEigencharacter ((Jψ ω).representation.comp (standardComponentHom hA)) χ →
      (¬ ∀ b, ‖(χ b : ℂ)‖ = 1) → ‖(χ a : ℂ)‖ < 1) →
    HasUniformSplitAnnihilators (standardComponentHom hA) a CT := by
  classical
  intro Vψ Jψ CT hinv hcontract
  let LM := L.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).subtype
    continuous_subtype_val
  have hLM : IsCompact (LM : Set (standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))) :=
    (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)).isClosedEmbedding_subtypeVal.isCompact_preimage hL
  let W := fun ω => fixedVectors (Jψ ω).representation LM.toSubgroup
  let d := standardInducedFixedOrder hG hi hν I τ L
  have hdim := fun ω => finiteDimensional_finrank_standardUnramifiedJacquet_fixed_le
    hG hi hν I hKc hPK J hA τ hτadm L hL hLstd (ψ ω)
  have : ∀ ω, FiniteDimensional ℂ (W ω) := fun ω => (hdim ω).1
  have hd : ∀ ω, Module.finrank ℂ (W ω) ≤ d := fun ω => (hdim ω).2
  have hW : ∀ ω b, ∀ y ∈ W ω,
      (Jψ ω).representation (standardComponentHom hA b) y ∈ W ω := fun ω b _ hy =>
    apply_mem_fixedVectors_of_central (Jψ ω).representation
      (standardComponentHom hA) (standardComponentHom_commute hA) LM.toSubgroup b hy
  have hV : ∀ ω, (Vψ ω).IsAdmissible := by
    intro ω
    exact CompactInduction.induced_isAdmissible
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
      K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
      (τ.twist (ψ ω).val.toMonoidHom (unramifiedCharacter_isOpen_ker _ (ψ ω)))
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
      ((SmoothRep.isAdmissible_twist_iff _ _ τ).mpr hτadm)
  obtain ⟨⟨ζ, hζ⟩, _⟩ :=
    standardCocharacter F G hG S i hi ν hν (RationalPointFamily.rootSet i ν J)
      (RationalPointFamily.rootSet_subset i ν J)
  have hCT : ∀ ω, CT ω ∈ coefficientSpaceFrom (Jψ ω).representation (W ω) := by
    intro ω
    let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
    have hAd : D.Admits (Vψ ω).representation (Vψ ω).isSmooth :=
      standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem (Vψ ω).representation (hV ω)
    obtain ⟨b, hb⟩ := D.exists_isStablePairing hAd
    exact standardConstantTerm_mem_fixedJacquet_coefficientSpace hG hi hν hζ hB hA hmem
      (Vψ ω) (hV ω) hb (t ω) LM hLM (hinv ω)
  obtain ⟨θ, hθ, hgap⟩ := exists_standardUnitaryJacquet_contracting_norm_bound
    hG hi hν I J hA τ hτirr hτadm a
  apply hasUniformSplitAnnihilators_of_fixedLevel_coefficients
    (fun ω => (Jψ ω).representation) (standardComponentHom hA) a W hW d hd CT hCT
    (θ := (θ : ℝ)) θ.coe_nonneg (by exact_mod_cast hθ)
  intro ω χ hχ hχU
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have h1 := map_one_of_mem_jointGenEigenspace
    ((Jψ ω).representation.comp (standardComponentHom hA)) hy0 hy.2
  have hm := map_mul_of_mem_jointGenEigenspace
    ((Jψ ω).representation.comp (standardComponentHom hA)) hy0 hy.2
  let χu := jointCharacter χ h1 hm
  have hgen : IsGeneralizedEigencharacter
      ((Jψ ω).representation.comp (standardComponentHom hA)) χu := by
    refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨d, y, hy0, ?_⟩
    intro b
    change (((Jψ ω).representation (standardComponentHom hA b) - χ b • 1) ^ d) y = 0
    exact pow_eq_zero_of_mem_jointGenEigenspace_of_finrank_le
      ((Jψ ω).representation.comp (standardComponentHom hA)) (W ω) (hW ω)
        (hd ω) hy.1 hy.2 b
  have hχuU : ¬ ∀ b, ‖(χu b : ℂ)‖ = 1 := by
    intro hu
    exact hχU hu
  have hlt : ‖(χu a : ℂ)‖₊ < 1 := by
    exact_mod_cast hcontract ω χu hgen hχuU
  have hle : ‖(χu a : ℂ)‖ ≤ (θ : ℝ) := by
    exact_mod_cast hgap (ψ ω) (hψ ω) χu hgen hlt
  exact hle

end Langlands.HarishChandraSchwartz
