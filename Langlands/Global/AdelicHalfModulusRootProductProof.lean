import Langlands.Global.AdelicHalfModulusRootProductStatement
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicMinimalParabolicLineBound

/-! # The half modulus of a standard parabolic as a product over positive roots

`halfModulusRootProduct` proves `HalfModulusRootProductStatement`: on the positive split
component of a standard parabolic `P_J`, `|a^{ρ_J}|² = ∏_{β ∈ Φ⁺} |β(a)|^{m_β}`. The algebraic
input, `characterRestrict_adjointDeterminantCharacter_splitComponent`, identifies the restriction
of `det(Ad | Lie P_J)` to the split component `A_J` with `positiveRootSum`, the sum of the
restrictions of the positive relative roots counted with the dimensions of their weight spaces.
The paired Markdown records the argument. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The character `∑_{β ∈ Φ⁺} m_β · β|_{A_J}` of the split component `A_J` of `P_J`: the sum
over the positive relative roots `β` of the restrictions `f_J ≫ β` along `A_J → T`, each counted
`m_β = dim_F 𝔤_β` times. -/
def positiveRootSum (J : StandardIndex F G 𝓕.i 𝓕.ν) : characterLattice (𝓕.A J) :=
  ∑ᶠ (β : characterLattice 𝓕.T) (_ : β ∈ positiveRelativeRoots 𝓕.i 𝓕.ν),
    Module.finrank F (weightSpace 𝓕.i β) • (𝓕.f J ≫ β)

omit [NumberField F] in
/-- **`2ρ_J` on the split component.** The restriction of `det(Ad | Lie P_J)` along
`A_J → M_J → P_J` is `positiveRootSum J`. -/
theorem characterRestrict_adjointDeterminantCharacter_splitComponent
    (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    rationalCharacters.equivCharacterLattice (𝓕.A J)
        (characterRestrict (𝓕.a J ≫ 𝓕.l J) (Lie.adjointDeterminantCharacter (𝓕.P J))) =
      𝓕.positiveRootSum J := by
  classical
  rw [positiveRootSum]
  have hc := 𝓕.isCompatible J
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.1, 𝓕.f J⟩, hc⟩
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.isSplitSubtorus.1
  obtain ⟨ζ, hζ, hPeq, hZeq⟩ := hc.realization
  have hpcl := hc.parabolic.isClosedSubgroup
  have hlcl : IsClosedSubgroup (𝓕.l J ≫ 𝓕.p J) := hc.levi.isClosedSubgroup.comp hpcl
  let := hpcl.mono
  let := hlcl.mono
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ 𝓕.i)).IsRepresentedBy (𝓕.p J) :=
    ⟨Over.mono_of_mono_left _, hPeq⟩
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ 𝓕.i)).IsRepresentedBy
      (𝓕.l J ≫ 𝓕.p J) :=
    ⟨Over.mono_of_mono_left _, hZeq⟩
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ζ ≫ 𝓕.i)
  let : IsAffineHom (Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ζ ≫ 𝓕.i)).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _).isAffineHom
  let : LocallyOfFiniteType
      (Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ζ ≫ 𝓕.i)).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _).locallyOfFiniteType
  let c := Lie.finiteCoordinates (Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ζ ≫ 𝓕.i))
  have hl : Dynamic.centralizerToParabolic hP hZ = 𝓕.l J :=
    hP.hom_ext (Dynamic.centralizerToParabolic_comp hP hZ)
  have h1 := Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic hP hZ hU c
  rw [hl] at h1
  have h2 := characterRestrict_centralizerAdjointDeterminant hT 𝓕.i ζ hZ hU (𝓕.torus J)
    (𝓕.torus_comp J) c
  have hA : IsSplitTorus (𝓕.A J).toGrp := hc.splitComponent.1.isSplitSubtorus.1
  let : IsAffineHom (𝓕.A J).toGrp.X.hom := hA.isAffineHom
  let : IsAffine (𝓕.A J).toGrp.X.left := isAffine_of_isAffineHom (𝓕.A J).toGrp.X.hom
  have h3 := Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral (𝓕.M J) (𝓕.a J)
    hc.splitComponent.1.2
  have ha : 𝓕.a J = CommGroupScheme.groupHom (𝓕.f J) ≫ 𝓕.torus J :=
    hZ.hom_ext (by rw [Category.assoc, 𝓕.torus_comp J]; exact hc.factor_comp.symm)
  have hE : characterRestrict (𝓕.a J ≫ 𝓕.l J) (Lie.adjointDeterminantCharacter (𝓕.P J)) =
      characterRestrict (CommGroupScheme.groupHom (𝓕.f J)) (positiveWeightCharacter 𝓕.i ζ) := by
    rw [characterRestrict_comp, AddMonoidHom.comp_apply, h1, map_add, h3, add_zero, ha,
      characterRestrict_comp, AddMonoidHom.comp_apply, h2]
  rw [hE]
  have hR := relativeRootSystem F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
  have hsupp : (Function.support fun α : characterLattice 𝓕.T =>
      (if 0 < latticePairing 𝓕.T α ζ then Module.finrank F (weightSpace 𝓕.i α) else 0) •
        (rationalCharacters.equivCharacterLattice 𝓕.T).symm α).Finite := by
    apply (hT.finite_weightSupport 𝓕.i).subset
    intro α hα hbot
    apply hα
    have h0 : Module.finrank F (weightSpace 𝓕.i α) = 0 := by rw [hbot, finrank_bot]
    simp only [h0, ite_self, zero_smul]
  have key := AddMonoidHom.map_finsum
    ((rationalCharacters.equivCharacterLattice (𝓕.A J)).toAddMonoidHom.comp
      (characterRestrict (CommGroupScheme.groupHom (𝓕.f J)))) hsupp
  rw [positiveWeightCharacter]
  refine key.trans ?_
  rw [finsum_mem_def]
  apply finsum_congr
  intro α
  rw [map_nsmul]
  change (if 0 < latticePairing 𝓕.T α ζ then Module.finrank F (weightSpace 𝓕.i α) else 0) •
      (𝓕.f J ≫ α) = _
  by_cases hpos : 0 < latticePairing 𝓕.T α ζ
  · rw [ite_eq_left hpos]
    by_cases hm : Module.finrank F (weightSpace 𝓕.i α) = 0
    · rw [hm, zero_smul]
      by_cases hmem : α ∈ positiveRelativeRoots 𝓕.i 𝓕.ν
      · rw [Set.indicator_of_mem hmem, hm, zero_smul]
      · rw [Set.indicator_of_notMem hmem]
    · have hroot : α ∈ relativeRoots 𝓕.i := by
        refine ⟨?_, ?_⟩
        · rintro rfl
          simp at hpos
        · intro hbot
          apply hm
          rw [hbot, finrank_bot]
      have hmem : α ∈ positiveRelativeRoots 𝓕.i 𝓕.ν := by
        refine ⟨hroot, ?_⟩
        rcases lt_or_gt_of_ne (𝓕.generic α hroot) with hn | hp
        · exfalso
          have hneg : -α ∈ positiveRelativeRoots 𝓕.i 𝓕.ν :=
            ⟨hR.neg_mem_relativeRoots 𝓕.i hT hroot, by
              rw [map_neg, LinearMap.neg_apply]
              omega⟩
          have h := hζ.pairing_nonneg_of_positive 𝓕.i 𝓕.ν hneg
          rw [map_neg, LinearMap.neg_apply] at h
          omega
        · exact hp
      rw [Set.indicator_of_mem hmem]
  · rw [ite_eq_right hpos, zero_smul]
    by_cases hmem : α ∈ positiveRelativeRoots 𝓕.i 𝓕.ν
    · rw [Set.indicator_of_mem hmem]
      have h0 : latticePairing 𝓕.T α ζ = 0 :=
        le_antisymm (not_lt.mp hpos) (hζ.pairing_nonneg_of_positive 𝓕.i 𝓕.ν hmem)
      have hf0 : 𝓕.f J ≫ α = 0 :=
        r.restrict_eq_zero_of_mem_closure
          ((hζ.pairing_eq_zero_iff_mem_closure 𝓕.i 𝓕.ν hmem).mp h0)
      rw [hf0, smul_zero]
    · rw [Set.indicator_of_notMem hmem]

end StandardParabolicFamily

namespace PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F] {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The norm of a multiple of a character is the power of the norm. -/
theorem coe_normCharacter_nsmul (n : ℕ) (χ : characterLattice T)
    (s : AdelicGroupPoints F T.toGrp) :
    ((normCharacter F T (n • χ) s : ℝ≥0) : ℝ) = ((normCharacter F T χ s : ℝ≥0) : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, normCharacter_add, Units.val_mul, NNReal.coe_mul, ih, pow_succ]

/-- The norm of a finite sum of multiples of characters is the product of powers of the
norms. -/
theorem coe_normCharacter_sum {κ : Type*} (t : Finset κ) (n : κ → ℕ)
    (g : κ → characterLattice T) (s : AdelicGroupPoints F T.toGrp) :
    ((normCharacter F T (∑ b ∈ t, n b • g b) s : ℝ≥0) : ℝ) =
      ∏ b ∈ t, ((normCharacter F T (g b) s : ℝ≥0) : ℝ) ^ n b := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, normCharacter_add, Units.val_mul,
      NNReal.coe_mul, ih, coe_normCharacter_nsmul]

/-- `coe_normCharacter_sum` for a finite set and `finsum`/`finprod`. -/
theorem coe_normCharacter_finsum_mem {κ : Type*} {S : Set κ} (hS : S.Finite) (n : κ → ℕ)
    (g : κ → characterLattice T) (s : AdelicGroupPoints F T.toGrp) :
    ((normCharacter F T (∑ᶠ (b : κ) (_ : b ∈ S), n b • g b) s : ℝ≥0) : ℝ) =
      ∏ᶠ (b : κ) (_ : b ∈ S), ((normCharacter F T (g b) s : ℝ≥0) : ℝ) ^ n b := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finprod_mem_eq_finite_toFinset_prod _ hS,
    coe_normCharacter_sum]

end PositiveRealTorus

/-- **The half modulus on the positive split component is a product over positive roots.**
`HalfModulusRootProductStatement` holds. -/
theorem halfModulusRootProduct : HalfModulusRootProductStatement.{u} := by
  intro F _ _ G _ _ _ 𝓕 J s
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.isSplitSubtorus.1
  rw [𝓕.halfModulus_eq_sqrt J, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (NNReal.coe_nonneg _), PositiveRealTorus.positivePointMap_apply,
    ← characterNorm_comp]
  have hkey := 𝓕.characterRestrict_adjointDeterminantCharacter_splitComponent J
  rw [StandardParabolicFamily.positiveRootSum] at hkey
  rw [← PositiveRealTorus.coe_normCharacter_finsum_mem (hT.finite_positiveRelativeRoots 𝓕.i 𝓕.ν),
    ← hkey]
  rfl

end Langlands.Global
