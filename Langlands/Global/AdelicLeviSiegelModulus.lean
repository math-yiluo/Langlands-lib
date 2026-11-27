import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicPositiveRootCharacterRelation
import Langlands.Global.AdelicParabolicModulus
import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants
import Langlands.GroupScheme.Rational.SubgroupRelativeRootComparison
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Siegel modulus on the norm-one subgroup of a standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.AdelicSiegelFactors

open GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

omit [NumberField F] in
private theorem nonzero_of_positive_pairing {α : characterLattice T}
    (h : 0 < latticePairing T α ν) : α ≠ 0 := by
  rintro rfl
  simp only [map_zero, LinearMap.zero_apply, lt_self_iff_false] at h

private theorem siegelModulus_eq_norm_positiveWeightCharacter
    (hT : IsSplitTorus T.toGrp) {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
    (j : T₀ ⟶ T) (a : intrinsicSubgroup F T₀) :
    siegelModulus F G T i ν T₀ j a =
      ((characterNorm F T.toGrp (positiveWeightCharacter i ν).toMul
        (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val) : ℝ≥0) : ℝ) := by
  classical
  have hΔ : (positiveRelativeRoots i ν).Finite :=
    (hT.finite_relativeRoots i).subset (positiveRelativeRoots_subset_relativeRoots i ν)
  let z := map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val
  let w (α : characterLattice T) : rationalCharacters T.toGrp :=
    Module.finrank F (weightSpace i α) • (rationalCharacters.equivCharacterLattice T).symm α
  have hsum : positiveWeightCharacter i ν = ∑ α ∈ hΔ.toFinset, w α := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hΔ, positiveWeightCharacter, finsum_mem_def]
    apply finsum_congr
    intro α
    by_cases hα : α ∈ positiveRelativeRoots i ν
    · rw [Set.indicator_of_mem hα, ite_eq_left hα.2]
    · rw [Set.indicator_of_notMem hα]
      by_cases hp : 0 < latticePairing T α ν
      · have hz : weightSpace i α = ⊥ := by
          by_contra h
          exact hα ⟨⟨nonzero_of_positive_pairing ν hp, h⟩, hp⟩
        rw [ite_eq_left hp, hz, finrank_bot, zero_smul]
      · rw [ite_eq_right hp, zero_smul]
  let χnorm : rationalCharacters T.toGrp →+ Additive ℝ≥0ˣ :=
    { toFun := fun χ => Additive.ofMul (characterNorm F T.toGrp χ.toMul z)
      map_zero' := characterNorm_zero F T.toGrp z
      map_add' := fun χ ψ => characterNorm_add F T.toGrp χ ψ z }
  rw [siegelModulus, finprod_mem_eq_finite_toFinset_prod _ hΔ, hsum]
  change _ = (((χnorm _).toMul : ℝ≥0) : ℝ)
  rw [map_sum, toMul_sum, Units.coe_prod, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro α _
  change _ = ((characterNorm F T.toGrp (w α).toMul z : ℝ≥0) : ℝ)
  dsimp only [w]
  rw [characterNorm_nsmul]
  congr 2

omit [NumberField F] in
private theorem finite_support_positiveWeightSummand
    (hT : IsSplitTorus T.toGrp) :
    (Function.support (fun α : characterLattice T =>
      (if 0 < latticePairing T α ν then Module.finrank F (weightSpace i α) else 0) •
        (rationalCharacters.equivCharacterLattice T).symm α)).Finite :=
  (hT.finite_weightSupport i).subset (fun α hα hz => hα (by
    change weightSpace i α = ⊥ at hz
    dsimp only
    rw [hz, finrank_bot, ite_self, zero_smul]))

variable [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]

omit [NumberField F] in
private theorem positiveWeightCharacter_add_levi
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    {eta : cocharacterLattice T} (heta : IsStandardCocharacter i ν J eta)
    {l : L ⟶ G} (iL : T.toGrp ⟶ L) (hcomp : iL ≫ l = i)
    (hL : (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy l) :
    positiveWeightCharacter i ν = positiveWeightCharacter iL ν + positiveWeightCharacter i eta := by
  classical
  let : Mono l.hom.hom := hL.1
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT := hi.isSplitSubtorus.1
  have hEq : (AutomorphicAction.conjugation iL).IsEquivariant (AutomorphicAction.conjugation i) l := by
    intro V t x
    rw [← hcomp]
    exact RelativeRoot.conjugation_act_comp iL l V t x
  have hrank (α : characterLattice T) :
      Module.finrank F (weightSpace iL α) =
        if latticePairing T α eta = 0 then Module.finrank F (weightSpace i α) else 0 := by
    rw [(Submodule.equivMapOfInjective (Lie.targetMapLinear l F)
      (Lie.targetMapLinear_injective l F) (weightSpace iL α)).finrank_eq]
    have hmap := hEq.map_actionWeightSpace_eq_inf_range α
    rw [RelativeRoot.actionWeightSpace_conjugation, RelativeRoot.actionWeightSpace_conjugation,
      ← RelativeRoot.tangentSubmodule_range l, hL.2,
      weightSpace_inf_tangentSubmodule_centralizer hT i] at hmap
    rw [hmap]
    by_cases h : latticePairing T α eta = 0
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, finrank_bot]
  rw [positiveWeightCharacter, positiveWeightCharacter, positiveWeightCharacter,
    ← finsum_add_distrib (finite_support_positiveWeightSummand iL ν hT)
      (finite_support_positiveWeightSummand i eta hT)]
  apply finsum_congr
  intro α
  rw [hrank]
  by_cases hbot : weightSpace i α = ⊥
  · rw [hbot, finrank_bot]
    simp only [ite_self, zero_smul, add_zero]
  by_cases hz : α = 0
  · subst α
    have hzero (ζ : cocharacterLattice T) : ¬ 0 < latticePairing T 0 ζ := by
      simp only [map_zero, LinearMap.zero_apply, lt_self_iff_false, not_false_eq_true]
    rw [ite_eq_right (hzero ν), ite_eq_right (hzero ν), ite_eq_right (hzero eta),
      zero_smul, add_zero]
  have hroot : α ∈ relativeRoots i := ⟨hz, hbot⟩
  rcases lt_or_gt_of_ne (hν α hroot) with hneg | hpos
  · have hminus : -α ∈ relativeRoots i :=
      (relativeRootSystem F G hG T i hi).neg_mem_relativeRoots i hT hroot
    have hn := heta.pairing_nonneg_of_positive i ν
      (show -α ∈ positiveRelativeRoots i ν from ⟨hminus, by simpa using neg_pos.mpr hneg⟩)
    have hn' : ¬ 0 < latticePairing T α eta := by simpa using hn
    simp [not_lt.mpr hneg.le, hn']
  · have hn := heta.pairing_nonneg_of_positive i ν
      (show α ∈ positiveRelativeRoots i ν from ⟨hroot, hpos⟩)
    rcases eq_or_lt_of_le hn with he | hp
    · simp [hpos, he.symm]
    · simp [hpos, hp, hp.ne']

/-- The ambient minimal modulus on a positive torus point belonging to the norm-one
subgroup of a standard Levi equals the minimal modulus of that Levi. -/
theorem siegelModulus_eq_levi_of_normOne
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) {l : L ⟶ G}
    (hL : (standardLevi i ν J).IsRepresentedBy l)
    (iL : T.toGrp ⟶ L) (hcomp : iL ≫ l = i)
    {T₀ T₁ : CommGroupScheme (Spec (CommRingCat.of F))}
    (j : T₀ ⟶ T) (k : T₁ ⟶ T)
    (a : intrinsicSubgroup F T₀) (b : intrinsicSubgroup F T₁)
    (hab : map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val =
      map F T₁.toGrp T.toGrp (CommGroupScheme.groupHom k) b.val)
    (hb : positiveMap F L T iL T₁ k b ∈ normOneSubgroup F L) :
    siegelModulus F G T i ν T₀ j a = siegelModulus F L T iL ν T₁ k b := by
  obtain ⟨⟨eta, heta⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let U := Standard.unipotentScheme i ν J
  let u := Standard.unipotentHom i ν J
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy l := by
    rw [← (hcompare eta heta).2.1]
    exact hL
  have hU : (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy u := by
    rw [← (hcompare eta heta).2.2]
    exact Standard.isRepresentedBy_unipotentHom i ν J
  let : IsAffineHom U.X.hom := (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom_source
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : LocallyOfFiniteType U.X.hom := locallyOfFiniteType_unipotent F hU
  have hT := hi.isSplitSubtorus.1
  let c := (Dynamic.centralizerAdjointAction hZ hU).determinantCharacter (Lie.finiteCoordinates U)
  have hchar : characterRestrict iL c = positiveWeightCharacter i eta :=
    characterRestrict_centralizerAdjointDeterminant hT i eta hZ hU iL hcomp (Lie.finiteCoordinates U)
  let t := map F T₁.toGrp T.toGrp (CommGroupScheme.groupHom k) b.val
  have ht : map F T.toGrp L iL t = positiveMap F L T iL T₁ k b := by
    rw [← map_comp_apply_of_hom]
    rfl
  have hUnit : characterNorm F T.toGrp (characterRestrict iL c).toMul t = 1 := by
    rw [show (characterRestrict iL c).toMul = iL ≫ c.toMul from rfl, characterNorm_comp, ht]
    exact (mem_normOneSubgroup F L _).mp hb _
  rw [siegelModulus_eq_norm_positiveWeightCharacter i ν hT j a,
    siegelModulus_eq_norm_positiveWeightCharacter iL ν hT k b, hab,
    positiveWeightCharacter_add_levi i ν hG hi hν heta iL hcomp hZ,
    ← hchar, characterNorm_add, hUnit, mul_one]

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- At a common positive torus point in a standard Levi's norm-one subgroup, the ambient
and Levi minimal Siegel moduli are equal. -/
def AdelicLeviSiegelModulusStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (G L : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom],
    IsConnectedReductive G →
    ∀ (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (l : L ⟶ G), (standardLevi i ν J).IsRepresentedBy l →
    ∀ (iL : T.toGrp ⟶ L), iL ≫ l = i →
    ∀ (T₀ T₁ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T) (k : T₁ ⟶ T) (a : intrinsicSubgroup F T₀) (b : intrinsicSubgroup F T₁),
    map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a.val =
        map F T₁.toGrp T.toGrp (CommGroupScheme.groupHom k) b.val →
    positiveMap F L T iL T₁ k b ∈ normOneSubgroup F L →
    siegelModulus F G T i ν T₀ j a = siegelModulus F L T iL ν T₁ k b

theorem adelicLeviSiegelModulus : AdelicLeviSiegelModulusStatement := by
  intro F _ _ T G L _ _ _ _ hG i hi ν hν J hJ l hL iL hcomp T₀ T₁ j k a b hab hb
  exact siegelModulus_eq_levi_of_normOne i ν hG hi hν J hJ hL iL hcomp j k a b hab hb

end Langlands.Global
