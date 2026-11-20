import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction
import Langlands.Representation.Plancherel.CompactProductInducedCoefficients

/-! # Actual product-induced coefficients at the full-group endpoint -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe uG uV u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ]
  [SecondCountableTopology Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {P M U : Subgroup Γ}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set Γ))
  (hP : P = ⊤) (hM : M = ⊤) (hbot : U = ⊥)
  (A : SmoothRep.{0, uG, uV} ℂ M)
  (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ))
  [LocallyCompactSpace P]
  (hPc : IsClosed (P : Set Γ)) (hm : Continuous h.projection)
  (hPK : ∀ g : Γ, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hΓ : ∀ g : Γ, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

/-- The actual product-induced coefficient carrier at the full-group endpoint
is the coefficient tensor of the original ambient representation. The first
comparison uses the supplied compact subgroup's Haar probability. -/
def fullLeviProductCoefficientTensorEquiv :
    productInducedCoefficientObject h hU A ≃ₗ[ℂ]
      CoefficientTensor (fullLeviAmbientSmoothRep M hM A) :=
  (CompactInduction.coefficientTensorEquiv h hU A K hK hPc hm hPK hΓ hδ hA).toLinearEquiv.trans
    (fullLeviInductionTensorEquiv h hU hP hM hbot A)

/-- The comparison preserves the actual compact-probability coefficient map.
This compares the original functions, with their original normalization. -/
theorem coefficientTensorMap_fullLeviProductCoefficientTensorEquiv
    (F : productInducedCoefficientObject h hU A) :
    coefficientTensorMap (fullLeviAmbientSmoothRep M hM A)
      (fullLeviProductCoefficientTensorEquiv h hU hP hM hbot A K hK hPc hm hPK hΓ hδ hA F) =
        CompactInduction.coefficientMap h hU A K hK hPc hm hPK hΓ hδ hA F :=
  coefficientTensorMap_fullLeviInductionTensorEquiv h hU hP hM hbot A
    (CompactInduction.coefficientTensorEquiv h hU A K hK hPc hm hPK hΓ hδ hA F)

include hP hbot in
/-- Every actual coefficient tensor has a preimage in the product-induced
carrier, with equality of its full coefficient function. -/
theorem exists_fullLeviProductCoefficient_preimage
    (t : CoefficientTensor (fullLeviAmbientSmoothRep M hM A)) :
    ∃ F : productInducedCoefficientObject h hU A,
      CompactInduction.coefficientMap h hU A K hK hPc hm hPK hΓ hδ hA F =
        coefficientTensorMap (fullLeviAmbientSmoothRep M hM A) t := by
  let E := fullLeviProductCoefficientTensorEquiv h hU hP hM hbot A K hK hPc hm hPK hΓ hδ hA
  refine ⟨E.symm t, ?_⟩
  rw [← coefficientTensorMap_fullLeviProductCoefficientTensorEquiv h hU
    hP hM hbot A K hK hPc hm hPK hΓ hδ hA]
  exact congrArg (coefficientTensorMap (fullLeviAmbientSmoothRep M hM A))
    (E.apply_symm_apply t)

end Generic

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]

local instance : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G
local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance : T2Space (rationalPoints G) := rationalPoint_t2Space F G

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  (A : SmoothRep.{0, u, uV} ℂ
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)))
  (hA : A.IsAdmissible)

/-- The existing compact coefficient-tensor comparison on actual full-root data. -/
def rationalFullLeviCompactCoefficientTensorEquiv :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν Finset.univ
  CompactInduction.coefficientTensorEquiv
    (isSemidirectDecomposition_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ))
    (isClosed_standardUnipotentPoints i ν
      (RationalPointFamily.rootSet i ν Finset.univ)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν Finset.univ)
    (continuous_projection_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν Finset.univ hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν Finset.univ rfl
      (RationalPointFamily.rootSet_subset i ν Finset.univ)) hA

/-- The literal full-root product-induced coefficient space on rational
points, identified with ambient coefficient tensors with carrier in `uV`. This is
the generic comparison at the actual standard parabolic for all simple roots. -/
def rationalFullLeviProductCoefficientTensorEquiv :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν Finset.univ
  fullLeviProductCoefficientTensorEquiv
    (isSemidirectDecomposition_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ))
    (isClosed_standardUnipotentPoints i ν
      (RationalPointFamily.rootSet i ν Finset.univ))
    (RationalPointFamily.parabolic_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.unipotent_univ_eq_bot i ν) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν Finset.univ)
    (continuous_projection_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν Finset.univ hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν Finset.univ rfl
      (RationalPointFamily.rootSet_subset i ν Finset.univ)) hA

/-- The rational product comparison is the compact comparison followed by
coefficient-tensor transport along the full-root evaluation equivalence. -/
theorem rationalFullLeviProductCoefficientTensorEquiv_eq_trans :
    rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK A hA =
      (rationalFullLeviCompactCoefficientTensorEquiv hG hi hν hKc hPK A hA).toLinearEquiv.trans
        (coefficientTensorCongr (rationalFullLeviInductionEquiv hG hi hν A)) :=
  rfl

/-- The actual `E_G^G` map at all simple roots is the ordinary coefficient map
after the displayed tensor equivalence, for the unchanged compact measure. -/
theorem coefficientTensorMap_rationalFullLeviProductCoefficientTensorEquiv
    (Φ : productInducedCoefficientObject
      (isSemidirectDecomposition_standard hG hi hν
        (RationalPointFamily.rootSet_subset i ν Finset.univ))
      (isClosed_standardUnipotentPoints i ν
        (RationalPointFamily.rootSet i ν Finset.univ)) A) :
    coefficientTensorMap (fullLeviAmbientSmoothRep _
      (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν) A)
        (rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK A hA Φ) =
      rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK A hA Φ := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν Finset.univ
  have h := coefficientTensorMap_fullLeviProductCoefficientTensorEquiv _ _
    (RationalPointFamily.parabolic_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.unipotent_univ_eq_bot i ν) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν Finset.univ)
    (continuous_projection_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν Finset.univ hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν Finset.univ rfl
      (RationalPointFamily.rootSet_subset i ν Finset.univ)) hA Φ
  -- The two sides carry different, definitionally equal, instance terms. Comparing
  -- whole applications would unfold the coercion, so the maps and the vectors are
  -- compared separately.
  refine (DFunLike.congr ?_ ?_).trans (h.trans (DFunLike.congr ?_ ?_))
  · rfl
  · refine DFunLike.congr ?_ ?_ <;> rfl
  · rfl
  · rfl

/-- Every ambient coefficient tensor at the full root has a product-induced
preimage whose actual `E_G^G` coefficient is the same function. -/
theorem exists_rationalFullLeviProductCoefficient_preimage
    (t : CoefficientTensor (fullLeviAmbientSmoothRep _
      (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν) A)) :
    ∃ Φ : productInducedCoefficientObject
        (isSemidirectDecomposition_standard hG hi hν
          (RationalPointFamily.rootSet_subset i ν Finset.univ))
        (isClosed_standardUnipotentPoints i ν
          (RationalPointFamily.rootSet i ν Finset.univ)) A,
      rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK A hA Φ =
        coefficientTensorMap (fullLeviAmbientSmoothRep _
          (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν) A) t := by
  let E := rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK A hA
  refine ⟨E.symm t, ?_⟩
  rw [← coefficientTensorMap_rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK A hA]
  exact congrArg (coefficientTensorMap _) (E.apply_symm_apply t)

end Rational

end Langlands.HarishChandraSchwartz
