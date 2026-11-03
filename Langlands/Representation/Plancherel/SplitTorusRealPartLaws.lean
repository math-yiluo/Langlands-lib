import Langlands.Representation.Plancherel.SplitTorusNormFormula
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Choice independence, functoriality and image comparison of real parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A B : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The logarithmic modulus evaluated on any multiplicative lift of the lattice. -/
def latticeLiftLog (χ : rationalPoints A.toGrp →* ℂˣ)
    (σ : Multiplicative (cocharacterLattice A) →* rationalPoints A.toGrp) :
    cocharacterLattice A →+ ℝ where
  toFun c := normLog (LocalField.residueCardinality F) (characterNorm χ (σ (.ofAdd c)))
  map_zero' := by
    change normLog _ (characterNorm χ (σ 1)) = 0
    rw [map_one, map_one, normLog_one]
  map_add' c d := by
    change normLog _ (characterNorm χ (σ (.ofAdd c * .ofAdd d))) = _
    rw [map_mul, map_mul, normLog_mul]

/-- The section construction performed with an arbitrary lattice lift.
Its independence theorem below imposes the valuation normalization on that lift. -/
def normalizedRealPartFromLift (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (σ : Multiplicative (cocharacterLattice A) →* rationalPoints A.toGrp) :
    RealTorusSpace.Vstar A :=
  (RealTorusSpace.characterDualEquiv hA).symm (extendLatticeLog (latticeLiftLog χ σ))

theorem pair_normalizedRealPartFromLift_tmul (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (σ : Multiplicative (cocharacterLattice A) →* rationalPoints A.toGrp)
    (r : ℝ) (c : cocharacterLattice A) :
    RealTorusSpace.pair A (normalizedRealPartFromLift hA χ σ) (r ⊗ₜ[ℤ] c) =
      r * normLog (LocalField.residueCardinality F) (characterNorm χ (σ (.ofAdd c))) := by
  have h := LinearMap.congr_fun
    ((RealTorusSpace.characterDualEquiv hA).apply_symm_apply
      (extendLatticeLog (latticeLiftLog χ σ))) (r ⊗ₜ[ℤ] c)
  exact h

/-- Cocharacter evaluation at any order-one field unit has the same positive valuation. -/
theorem valuation_cocharacterPoints_of_order_one (hA : IsSplitTorus A.toGrp)
    (π : Fˣ) (hπ : (fieldOrderUnits F π).toAdd = 1) (c : cocharacterLattice A) :
    (valuation hA (CocharacterUniformizer.cocharacterPoints F A c π)).toAdd =
      (1 : ℝ) ⊗ₜ[ℤ] c := by
  symm
  apply (BruhatTits.Cartan.eq_centralizerValuation_iff _ _ _ _).mpr
  intro α
  rw [BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply, RealTorusSpace.eval_tmul, one_mul]
  have he := CocharacterUniformizer.rationalCharacterEval_cocharacterPoints F A
    (rationalCharacters.equivCharacterLattice A α) c π
  have hv : (rationalCharacterValuation A.toGrp
      (CocharacterUniformizer.cocharacterPoints F A c π)).toAdd α =
      latticePairing A (rationalCharacters.equivCharacterLattice A α) c := by
    rw [rationalCharacterValuation_apply]
    rw [show rationalCharacterEval α
      (CocharacterUniformizer.cocharacterPoints F A c π) =
        π ^ latticePairing A (rationalCharacters.equivCharacterLattice A α) c
      from he, map_zpow, toAdd_zpow, hπ, smul_eq_mul, mul_one]
  exact (congrArg (fun n : ℤ => (n : ℝ)) hv).symm

/-- The existing positive valuation is natural under actual split-torus morphisms. -/
theorem valuation_map (hA : IsSplitTorus A.toGrp) (hB : IsSplitTorus B.toGrp)
    (f : A ⟶ B) (a : rationalPoints A.toGrp) :
    (valuation hB (rationalPoints.map (CommGroupScheme.groupHom f) a)).toAdd =
      RealTorusSpace.cocharacterMapReal f (valuation hA a).toAdd := by
  symm
  apply (BruhatTits.Cartan.eq_centralizerValuation_iff _ _ _ _).mpr
  intro α
  rw [BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply, RealTorusSpace.eval_eq_pair,
    RealTorusSpace.pair_cocharacterMapReal, rationalCharacterRestrictReal_tmul,
    ← RealTorusSpace.eval_eq_pair]
  have h := BruhatTits.Cartan.centralizerValuation_spec (𝟙 A.toGrp)
    (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA) a
    (characterRestrict (CommGroupScheme.groupHom f) α)
  simpa only [BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply,
    rationalCharacterValuation_characterRestrict,
    rationalCharacters.equivCharacterLattice, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.refl_apply] using h

/-- Values on any integral lattice basis determine the same intrinsic parameter. -/
theorem normalizedRealPart_eq_of_basis (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    {I : Type*} (b : Module.Basis I ℤ (cocharacterLattice A))
    (phi : RealTorusSpace.Vstar A)
    (hphi : ∀ i, RealTorusSpace.pair A phi ((1 : ℝ) ⊗ₜ[ℤ] b i) =
      sectionLog χ (b i)) :
    normalizedRealPart hA χ = phi := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply (b.baseChange ℝ).ext
  intro i
  change RealTorusSpace.pair A (normalizedRealPart hA χ)
      ((b.baseChange ℝ) i) = RealTorusSpace.pair A phi ((b.baseChange ℝ) i)
  rw [Module.Basis.baseChange_apply, pair_normalizedRealPart_tmul, one_mul, hphi]

section CanonicalTopology

variable [IsAffine A.X.left]

local instance lawsPointTopology : TopologicalSpace (rationalPoints A.toGrp) :=
  rationalPointTopology F A.X

/-- Every normalized lattice lift computes the same real part of a smooth character. -/
theorem normalizedRealPartFromLift_eq (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (σ : Multiplicative (cocharacterLattice A) →* rationalPoints A.toGrp)
    (hσ : ∀ c, (valuation hA (σ (.ofAdd c))).toAdd = (1 : ℝ) ⊗ₜ[ℤ] c) :
    normalizedRealPartFromLift hA χ σ = normalizedRealPart hA χ := by
  apply (RealTorusSpace.characterDualEquiv hA).injective
  apply AlgebraTensorModule.ext
  intro r c
  change RealTorusSpace.pair A (normalizedRealPartFromLift hA χ σ) (r ⊗ₜ[ℤ] c) =
    RealTorusSpace.pair A (normalizedRealPart hA χ) (r ⊗ₜ[ℤ] c)
  rw [pair_normalizedRealPartFromLift_tmul,
    show (r ⊗ₜ[ℤ] c : RealTorusSpace.V A) =
      r • ((1 : ℝ) ⊗ₜ[ℤ] c) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, smul_eq_mul, ← hσ c,
    pair_normalizedRealPart_valuation hA χ hχ]

/-- Every order-one uniformizer gives the same logarithmic lattice values. -/
theorem sectionLog_eq_of_order_one (hA : IsSplitTorus A.toGrp)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints A.toGrp)))
    (π : Fˣ) (hπ : (fieldOrderUnits F π).toAdd = 1)
    (c : cocharacterLattice A) :
    normLog (LocalField.residueCardinality F)
      (characterNorm χ (CocharacterUniformizer.cocharacterPoints F A c π)) =
      sectionLog χ c := by
  have h := pair_normalizedRealPart_valuation hA χ hχ
    (CocharacterUniformizer.cocharacterPoints F A c π)
  rw [valuation_cocharacterPoints_of_order_one hA π hπ, pair_normalizedRealPart_tmul,
    one_mul] at h
  exact h.symm

/-- Image-character pullbacks are smooth for the canonical rational-point topology. -/
theorem isOpen_ker_imageCharacterPullback (hA : IsSplitTorus A.toGrp)
    (ψ : rationalImageCharacters A.toGrp) :
    IsOpen ((rationalImageCharacterPullback A.toGrp ψ).ker :
      Set (rationalPoints A.toGrp)) := by
  let : Smooth A.X.hom := hA.smooth
  let : IsTopologicalGroup (rationalPoints A.toGrp) :=
    rationalPoint_isTopologicalGroup F A.toGrp
  exact Subgroup.isOpen_mono
    (fun _ ha => rationalImageCharacterPullback_trivial A.toGrp ψ ha)
    (isOpen_rationalCommonNormKernel A.toGrp)

/-- Exact comparison with the existing normalized functional on the actual image. -/
theorem pair_normalizedRealPart_imageCharacterPullback (hA : IsSplitTorus A.toGrp)
    (ψ : rationalImageCharacters A.toGrp) (a : rationalPoints A.toGrp) :
    RealTorusSpace.pair A
      (normalizedRealPart hA (rationalImageCharacterPullback A.toGrp ψ))
        (valuation hA a).toAdd =
      rationalImageRealPart A.toGrp ψ
        (Additive.ofMul (rationalValuationImageProjection A.toGrp a)) := by
  rw [pair_normalizedRealPart_valuation hA _ (isOpen_ker_imageCharacterPullback hA ψ)]
  rfl

variable [IsAffine B.X.left]

local instance targetPointTopology : TopologicalSpace (rationalPoints B.toGrp) :=
  rationalPointTopology F B.X

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Actual morphisms preserve smoothness by continuous pullback. -/
theorem isOpen_ker_comp_points (f : A ⟶ B)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints B.toGrp))) :
    IsOpen ((χ.comp (rationalPoints.map (CommGroupScheme.groupHom f))).ker :
      Set (rationalPoints A.toGrp)) := by
  exact hχ.preimage (continuous_rationalPointMap F f.hom.hom)

omit [IsAffine A.X.left] in
/-- The normalized real part is natural under actual morphisms of split tori. -/
theorem normalizedRealPart_comp_points (hA : IsSplitTorus A.toGrp)
    (hB : IsSplitTorus B.toGrp) (f : A ⟶ B)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints B.toGrp))) :
    normalizedRealPart hA (χ.comp (rationalPoints.map (CommGroupScheme.groupHom f))) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (normalizedRealPart hB χ) := by
  apply normalizedRealPart_unique hA _ _
  intro a
  rw [← RealTorusSpace.pair_cocharacterMapReal, ← valuation_map hA hB f a]
  exact norm_eq_rpow_normalizedRealPart hB χ hχ _

omit [IsAffine A.X.left] in
/-- The raw natural-log parameter has the same actual-morphism naturality. -/
theorem rawLogRealPart_comp_points (hA : IsSplitTorus A.toGrp)
    (hB : IsSplitTorus B.toGrp) (f : A ⟶ B)
    (χ : rationalPoints B.toGrp →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (rationalPoints B.toGrp))) :
    rawLogRealPart hA (χ.comp (rationalPoints.map (CommGroupScheme.groupHom f))) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (rawLogRealPart hB χ) := by
  rw [rawLogRealPart, rawLogRealPart, normalizedRealPart_comp_points hA hB f χ hχ,
    map_smul]

end CanonicalTopology

section RankZero

variable (F) (I : Type u) [Finite I] [IsEmpty I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I

/-- Every character parameter of an actual rank-zero coordinate torus is zero. -/
theorem normalizedRealPart_rankZero (hT : IsSplitTorus (𝕋).toGrp)
    (χ : rationalPoints (𝕋).toGrp →* ℂˣ) :
    normalizedRealPart hT χ = 0 :=
  RealTorusSpace.eq_zero_of_isEmpty_character F I _

theorem rawLogRealPart_rankZero (hT : IsSplitTorus (𝕋).toGrp)
    (χ : rationalPoints (𝕋).toGrp →* ℂˣ) :
    rawLogRealPart hT χ = 0 := by
  rw [rawLogRealPart, normalizedRealPart_rankZero F I hT χ, smul_zero]

end RankZero

end Langlands.Plancherel.SplitTorus
