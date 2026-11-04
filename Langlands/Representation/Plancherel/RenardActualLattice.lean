import Langlands.Representation.Plancherel.RenardIntegralRestriction
import Langlands.Representation.Plancherel.RenardDominantValuation
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness

/-! # Actual lattice comparison from restriction evaluation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}
  (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

local instance renardActualLatticeRationalCharactersIntModule : Module ℤ (rationalCharacters Z) := AddCommGroup.toIntModule _
local instance renardActualLatticeCharacterLatticeIntModule : Module ℤ (characterLattice S) := AddCommGroup.toIntModule _
local instance renardActualLatticeCocharacterLatticeIntModule : Module ℤ (cocharacterLattice S) := AddCommGroup.toIntModule _

/-- The actual restriction map as an integer linear map. -/
def integralCharacterRestriction : rationalCharacters Z →ₗ[ℤ] characterLattice S :=
  (characterRestriction s).toIntLinearMap

attribute [-instance] AddCommGroup.toIntModule in
/-- Integral pairing with the actual restricted-character image. -/
def restrictedIntegralPairing :
    cocharacterLattice S →ₗ[ℤ] Module.Dual ℤ (integralCharacterRestriction s).range :=
  (integralCharacterRestriction s).range.subtype.dualMap.comp (latticePairing S).flip

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
attribute [-instance] AddCommGroup.toIntModule in
@[simp] theorem restrictedIntegralPairing_apply (c : cocharacterLattice S)
    (χ : rationalCharacters Z) :
    restrictedIntegralPairing s c ((integralCharacterRestriction s).rangeRestrict χ) =
      latticePairing S (characterRestriction s χ) c := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A split torus's cocharacter lattice embeds in its real scalar extension. -/
theorem cocharacter_tmul_injective (hS : IsSplitTorus S.toGrp) :
    Function.Injective (fun c : cocharacterLattice S => (1 : ℝ) ⊗ₜ[ℤ] c) := by
  let := CocharacterUniformizer.latticePairing_isPerfPair F S hS
  intro c d hcd
  apply (LinearMap.IsPerfPair.bijective_right (latticePairing S)).injective
  apply LinearMap.ext
  intro α
  have he := congrArg (RealTorusSpace.eval S α) hcd
  simp only [RealTorusSpace.eval_tmul, one_mul] at he
  exact_mod_cast he

include h in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
attribute [-instance] AddCommGroup.toIntModule in
/-- The given real comparison makes the restricted integral pairing injective. -/
theorem restrictedIntegralPairing_injective (hS : IsSplitTorus S.toGrp) :
    Function.Injective (restrictedIntegralPairing s) := by
  intro c d hcd
  apply cocharacter_tmul_injective hS
  apply h.injective
  apply AddMonoidHom.ext
  intro χ
  change RealTorusSpace.eval S (characterRestriction s χ) ((1 : ℝ) ⊗ₜ[ℤ] c) =
    RealTorusSpace.eval S (characterRestriction s χ) ((1 : ℝ) ⊗ₜ[ℤ] d)
  simp only [RealTorusSpace.eval_tmul, one_mul]
  exact congrArg (fun n : ℤ => (n : ℝ))
    (LinearMap.congr_fun hcd ((integralCharacterRestriction s).rangeRestrict χ))

include h in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
attribute [-instance] AddCommGroup.toIntModule in
/-- The actual restricted integral pairing has finite-index image. -/
theorem restrictedIntegralPairing_finiteIndex (hS : IsSplitTorus S.toGrp) :
    (restrictedIntegralPairing s).range.toAddSubgroup.FiniteIndex := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let := hI
  let := Fintype.ofFinite I
  let : Module ℤ (I → ℤ) := Pi.module I (fun _ => ℤ) ℤ
  let eS : S ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let eB : characterLattice S ≃ₗ[ℤ] (I → ℤ) := ((characterLattice.congr eS).trans
    (splitTorus.characterLatticeEquiv F I)).toIntLinearEquiv
  let eC : cocharacterLattice S ≃ₗ[ℤ] (I → ℤ) := ((cocharacterLattice.congr eS).trans
    (splitTorus.cocharacterLatticeEquiv F I)).toIntLinearEquiv
  let := Module.Free.of_equiv eB.symm
  let := Module.Finite.equiv eB.symm
  exact IntegralRestriction.finiteIndex_range_of_injective
    (eC.trans eB.symm) (integralCharacterRestriction s).range
    (restrictedIntegralPairing s)
    (restrictedIntegralPairing_injective s h ⟨I, hI, ⟨e⟩⟩)

include h in
/-- An actual integer valuation vanishes on the kernel of restriction. -/
theorem rationalCharacterValuation_eq_zero_of_restriction_eq_zero
    (z : rationalPoints Z) (χ : rationalCharacters Z)
    (hχ : characterRestriction s χ = 0) :
    (rationalCharacterValuation Z z).toAdd χ = 0 := by
  have hv := centralizerValuation_spec s h z χ
  simp only [hχ, RealTorusSpace.eval_eq_pair, TensorProduct.tmul_zero, map_zero,
    LinearMap.zero_apply] at hv
  exact_mod_cast hv.symm

attribute [-instance] AddCommGroup.toIntModule in
/-- An actual valuation, descended to the restricted-character lattice. -/
def descendedActualValuation (h : Function.Bijective (restrictionEvaluation s))
    (y : rationalCharacterValuationImage Z) :
    Module.Dual ℤ (integralCharacterRestriction s).range :=
  IntegralRestriction.descend (integralCharacterRestriction s)
    ⟨y.val.toAdd.toIntLinearMap, by
      rw [Submodule.mem_dualAnnihilator]
      intro χ hχ
      obtain ⟨z, hz⟩ := y.property
      change y.val.toAdd χ = 0
      rw [← hz]
      exact rationalCharacterValuation_eq_zero_of_restriction_eq_zero s h z χ hχ⟩

attribute [-instance] AddCommGroup.toIntModule in
@[simp] theorem descendedActualValuation_apply (y : rationalCharacterValuationImage Z)
    (χ : rationalCharacters Z) :
    descendedActualValuation s h y ((integralCharacterRestriction s).rangeRestrict χ) =
      y.val.toAdd χ :=
  IntegralRestriction.descend_apply_rangeRestrict _ _ _

attribute [-instance] AddCommGroup.toIntModule in
/-- Actual valuation values as multiplicative integral functionals on the
restricted-character lattice. -/
def actualValuationOnRestriction :
    rationalCharacterValuationImage Z →*
      Multiplicative (Module.Dual ℤ (integralCharacterRestriction s).range) where
  toFun y := Multiplicative.ofAdd (descendedActualValuation s h y)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro a
    obtain ⟨χ, rfl⟩ := (integralCharacterRestriction s).surjective_rangeRestrict a
    change descendedActualValuation s h 1 _ = 0
    rw [descendedActualValuation_apply]
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro a
    obtain ⟨χ, rfl⟩ := (integralCharacterRestriction s).surjective_rangeRestrict a
    change descendedActualValuation s h (x * y) _ =
      descendedActualValuation s h x _ + descendedActualValuation s h y _
    simp only [descendedActualValuation_apply]
    rfl

attribute [-instance] AddCommGroup.toIntModule in
/-- Restriction evaluation loses no actual valuation value. -/
theorem actualValuationOnRestriction_injective :
    Function.Injective (actualValuationOnRestriction s h) := by
  intro x y hxy
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro χ
  have he := congrArg
    (fun q => q.toAdd ((integralCharacterRestriction s).rangeRestrict χ)) hxy
  change descendedActualValuation s h x _ = descendedActualValuation s h y _ at he
  simpa only [descendedActualValuation_apply] using he

attribute [-instance] AddCommGroup.toIntModule in
/-- A uniformizer value corresponds to its restricted integral pairing. -/
@[simp] theorem actualValuationOnRestriction_uniformizer (c : cocharacterLattice S) :
    actualValuationOnRestriction s h
      ((rationalCharacterValuation Z).rangeRestrict
        (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))) =
      Multiplicative.ofAdd (restrictedIntegralPairing s c) := by
  apply Multiplicative.toAdd.injective
  apply LinearMap.ext
  intro a
  obtain ⟨χ, rfl⟩ := (integralCharacterRestriction s).surjective_rangeRestrict a
  change descendedActualValuation s h _ _ = restrictedIntegralPairing s c _
  rw [descendedActualValuation_apply, restrictedIntegralPairing_apply]
  exact rationalCharacterValuation_map_uniformizerSection s c χ

attribute [-instance] AddCommGroup.toIntModule in
/-- The split valuation image is exactly the preimage of the integral pairing
image under restriction evaluation. -/
theorem splitValuationImage_eq_comap (hS : IsSplitTorus S.toGrp) :
    splitValuationImage s =
      ((restrictedIntegralPairing s).range.toAddSubgroup.toSubgroup).comap
        (actualValuationOnRestriction s h) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨c, hc⟩ := exists_rationalCharacterValuation_map_eq s hS t
    have hc' :
        (rationalCharacterValuation Z).rangeRestrict
            (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c))) =
          (rationalCharacterValuation Z).rangeRestrict (rationalPoints.map s t) :=
      Subtype.ext hc
    change (actualValuationOnRestriction s h
      ((rationalCharacterValuation Z).rangeRestrict (rationalPoints.map s t))).toAdd ∈
      (restrictedIntegralPairing s).range
    rw [← hc', actualValuationOnRestriction_uniformizer]
    exact ⟨c, rfl⟩
  · intro hy
    change (actualValuationOnRestriction s h y).toAdd ∈
      (restrictedIntegralPairing s).range at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨uniformizerSection S (Multiplicative.ofAdd c), ?_⟩
    apply actualValuationOnRestriction_injective s h
    change actualValuationOnRestriction s h
      ((rationalCharacterValuation Z).rangeRestrict
        (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))) = _
    rw [actualValuationOnRestriction_uniformizer]
    exact congrArg Multiplicative.ofAdd hc

include h in
/-- The existing real comparison and splitness imply finite index of the
actual split valuation image. -/
theorem finiteIndex_splitValuationImage_of_comparison (hS : IsSplitTorus S.toGrp) :
    (splitValuationImage s).FiniteIndex := by
  have hp := restrictedIntegralPairing_finiteIndex s h hS
  have : (restrictedIntegralPairing s).range.toAddSubgroup.toSubgroup.FiniteIndex :=
    (AddSubgroup.finiteIndex_toSubgroup_iff _).mpr hp
  rw [splitValuationImage_eq_comap s h hS]
  infer_instance

include h in
/-- Uniformizer points are a section of the actual split valuation image. -/
theorem bijOn_C0_splitValuationImage_of_comparison (hS : IsSplitTorus S.toGrp) :
    Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨uniformizerSection S c, rfl⟩
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ hcd
    have hv := centralizerValuation_eq_of_characterValuation_eq s h
      (congrArg Subtype.val hcd)
    have he := congrArg Multiplicative.toAdd hv
    change (centralizerValuation s h
      (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c.toAdd)))).toAdd =
      (centralizerValuation s h
      (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd d.toAdd)))).toAdd at he
    rw [centralizerValuation_uniformizerSection, centralizerValuation_uniformizerSection] at he
    have hco := cocharacter_tmul_injective hS he
    change rationalPoints.map s (uniformizerSection S c) =
      rationalPoints.map s (uniformizerSection S d)
    rw [show c = Multiplicative.ofAdd c.toAdd from rfl,
      show d = Multiplicative.ofAdd d.toAdd from rfl, hco]
  · rintro _ ⟨t, rfl⟩
    obtain ⟨c, hc⟩ := exists_rationalCharacterValuation_map_eq s hS t
    refine ⟨rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)),
      (mem_C0 S s _).mpr ⟨c, rfl⟩, ?_⟩
    exact Subtype.ext hc

end Langlands.Plancherel.RenardCartan
