import Langlands.Representation.Plancherel.RenardLatticeComparisonStatement
import Langlands.Representation.Plancherel.RationalImageLattice
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharactersStatement

/-! # Uniformizer realization and finite index of the split-component valuation image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The ambient valuation of a uniformizer point is the pairing of the
restricted character with its cocharacter. -/
theorem rationalCharacterValuation_map_uniformizerSection (s : T.toGrp ⟶ Z)
    (c : cocharacterLattice T) (χ : rationalCharacters Z) :
    (rationalCharacterValuation Z
        (rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd c)))).toAdd χ =
      latticePairing T (rationalCharacters.equivCharacterLattice T (characterRestrict s χ)) c := by
  rw [← rationalCharacterValuation_characterRestrict]
  have h := CocharacterUniformizer.rationalCharacterValuation_latticeSection F T
    (rationalCharacters.equivCharacterLattice T (characterRestrict s χ)) c
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- Every split-torus point has the ambient valuation of a uniformizer point. -/
theorem exists_rationalCharacterValuation_map_eq (s : T.toGrp ⟶ Z)
    (hT : IsSplitTorus T.toGrp) (t : rationalPoints T.toGrp) :
    ∃ c : cocharacterLattice T,
      rationalCharacterValuation Z
          (rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd c))) =
        rationalCharacterValuation Z (rationalPoints.map s t) := by
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F T hT).2.2 t
  refine ⟨c.toAdd, ?_⟩
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro χ
  rw [rationalCharacterValuation_map_uniformizerSection,
    ← rationalCharacterValuation_characterRestrict]
  have h := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff F T t c).mp hc
    (rationalCharacters.equivCharacterLattice T (characterRestrict s χ))
  rw [AddEquiv.symm_apply_apply] at h
  exact h.symm

/-- A finite-index restriction range makes the uniformizer valuation injective. -/
theorem cocharacter_eq_of_rationalCharacterValuation_eq (s : T.toGrp ⟶ Z)
    (hT : IsSplitTorus T.toGrp) (hindex : (characterRestrict s).range.FiniteIndex)
    {c d : cocharacterLattice T}
    (h : rationalCharacterValuation Z
        (rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd c))) =
      rationalCharacterValuation Z
        (rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd d)))) :
    c = d := by
  let := CocharacterUniformizer.latticePairing_isPerfPair F T hT
  have hinj := (LinearMap.IsPerfPair.bijective_right (latticePairing T)).injective
  apply hinj
  apply LinearMap.ext
  intro α
  change latticePairing T α c = latticePairing T α d
  have hn : (characterRestrict s).range.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  obtain ⟨χ, hχ⟩ := AddSubgroup.nsmul_index_mem (characterRestrict s).range
    ((rationalCharacters.equivCharacterLattice T).symm α)
  have hc := congrArg (fun v => v.toAdd χ) h
  simp only [rationalCharacterValuation_map_uniformizerSection, hχ, map_nsmul,
    AddEquiv.apply_symm_apply, LinearMap.smul_apply, nsmul_eq_mul] at hc
  exact mul_left_cancel₀ (by exact_mod_cast hn) hc

/-- The valuation is a bijection from the uniformizer subgroup onto the actual
image of the split-torus points. -/
theorem bijOn_C0_splitValuationImage (s : T.toGrp ⟶ Z)
    (hT : IsSplitTorus T.toGrp) (hindex : (characterRestrict s).range.FiniteIndex) :
    Set.BijOn (rationalCharacterValuation Z).rangeRestrict
      (C0 T s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨uniformizerSection T c, rfl⟩
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ h
    have hv := congrArg Subtype.val h
    have hcd := cocharacter_eq_of_rationalCharacterValuation_eq s hT hindex
      (c := c.toAdd) (d := d.toAdd) hv
    change rationalPoints.map s (uniformizerSection T c) =
      rationalPoints.map s (uniformizerSection T d)
    rw [show c = Multiplicative.ofAdd c.toAdd from rfl,
      show d = Multiplicative.ofAdd d.toAdd from rfl, hcd]
  · rintro _ ⟨t, rfl⟩
    obtain ⟨c, hc⟩ := exists_rationalCharacterValuation_map_eq s hT t
    refine ⟨rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd c)),
      (mem_C0 T s _).mpr ⟨c, rfl⟩, ?_⟩
    exact Subtype.ext hc

/-- If restriction of rational characters is injective, every actual valuation
value has a positive power in the split-torus image. -/
theorem pow_index_mem_splitValuationImage (s : T.toGrp ⟶ Z)
    (hT : IsSplitTorus T.toGrp) (hinj : Function.Injective (characterRestrict s))
    (y : rationalCharacterValuationImage Z) :
    y ^ (characterRestrict s).range.index ∈ splitValuationImage s := by
  let := CocharacterUniformizer.latticePairing_isPerfPair F T hT
  set N := (characterRestrict s).range.index
  let e := AddMonoidHom.ofInjective hinj
  let m : characterLattice T →+ (characterRestrict s).range :=
    { toFun := fun α => ⟨N • (rationalCharacters.equivCharacterLattice T).symm α,
        AddSubgroup.nsmul_index_mem _ _⟩
      map_zero' := by ext; simp
      map_add' := fun α β => by ext; simp }
  let ν : characterLattice T →ₗ[ℤ] ℤ :=
    ((y.val.toAdd.comp e.symm.toAddMonoidHom).comp m).toIntLinearMap
  obtain ⟨c, hc⟩ := (LinearMap.IsPerfPair.bijective_right (latticePairing T)).surjective ν
  refine ⟨uniformizerSection T (Multiplicative.ofAdd c), ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro χ
  change (rationalCharacterValuation Z
      (rationalPoints.map s (uniformizerSection T (Multiplicative.ofAdd c)))).toAdd χ =
    (y ^ N).val.toAdd χ
  rw [rationalCharacterValuation_map_uniformizerSection]
  have hν := LinearMap.congr_fun hc (rationalCharacters.equivCharacterLattice T
    (characterRestrict s χ))
  change latticePairing T _ c = ν _ at hν
  rw [hν]
  have he : e.symm (m (rationalCharacters.equivCharacterLattice T (characterRestrict s χ))) =
      N • χ := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply, map_nsmul]
    apply Subtype.ext
    change N • (rationalCharacters.equivCharacterLattice T).symm
        (rationalCharacters.equivCharacterLattice T (characterRestrict s χ)) = _
    rw [AddEquiv.symm_apply_apply]
    rfl
  change y.val.toAdd (e.symm (m _)) = _
  rw [he, map_nsmul, Subgroup.coe_pow, toAdd_pow, AddMonoidHom.nsmul_apply]

/-- Injective restriction gives finite index of the actual split-torus image. -/
theorem finiteIndex_splitValuationImage_of_injective (hZ : IsConnectedReductive Z)
    (s : T.toGrp ⟶ Z) (hs : IsSplitComponent s)
    (hinj : Function.Injective (characterRestrict s)) :
    (splitValuationImage s).FiniteIndex := by
  have hindex := hs.finiteIndex_range_characterRestrict hZ
  have hT : IsSplitTorus T.toGrp := hs.1.1.1
  have := (rationalCharacterLattice F Z hZ).2
  have hfin : Module.Finite ℤ (Additive (rationalCharacterValuationImage Z)) :=
    rationalImage_moduleFinite Z
  have hN : (characterRestrict s).range.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have h := CharacterRestrictionFiniteIndex.finiteIndex_of_nsmul_mem
    (Subgroup.toAddSubgroup (splitValuationImage s)) hN fun y =>
      pow_index_mem_splitValuationImage s hT hinj y.toMul
  exact ⟨h.index_ne_zero⟩

/-- Injective restriction to a split component gives both conjuncts of the
split-component lattice statement. -/
theorem splitComponentLattice_of_injective (hZ : IsConnectedReductive Z)
    (s : T.toGrp ⟶ Z) (hs : IsSplitComponent s)
    (hinj : Function.Injective (characterRestrict s)) :
    (splitValuationImage s).FiniteIndex ∧
      Set.BijOn (rationalCharacterValuation Z).rangeRestrict
        (C0 T s : Set (rationalPoints Z))
        (splitValuationImage s : Set (rationalCharacterValuationImage Z)) :=
  ⟨finiteIndex_splitValuationImage_of_injective hZ s hs hinj,
    bijOn_C0_splitValuationImage s hs.1.1.1 (hs.finiteIndex_range_characterRestrict hZ)⟩

/-- The split-component lattice statement follows from detection of nonzero
rational characters by central split tori. -/
theorem splitComponentLatticeStatement_of_centralSplitTorusCharacter
    (hS : CentralSplitTorusCharacterStatement.{u}) :
    SplitComponentLatticeStatement.{u} := by
  intro F _ _ _ _ Z hZ T s hs
  exact splitComponentLattice_of_injective hZ s hs
    (characterRestrict_injective_of_centralSplitTorusCharacter hS hZ hs)

/-- The split-component lattice statement follows from the character
restriction statement. -/
theorem splitComponentLatticeStatement_of_characterRestriction
    (hR : CharacterRestrictionStatement.{u}) :
    SplitComponentLatticeStatement.{u} := by
  intro F _ _ _ _ Z hZ T s hs
  exact splitComponentLattice_of_injective hZ s hs (hR F Z hZ T s hs).1

end Langlands.Plancherel.RenardCartan
