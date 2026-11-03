import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # Intrinsic uniformizer sections for every actual split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

variable (F : Type u) [Field F]
  (A : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Splitness transports the published integral perfect pairing to the actual torus. -/
theorem latticePairing_isPerfPair (hA : IsSplitTorus A.toGrp) :
    (latticePairing A).IsPerfPair := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hA
  let eC : A ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact latticePairing_isPerfPair_of_split eC

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A section representative is characterized by its actual integer valuations. -/
theorem mem_normKernel_mul_section_inv_iff (a : rationalPoints A.toGrp)
    (c : Multiplicative (cocharacterLattice A)) :
    a * (latticeSection F A c)⁻¹ ∈ Plancherel.rationalCommonNormKernel A.toGrp ↔
      ∀ α : characterLattice A,
        (Plancherel.rationalCharacterValuation A.toGrp a).toAdd
          ((rationalCharacters.equivCharacterLattice A).symm α) =
          latticePairing A α c.toAdd := by
  rw [Plancherel.mem_rationalCommonNormKernel_iff_valuation]
  have hv (α : characterLattice A) :
      (Plancherel.rationalCharacterValuation A.toGrp
        (a * (latticeSection F A c)⁻¹)).toAdd
          ((rationalCharacters.equivCharacterLattice A).symm α) =
        (Plancherel.rationalCharacterValuation A.toGrp a).toAdd
          ((rationalCharacters.equivCharacterLattice A).symm α) -
          latticePairing A α c.toAdd := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, AddMonoidHom.add_apply,
      AddMonoidHom.neg_apply]
    rw [show c = Multiplicative.ofAdd c.toAdd from rfl,
      rationalCharacterValuation_latticeSection]
    rfl
  constructor
  · intro h α
    exact sub_eq_zero.mp ((hv α).symm.trans (h _))
  · intro h χ
    have ht := hv (rationalCharacters.equivCharacterLattice A χ)
    have hχ := h (rationalCharacters.equivCharacterLattice A χ)
    rw [AddEquiv.symm_apply_apply] at ht
    rw [AddEquiv.symm_apply_apply] at hχ
    rw [ht, hχ, sub_self]

/-- All three intrinsic section properties hold for an arbitrary actual split torus. -/
theorem isUniformizerLatticeSection (hA : IsSplitTorus A.toGrp) :
    IsUniformizerLatticeSection F A := by
  let := latticePairing_isPerfPair F A hA
  have hinj := (LinearMap.IsPerfPair.bijective_right (latticePairing A)).injective
  refine ⟨?_, (fun c α => rationalCharacterValuation_latticeSection F A α c), ?_⟩
  · intro c d hcd
    apply Multiplicative.toAdd.injective
    apply hinj
    apply LinearMap.ext
    intro α
    change latticePairing A α c.toAdd = latticePairing A α d.toAdd
    rw [← rationalCharacterValuation_latticeSection F A α c.toAdd,
      ← rationalCharacterValuation_latticeSection F A α d.toAdd]
    exact congrArg (fun a => (Plancherel.rationalCharacterValuation A.toGrp a).toAdd
      ((rationalCharacters.equivCharacterLattice A).symm α)) hcd
  · intro a
    let f : characterLattice A →ₗ[ℤ] ℤ :=
      ((Plancherel.rationalCharacterValuation A.toGrp a).toAdd.comp
        (rationalCharacters.equivCharacterLattice A).symm.toAddMonoidHom).toIntLinearMap
    obtain ⟨c, hc⟩ := (LinearMap.IsPerfPair.bijective_right (latticePairing A)).surjective f
    have hval (α : characterLattice A) :
        (Plancherel.rationalCharacterValuation A.toGrp a).toAdd
          ((rationalCharacters.equivCharacterLattice A).symm α) =
          latticePairing A α c :=
      (LinearMap.congr_fun hc α).symm
    refine ⟨Multiplicative.ofAdd c,
      (mem_normKernel_mul_section_inv_iff F A a _).mpr hval, ?_⟩
    intro d hd
    apply Multiplicative.toAdd.injective
    apply hinj
    apply LinearMap.ext
    intro α
    change latticePairing A α d.toAdd = latticePairing A α c
    rw [← (mem_normKernel_mul_section_inv_iff F A a d).mp hd α, hval]

/-- The exact published arbitrary-universe, arbitrary-actual-split-torus target. -/
theorem splitTorusUniformizerSection :
    SplitTorusUniformizerSectionStatement.{u} := by
  intro F _ _ _ _ A hA
  exact isUniformizerLatticeSection F A hA

end Langlands.GroupScheme.CocharacterUniformizer
