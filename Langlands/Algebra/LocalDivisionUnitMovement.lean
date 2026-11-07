import Langlands.Algebra.DivisionMaximalRootEmbedding
import Langlands.Algebra.DivisionUnitMovement
import Langlands.Algebra.LocalDivisionUnitLift

/-! Moving actual integral units into a full-residue subfield modulo commutators. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

variable {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L]
  (ι : L →ₐ[K] D)

omit [FiniteDimensional K L] in
/-- An original integral polynomial root is also a root after passing to the embedded field. -/
theorem localDivisionSubfield_aeval_base_polynomial
    (f : Polynomial 𝒪[K])
    (b : (localDivisionSubfieldValuation K D ι).integer)
    (hb : f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) b = 0) :
    Polynomial.aeval (b : L) (f.map (algebraMap 𝒪[K] K)) = 0 := by
  let θ := (localDivisionSubfieldValuation K D ι).integer.subtype
  have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D ι) =
      (algebraMap K L).comp (algebraMap 𝒪[K] K) := by
    ext x
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hθ]
  change f.eval₂ (θ.comp (localDivisionSubfieldBaseIntegerMap K D ι)) (θ b) = 0
  rw [← Polynomial.hom_eval₂, hb, map_zero]

/-- The original integral-unit version of local commutator movement. -/
theorem localDivision_move_integerUnit
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (hresdeg : Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) =
        CentralSimple.reducedDegree K D)
    (a : (localReducedNormValuation K D).integerˣ) :
    ∃ c ∈ commutator Dˣ,
      c * Units.map (localReducedNormValuation K D).integer.subtype.toMonoidHom a ∈
        (Units.map ι.toMonoidHom).range := by
  let v := localReducedNormValuation K D
  let R := DivisionValuation.Residue v
  obtain ⟨g, hg⟩ := exists_localDivisionResidue_generator K D
  let z : R := DivisionValuation.reduction v g.val
  have hgen : ∀ y : R, y = 0 ∨ ∃ n : ℕ, y = z ^ n := by
    intro y
    rcases hg y with hy | ⟨n, hn⟩
    · exact Or.inl hy
    · exact Or.inr ⟨n, hn.trans (map_pow _ _ _)⟩
  have hz : z ≠ 0 := isUnit_iff_ne_zero.mp
    (g.isUnit.map (DivisionValuation.reduction v))
  obtain ⟨f, hmon, hmap, hdeg, hirr⟩ :=
    exists_localDivision_residue_minpoly_polynomial K D z
  have heval (q : Polynomial 𝒪[K]) :
      Polynomial.aeval z (q.map (IsLocalRing.residue 𝒪[K])) =
        q.eval₂ (localDivisionBaseReduction K D) z := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0 := by
    rw [← heval, hmap]
    exact minpoly.aeval 𝓀[K] z
  have hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0 := by
    rw [← heval, ← Polynomial.derivative_map, hmap]
    exact (PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral z))).aeval_derivative_ne_zero
      (minpoly.aeval 𝓀[K] z)
  have hfdeg : (f.map (algebraMap 𝒪[K] K)).natDegree =
      CentralSimple.reducedDegree K D := by
    rw [hmon.natDegree_map, hdeg]
    calc
      (minpoly 𝓀[K] z).natDegree = Module.finrank 𝓀[K] R :=
        (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral z)
          (localDivisionResidue_adjoin_eq_top K D z hgen)).finrank.symm
      _ = CentralSimple.reducedDegree K D := hresdeg
  obtain ⟨b, hb, hredb⟩ :=
    localDivisionSubfield_lift_base_polynomial K D ι hsurj f hmon z hroot hder
  have hbu : IsUnit b := by
    apply (DivisionValuation.isUnit_iff_value_eq_one _ b).mpr
    apply (DivisionValuation.reduction_ne_zero_iff _ b).mp
    intro h
    apply hz
    rw [← hredb, h, map_zero]
  let bI := hbu.unit
  let aI := localDivisionSubfieldIntegerUnitLift K D ι hsurj a
  let j := localDivisionSubfieldIntegerMap K D ι
  let tI : v.integerˣ := a * (Units.map j.toMonoidHom aI)⁻¹ * Units.map j.toMonoidHom bI
  let α : Dˣ := Units.map v.integer.subtype.toMonoidHom a
  let aL : Lˣ :=
    Units.map (localDivisionSubfieldValuation K D ι).integer.subtype.toMonoidHom aI
  let bL : Lˣ :=
    Units.map (localDivisionSubfieldValuation K D ι).integer.subtype.toMonoidHom bI
  let t : Dˣ := Units.map v.integer.subtype.toMonoidHom tI
  have htwist : t = fieldMovementTwist ι α aL bL := by
    apply Units.ext
    rfl
  have hreda : Units.map (DivisionValuation.reduction v).toMonoidHom
      (Units.map j.toMonoidHom aI) =
        Units.map (DivisionValuation.reduction v).toMonoidHom a := by
    apply Units.ext
    exact localDivisionSubfieldIntegerUnitLift_spec K D ι hsurj a
  have hredbI : DivisionValuation.reduction v (j bI.val) = z := by
    change localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ bI.val) = z
    rw [hbu.unit_spec]
    exact hredb
  have hredtU : Units.map (DivisionValuation.reduction v).toMonoidHom tI =
      Units.map (DivisionValuation.reduction v).toMonoidHom
        (Units.map j.toMonoidHom bI) := by
    dsimp only [tI]
    rw [map_mul, map_mul, map_inv, hreda, mul_inv_cancel, one_mul]
  have hredt : DivisionValuation.reduction v tI.val = z :=
    (congrArg Units.val hredtU).trans hredbI
  let := residueGeneratorField K D (t : D)
  let E := residueGeneratorSubalgebra K D (t : D)
  have hsurjt : Function.Surjective (localDivisionSubfieldResidueMap K D E.val) := by
    apply localDivisionSubfieldResidueMap_surjective K D E.val tI
    · exact ⟨⟨(t : D), residueGenerator_mem K D (t : D)⟩, rfl⟩
    · intro y
      rcases hgen y with hy | ⟨n, hn⟩
      · exact Or.inl hy
      · exact Or.inr ⟨n, by rw [map_pow, hredt]; exact hn⟩
  obtain ⟨c, hc, _⟩ :=
    localDivisionSubfield_lift_base_polynomial K D E.val hsurjt f hmon z hroot hder
  obtain ⟨u, y, hconj⟩ := exists_unit_conj_into_field_of_maximal_root K D ι t
    (f.map (algebraMap 𝒪[K] K)) (hmon.map _) hirr hfdeg (b : L)
    (localDivisionSubfield_aeval_base_polynomial K D ι f b hb) (c : E)
    (localDivisionSubfield_aeval_base_polynomial K D E.val f c hc)
  exact move_unit_of_conjugate_fieldMovementTwist ι α aL bL y u
    (htwist.symm.trans hconj)

/-- Every original valuation-one unit moves into a full-residue field modulo a commutator. -/
theorem localDivision_move_unit
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (hresdeg : Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) =
        CentralSimple.reducedDegree K D)
    (a : Dˣ) (ha : localReducedNormValuation K D (a : D) = 1) :
    ∃ c ∈ commutator Dˣ, c * a ∈ (Units.map ι.toMonoidHom).range := by
  let a₀ : (localReducedNormValuation K D).integer := ⟨(a : D), ha.le⟩
  have hu : IsUnit a₀ :=
    (DivisionValuation.isUnit_iff_value_eq_one _ a₀).mpr ha
  have hmap : Units.map (localReducedNormValuation K D).integer.subtype.toMonoidHom hu.unit = a := by
    apply Units.ext
    exact congrArg Subtype.val hu.unit_spec
  simpa only [hmap] using localDivision_move_integerUnit K D ι hsurj hresdeg hu.unit

/-- A chosen actual commutator moving the original valuation-one unit into the field. -/
def localDivisionMovementCommutator
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (hresdeg : Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) =
        CentralSimple.reducedDegree K D)
    (a : Dˣ) (ha : localReducedNormValuation K D (a : D) = 1) : Dˣ :=
  Classical.choose (localDivision_move_unit K D ι hsurj hresdeg a ha)

theorem localDivisionMovementCommutator_spec
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (hresdeg : Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) =
        CentralSimple.reducedDegree K D)
    (a : Dˣ) (ha : localReducedNormValuation K D (a : D) = 1) :
    localDivisionMovementCommutator K D ι hsurj hresdeg a ha ∈ commutator Dˣ ∧
      localDivisionMovementCommutator K D ι hsurj hresdeg a ha * a ∈
        (Units.map ι.toMonoidHom).range :=
  Classical.choose_spec (localDivision_move_unit K D ι hsurj hresdeg a ha)

end Langlands.CentralDivision
