import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic
import Langlands.BushnellKutzko.StratumApproximationReduction

/-! # Ramification index and residue degree in a tower of local fields

For finite extensions `F ⊆ E ⊆ K` of a nonarchimedean local field `F`, with `E` carrying its
spectral local-field structure, the ramification indices and residue degrees of the
Library's integral-closure construction multiply. -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uK

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]
  (K : Type uK) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- An element of `K` is integral over the spectral integers of `E` exactly when it is
integral over the integers of `F`. -/
theorem isIntegral_spectralInteger_iff (x : K) :
    letI := LocalField.FiniteExtension.valuativeRel F E
    IsIntegral 𝒪[E] x ↔ IsIntegral 𝒪[F] x := by
  let := LocalField.FiniteExtension.valuativeRel F E
  let A := subfieldIntegers F E
  have : Algebra.IsIntegral 𝒪[F] A :=
    inferInstanceAs (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have hA : IsIntegral 𝒪[E] x ↔ IsIntegral A x := by
    let e := subfieldIntegerEquiv F E
    constructor
    · intro h
      exact h.map_of_comp_eq e.symm.toRingHom (RingHom.id K) (by ext a; rfl)
    · intro h
      exact h.map_of_comp_eq e.toRingHom (RingHom.id K) (by ext a; rfl)
  rw [hA]
  exact ⟨fun h => isIntegral_trans (A := A) x h, fun h => h.tower_top⟩

/-- The integral closures of the two integer rings in `K` are the same subring. -/
def subfieldIntegersTowerEquiv :
    letI := LocalField.FiniteExtension.valuativeRel F E
    subfieldIntegers E K ≃+* subfieldIntegers F K :=
  letI := LocalField.FiniteExtension.valuativeRel F E
  { toFun := fun x => ⟨x, (isIntegral_spectralInteger_iff F E K x).mp x.2⟩
    invFun := fun x => ⟨x, (isIntegral_spectralInteger_iff F E K x).mpr x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }


/-- A unit of the integer ring of `E` stays a unit of the integer ring of `K`. -/
def subfieldIntegersUnitMap (u : (subfieldIntegers F E)ˣ) : (subfieldIntegers F K)ˣ where
  val := ⟨algebraMap E K (u : subfieldIntegers F E),
    (u : subfieldIntegers F E).2.map ((IsScalarTower.toAlgHom F E K).restrictScalars 𝒪[F])⟩
  inv := ⟨algebraMap E K ((u⁻¹ : (subfieldIntegers F E)ˣ) : subfieldIntegers F E),
    ((u⁻¹ : (subfieldIntegers F E)ˣ) : subfieldIntegers F E).2.map
      ((IsScalarTower.toAlgHom F E K).restrictScalars 𝒪[F])⟩
  val_inv := by
    apply Subtype.ext
    change algebraMap E K _ * algebraMap E K _ = 1
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  inv_val := by
    apply Subtype.ext
    change algebraMap E K _ * algebraMap E K _ = 1
    rw [← map_mul, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one, map_one]

variable [FiniteDimensional E K]

/-- Ramification indices multiply in the tower `F ⊆ E ⊆ K`, where `E` carries its spectral
local-field structure. -/
theorem subfieldRamificationIndex_tower :
    letI := LocalField.FiniteExtension.valuativeRel F E
    subfieldRamificationIndex F K =
      subfieldRamificationIndex F E * subfieldRamificationIndex E K := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have : FiniteDimensional F K := Module.Finite.trans E K
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isDiscreteValuationRing F K
  let := subfieldIntegers_isDiscreteValuationRing E K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨ϖE, hϖE⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F K)
  obtain ⟨u1, h1⟩ := baseUniformizer_factorization F E hπ hϖE
  obtain ⟨u3, h3⟩ := baseUniformizer_factorization F K hπ hϖK
  let ψ := subfieldIntegersTowerEquiv F E K
  have hϖE' : Irreducible (subfieldIntegerEquiv F E ϖE) := hϖE.map _
  obtain ⟨u2, h2⟩ := baseUniformizer_factorization E K hϖE' (hϖK.map ψ.symm)
  set e1 := subfieldRamificationIndex F E
  set e2 := subfieldRamificationIndex E K
  set e3 := subfieldRamificationIndex F K
  -- The three factorizations, read in `E` and `K`.
  have h1E : algebraMap F E (π : F) =
      ((u1 : subfieldIntegers F E) : E) * ((ϖE : subfieldIntegers F E) : E) ^ e1 := by
    have := congrArg (fun z : subfieldIntegers F E => (z : E)) h1
    simp at this
    exact this
  have h2K : algebraMap E K ((ϖE : subfieldIntegers F E) : E) =
      ((u2 : subfieldIntegers E K) : K) * ((ψ.symm ϖK : subfieldIntegers E K) : K) ^ e2 := by
    have := congrArg (fun z : subfieldIntegers E K => (z : K)) h2
    simp at this
    exact this
  have h3K : algebraMap F K (π : F) =
      ((u3 : subfieldIntegers F K) : K) * ((ϖK : subfieldIntegers F K) : K) ^ e3 := by
    have := congrArg (fun z : subfieldIntegers F K => (z : K)) h3
    simp at this
    exact this
  have hψ : ((ψ.symm ϖK : subfieldIntegers E K) : K) = ((ϖK : subfieldIntegers F K) : K) := rfl
  let w : (subfieldIntegers F K)ˣ :=
    subfieldIntegersUnitMap F E K u1 * (Units.map ψ.toMonoidHom u2) ^ e1
  have hK : ((u3 : subfieldIntegers F K) : K) * ((ϖK : subfieldIntegers F K) : K) ^ e3 =
      ((w : subfieldIntegers F K) : K) * ((ϖK : subfieldIntegers F K) : K) ^ (e2 * e1) := by
    rw [← h3K, IsScalarTower.algebraMap_apply F E K, h1E, map_mul, map_pow, h2K, hψ]
    change _ = ((subfieldIntegersUnitMap F E K u1 : subfieldIntegers F K) : K) *
      ((ψ u2 : subfieldIntegers F K) : K) ^ e1 * _
    change _ = algebraMap E K _ * ((u2 : subfieldIntegers E K) : K) ^ e1 * _
    ring
  have hA : (u3 : subfieldIntegers F K) * ϖK ^ e3 = (w : subfieldIntegers F K) * ϖK ^ (e2 * e1) :=
    Subtype.ext (by simpa using hK)
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖK hϖK u3 w e3 (e2 * e1) hA
  rw [this, mul_comm]

/-- Residue degrees multiply in the tower `F ⊆ E ⊆ K`. -/
theorem subfieldResidueDegree_tower :
    letI := LocalField.FiniteExtension.valuativeRel F E
    subfieldResidueDegree F K = subfieldResidueDegree F E * subfieldResidueDegree E K := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have : FiniteDimensional F K := Module.Finite.trans E K
  have hK := subfieldRamificationIndex_mul_residueDegree F K
  have hE := subfieldRamificationIndex_mul_residueDegree F E
  have hEK := subfieldRamificationIndex_mul_residueDegree E K
  have hdeg := Module.finrank_mul_finrank F E K
  have he := subfieldRamificationIndex_tower F E K
  have hpos : 0 < subfieldRamificationIndex F K := by
    have : 0 < Module.finrank F K := Module.finrank_pos
    rw [← hK] at this
    exact Nat.pos_of_mul_pos_right this
  rw [he] at hK hpos
  rw [← hdeg, ← hE, ← hEK] at hK
  have hK' : (subfieldRamificationIndex F E * subfieldRamificationIndex E K) *
      subfieldResidueDegree F K = (subfieldRamificationIndex F E * subfieldRamificationIndex E K) *
      (subfieldResidueDegree F E * subfieldResidueDegree E K) := by
    rw [hK]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos hK'

end Langlands.BushnellKutzko
