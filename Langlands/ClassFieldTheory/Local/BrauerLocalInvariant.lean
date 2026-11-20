import Langlands.Algebra.BrauerComparison.Naturality
import Langlands.ClassFieldTheory.Local.FiniteLocalInvariantRestriction
import Langlands.ClassFieldTheory.Local.FixedFieldUnitInflationComparison
import Langlands.ClassFieldTheory.Local.SeparableLocalInvariant

noncomputable section

open Langlands.Brauer Langlands.BrauerComparison Langlands.LocalField
open Langlands.LocalGalois.Separable ValuativeRel
open scoped TensorProduct

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace SeparableUnramifiedStage

/-- The stage inflation is the actual relative-to-continuous inflation of the Brauer comparison. -/
theorem inflation_eq_relativeToContinuous (S : SeparableUnramifiedStage K)
    (x : relativeCohomology K S.field 2) :
    S.inflation x = relativeToContinuous K S.field (SeparableClosure K) 2 x := by
  obtain ⟨y, rfl⟩ := (continuousToRelativeEquiv K S.field 2).surjective x
  change fixedFieldUnitInflation K (SeparableClosure K) S.subgroup 2
      (continuousToRelative K S.field 2 y) =
    relativeToContinuous K S.field (SeparableClosure K) 2 (continuousToRelative K S.field 2 y)
  rw [fixedFieldUnitInflation_continuousToRelative, relativeToContinuous_continuousToRelative]
  rfl

end SeparableUnramifiedStage

section Relative

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E)

private theorem separableLocalInvariant_relative_of_eq (S : SeparableUnramifiedStage K)
    (h : S.field = E) (x : relativeCohomology K E 2) :
    separableLocalInvariant K (relativeToContinuous K E (SeparableClosure K) 2 x) =
      spectralUnramifiedInvariant K E hE x := by
  subst E
  rw [← S.inflation_eq_relativeToContinuous K, separableLocalInvariant_inflation]

/-- The absolute value is computed by every actual unramified finite representative. -/
theorem separableLocalInvariant_relative (x : relativeCohomology K E 2) :
    separableLocalInvariant K (relativeToContinuous K E (SeparableClosure K) 2 x) =
      spectralUnramifiedInvariant K E hE x :=
  separableLocalInvariant_relative_of_eq K E hE (SeparableUnramifiedStage.ofIntermediate E hE)
    (SeparableUnramifiedStage.field_ofIntermediate E hE) x

end Relative

section Restriction

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- Cohomological restriction multiplies the absolute value by the finite extension degree. -/
theorem separableLocalInvariant_restriction (hcont : Continuous (algebraMap K L))
    (x : separableH2 K) :
    separableLocalInvariant L (separableRestriction K L x) =
      Module.finrank K L • separableLocalInvariant K x := by
  obtain ⟨H, hH, a, ha⟩ := exists_unramified_fixedFieldUnitInflation K x
  let S : SeparableUnramifiedStage K := ⟨H, hH⟩
  let : FiniteDimensional K S.field := S.finiteDimensional
  let : IsGalois K S.field := S.isGalois
  have hx : relativeToContinuous K S.field (SeparableClosure K) 2 a = x :=
    (S.inflation_eq_relativeToContinuous K a).symm.trans ha
  let : Algebra K (SeparableClosure L) := ((algebraMap L (SeparableClosure L)).comp
    (algebraMap K L)).toAlgebra
  let : IsScalarTower K L (SeparableClosure L) := IsScalarTower.of_algebraMap_eq' rfl
  let j : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  let : Algebra (SeparableClosure K) (SeparableClosure L) := j.toRingHom.toAlgebra
  let : IsScalarTower K (SeparableClosure K) (SeparableClosure L) := IsScalarTower.of_algHom j
  let M := unramifiedCompositum K L j S.field
  let : FiniteDimensional L M := unramifiedCompositum_finiteDimensional K L j S.field
  let : IsGalois L M := unramifiedCompositum_isGalois K L j S.field
  let := unramifiedCompositumAlgebra K L j S.field
  let := unramifiedCompositumTower K L j S.field
  have hM : ArithmeticUnramified L M := unramifiedCompositum_unramified K L j S.field hH
  have hcompat (a : S.field) :
      algebraMap M (SeparableClosure L) (algebraMap S.field M a) =
        algebraMap (SeparableClosure K) (SeparableClosure L) (algebraMap S.field (SeparableClosure K) a) := rfl
  rw [← hx]
  change separableLocalInvariant L (continuousUnitRestriction K L (SeparableClosure K)
    (SeparableClosure L) 2 (relativeToContinuous K S.field (SeparableClosure K) 2 a)) = _
  rw [relativeToContinuous_restriction K L (SeparableClosure K) (SeparableClosure L)
    S.field M hcompat, separableLocalInvariant_relative L M hM,
    separableLocalInvariant_relative K S.field S.unramified]
  exact spectralUnramifiedInvariant_baseChange K L j S.field hcont S.unramified a

end Restriction

/-- Serre's local invariant on the actual Brauer group of a nonarchimedean local field. -/
def localBrauerInvariant : BrauerGroup.{u, u} K ≃+ RationalModIntegers :=
  (brauerEquiv K).trans (separableLocalInvariant K)

/-- On an unramified splitting chart the invariant is computed from Serre's relative factor set. -/
theorem localBrauerInvariant_at_chart (A : CSA.{u, u} K)
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    (hE : ArithmeticUnramified K E)
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : E ⊗[K] A ≃ₐ[E] Matrix I I E) :
    localBrauerInvariant K (classOf A) = spectralUnramifiedInvariant K E hE (relativeClass e) := by
  change separableLocalInvariant K (brauerEquiv K (classOf A)) = _
  rw [brauerContinuousEquiv_at_chart K (SeparableClosure K) A E e]
  exact separableLocalInvariant_relative K E hE (relativeClass e)

/-- The chart value is Serre's valuation, inverse connecting map and arithmetic Frobenius. -/
theorem localBrauerInvariant_at_chart_eq_serre (A : CSA.{u, u} K)
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    (hE : ArithmeticUnramified K E)
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : E ⊗[K] A ≃ₐ[E] Matrix I I E) :
    letI := FiniteExtension.normedField K E
    letI := FiniteExtension.valuativeRel K E
    letI := FiniteExtension.isLocalField K E
    letI := spectralFiniteExtension_valuativeExtension K E
    letI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    localBrauerInvariant K (classOf A) =
      serreFiniteUnramifiedInvariant K E (spectralFiniteExtension_algebraMap_continuous K E)
        (localRamificationFactor_eq_one_of_arithmeticUnramified K E hE)
        (finiteUnramifiedCyclicCoordinate K E hE) (relativeClass e) :=
  (localBrauerInvariant_at_chart K A E hE e).trans
    (spectralUnramifiedInvariant_eq_serre K E hE (relativeClass e))

set_option maxHeartbeats 900000 in
/-- Every CSA has a positive-size chart over a finite unramified stage. -/
theorem exists_unramifiedSplittingChart (A : CSA.{u, u} K) :
    ∃ (S : SeparableUnramifiedStage K) (n : ℕ), 0 < n ∧
      Nonempty (S.field ⊗[K] A ≃ₐ[S.field] Matrix (Fin n) (Fin n) S.field) := by
  obtain ⟨H, hH, x, hx⟩ :=
    exists_unramified_fixedFieldUnitInflation K (brauerEquiv K (classOf A))
  let S : SeparableUnramifiedStage K := ⟨H, hH⟩
  let : FiniteDimensional K S.field := S.finiteDimensional
  let : IsGalois K S.field := S.isGalois
  let : DecidableEq Gal(S.field/K) := Classical.decEq _
  obtain ⟨B, e, he⟩ := exists_relativeClass_eq x
  have hB : brauerEquiv K (classOf B) = relativeToContinuous K S.field (SeparableClosure K) 2 x := by
    rw [brauerContinuousEquiv_at_chart K (SeparableClosure K) B S.field e, he]
  have hA : relativeToContinuous K S.field (SeparableClosure K) 2 x = brauerEquiv K (classOf A) :=
    (S.inflation_eq_relativeToContinuous K x).symm.trans hx
  have hab : classOf A = classOf B := (brauerEquiv K).injective (hB.trans hA).symm
  have hsplit : IsSplit (baseChange S.field A) := by
    apply (classOf_eq_zero_iff _).mp
    rw [← scalarExtension_classOf, hab, scalarExtension_classOf]
    exact (classOf_eq_zero_iff _).mpr ⟨Fintype.card Gal(S.field/K), Fintype.card_pos,
      ⟨e.trans (Matrix.reindexAlgEquiv S.field S.field (Fintype.equivFin Gal(S.field/K)))⟩⟩
  obtain ⟨n, hn, f⟩ := hsplit
  exact ⟨S, n, hn, f⟩

theorem localBrauerInvariant_eq_zero_iff (A : CSA.{u, u} K) :
    localBrauerInvariant K (classOf A) = 0 ↔ IsSplit A := by
  rw [← map_zero (localBrauerInvariant K), (localBrauerInvariant K).injective.eq_iff,
    classOf_eq_zero_iff]

section ScalarExtension

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- The actual Brauer scalar extension multiplies the invariant by the degree. -/
theorem localBrauerInvariant_scalarExtension (hcont : Continuous (algebraMap K L))
    (x : BrauerGroup.{u, u} K) :
    localBrauerInvariant L (scalarExtension L x) = Module.finrank K L • localBrauerInvariant K x := by
  change separableLocalInvariant L (brauerEquiv L (scalarExtension L x)) =
    Module.finrank K L • separableLocalInvariant K (brauerEquiv K x)
  rw [brauerEquiv_scalarExtension, separableLocalInvariant_restriction K L hcont]

end ScalarExtension

theorem localBrauerInvariant_self (x : BrauerGroup.{u, u} K) :
    localBrauerInvariant K (scalarExtension K x) = localBrauerInvariant K x := by
  rw [scalarExtension_self]
  rfl

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- Compatible field isomorphisms preserve the invariant under actual scalar extension. -/
theorem localBrauerInvariant_fieldEquiv (e : K ≃+* L) (hcont : Continuous e)
    (hval : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b) (x : BrauerGroup.{u, u} K) :
    letI := e.toRingHom.toAlgebra
    localBrauerInvariant L (scalarExtension L x) = localBrauerInvariant K x := by
  let := e.toRingHom.toAlgebra
  let : ValuativeExtension K L := ⟨hval⟩
  let e' := AlgEquiv.ofBijective (Algebra.ofId K L) e.bijective
  let : FiniteDimensional K L := Module.Finite.equiv e'.toLinearEquiv
  have hd : Module.finrank K L = 1 := e'.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self K)
  rw [localBrauerInvariant_scalarExtension K L hcont, hd, one_nsmul]

end Langlands.ClassFieldTheory.Local
