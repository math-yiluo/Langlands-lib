import Langlands.Geometry.Building.UnitaryDoubleAffineRootJumps
import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.Geometry.Building.AffineTransitiveRootLengths
import Langlands.GroupScheme.Examples.SU3RootTowerJumps

/-! # Indivisible affine lifts from supplied multipliable unitary depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

namespace KPApartmentData

/-- An affine root whose actual relative derivative has no half root is
indivisible. -/
theorem mem_nonDivisibleRoots_of_no_half_root
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (hNoHalf : ∀ b : relativeRoots i, 2 • (b : characterLattice S) ≠ a)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots)
    (hlin : ψ.linear = rootForm i a) :
    ψ ∈ AffineRootSystem.nonDivisibleRoots D.affineRoots := by
  refine ⟨hψ, ?_⟩
  rintro ⟨b, hb, -⟩
  have hforms : (2 : ℝ) • rootForm i b = rootForm i a := by
    rw [← hb, AffineMap.smul_linear, smul_smul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul, hlin]
  apply hNoHalf b
  apply eval_injective hS
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : TranslationSpace i →ₗ[ℝ] ℝ =>
    f (Submodule.Quotient.mk v)) hforms
  simpa only [LinearMap.smul_apply, smul_eq_mul, rootForm_mk,
    eval_nsmul_char, Nat.cast_ofNat] using h

end KPApartmentData

/-- A literal central jump whose half is not a quotient jump supplies an
indivisible actual affine root in the doubled direction. -/
theorem RootUnitaryCoordinates.exists_nonDivisible_affineRoot_double
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (R : RootUnitaryCoordinates i j s a)
    (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    (hNo4 : 2 • (2 • (a : characterLattice S)) ∉ relativeRoots i)
    (w : AddValuation R.extension (WithTop ℝ)) (x : D.Apartment)
    (hdepth : ∀ p, x.val a (R.equiv p) = SU3Root.Parameters.depthA w p)
    (hjump : SU3Root.Parameters.HasIndivisibleCentralJump
      (c := SU3Root.fieldInvolution R.base R.extension) w) :
    ∃ ψ ∈ AffineRootSystem.nonDivisibleRoots D.affineRoots,
      ψ.linear = rootForm i ⟨2 • (a : characterLattice S), h2a⟩ := by
  obtain ⟨r, hr, hhalf⟩ := hjump
  let ψ := D.affineFunctional ⟨2 • (a : characterLattice S), h2a⟩ x r
  have hlin : ψ.linear = rootForm i ⟨2 • (a : characterLattice S), h2a⟩ := rfl
  have hvalue : ψ x = r := by simp [ψ]
  have hψ : ψ ∈ D.affineRoots := by
    apply (R.mem_affineRoots_double_iff_centralDepthJump D hS a h2a hNo4
      w x hdepth hlin).mpr
    simpa only [SU3Root.Parameters.centralJumpValues, Set.mem_ofPred_eq, hvalue] using hr
  refine ⟨ψ, ⟨hψ, ?_⟩, hlin⟩
  intro hh
  have hhlin : ((2 : ℝ)⁻¹ • ψ).linear = rootForm i a := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul a.property 2 h2a, smul_smul]
    norm_num
  have hmem := (R.mem_affineRoots_iff_coordinateDepthJump D hS a h2a
    w x hdepth hhlin).mp hh
  apply hhalf
  have hhvalue : ((2 : ℝ)⁻¹ • ψ) x = r / 2 := by
    change (2 : ℝ)⁻¹ * ψ x = r / 2
    rw [hvalue]
    ring
  simpa only [CoordinateDepthJump, SU3Root.Parameters.quotientJumpValues,
    Set.mem_ofPred_eq, hhvalue] using hmem

section Henselian

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  (hH : HenselianLocalRing v.valuationSubring) (hv : Function.Surjective v)

include hv in
/-- The finite-tower jump theorem discharges the arithmetic premise for
supplied unitary coordinates with the original base-normalized depth. -/
theorem RootUnitaryCoordinates.exists_nonDivisible_affineRoot_double_henselian
    (hS : IsSplitTorus S.toGrp) (a : relativeRoots i)
    (R : RootUnitaryCoordinates i j s a)
    (h2a : 2 • (a : characterLattice S) ∈ relativeRoots i)
    (hNo4 : 2 • (2 • (a : characterLattice S)) ∉ relativeRoots i)
    (x : D.Apartment)
    (hdepth : ∀ p, x.val a (R.equiv p) =
      SU3Root.towerDepth k R.base R.extension v hH p) :
    ∃ ψ ∈ AffineRootSystem.nonDivisibleRoots D.affineRoots,
      ψ.linear = rootForm i ⟨2 • (a : characterLattice S), h2a⟩ := by
  let : FiniteDimensional k R.base := Module.Finite.left k R.base R.extension
  exact R.exists_nonDivisible_affineRoot_double D hS a h2a hNo4
    (FieldTheory.henselianSeparableAddValuation v hH R.extension) x hdepth
    (SU3Root.tower_hasIndivisibleCentralJump k R.base R.extension v hH hv)

namespace KPApartmentData

/-- Only roots with a relative double require unitary coordinates. Their
origins may be chosen independently in the supplied apartment. -/
def HasMultipliableUnitaryTowerDepths : Prop :=
  ∀ (a : relativeRoots i), 2 • (a : characterLattice S) ∈ relativeRoots i →
    ∃ (R : RootUnitaryCoordinates i j s a) (x : D.Apartment),
      ∀ p, x.val a (R.equiv p) = SU3Root.towerDepth k R.base R.extension v hH p

include hv in
/-- Supplied unitary depths on the multipliable relative roots suffice for
indivisible lifts of every full ordinary affine derivative. -/
theorem hasIndivisibleDerivativeLifts_of_unitaryTowerDepths
    (hS : IsSplitTorus S.toGrp)
    (hNo4 : ∀ a ∈ relativeRoots i, (4 : ℕ) • a ∉ relativeRoots i)
    (hc : D.HasMultipliableUnitaryTowerDepths (j := j) (s := s) hH) :
    AffineRootSystem.HasIndivisibleDerivativeLifts D.affineRoots := by
  classical
  rintro ⟨f, psi0, hpsi0, hpsi0lin⟩
  obtain ⟨a, ha, hnot⟩ := hpsi0
  by_cases hhalf : ∃ b : relativeRoots i, 2 • (b : characterLattice S) = a
  · obtain ⟨b, hba⟩ := hhalf
    have h2b : 2 • (b : characterLattice S) ∈ relativeRoots i :=
      hba.symm ▸ a.property
    obtain ⟨R, x, hdepth⟩ := hc b h2b
    have h4b : 2 • (2 • (b : characterLattice S)) ∉ relativeRoots i := by
      simpa only [smul_smul, show (2 : ℕ) * 2 = 4 from rfl] using hNo4 b b.property
    obtain ⟨ψ, hψ, hψlin⟩ :=
      R.exists_nonDivisible_affineRoot_double_henselian D hH hv hS b h2b h4b x hdepth
    refine ⟨ψ, hψ, ?_⟩
    have hroot : (⟨2 • (b : characterLattice S), h2b⟩ : relativeRoots i) = a :=
      Subtype.ext hba
    exact hψlin.trans ((congrArg (rootForm i) hroot).trans (ha.symm.trans hpsi0lin))
  · exact ⟨psi0, D.mem_nonDivisibleRoots_of_no_half_root hS a
      (fun b hb => hhalf ⟨b, hb⟩) ⟨a, ha, hnot⟩ ha, hpsi0lin⟩

end KPApartmentData

end Henselian

end Langlands.Geometry.Building
