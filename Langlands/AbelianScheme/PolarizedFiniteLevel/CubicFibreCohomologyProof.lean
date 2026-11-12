import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreEulerReductionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.SixfoldPolarizationDegreeReductionProof
import Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingAssembly
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.MultiplicationDegree
import Langlands.AbelianScheme.FieldAmpleMultiplicationKernelProof
import Langlands.AbelianScheme.FieldFiniteKernelIsogenyProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof
import Langlands.AlgebraicGeometry.Picard.PolarizedFiniteFlatRankProof

/-! # Proof of the cubic-fibre cohomology theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.GroupScheme

/-- On an abelian scheme over an algebraically closed field with an ample line
bundle, the symmetric multiplication formula makes multiplication by every
positive `k` an isogeny of native rank `k ^ (2 * g)` at every point. -/
theorem multiplication_isIsogeny_finrank_of_symmetricMultiplication
    (symm : FieldSymmetricMultiplicationPullbackStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ) (hg : A.HasRelativeDimension g)
    (H : LineBundle A.X.left) (hH : H.IsAmple) (k : ℕ) (hk : 0 < k) :
    GroupScheme.IsIsogeny (GroupScheme.multiplication A.toGrp (k : ℤ)) ∧
      ∀ x : A.X.left,
        (GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom.left.finrank x = k ^ (2 * g) := by
  have hpow := symm K A.toGrp A.smooth A.proper A.geometricallyConnected
    (symmetrization A H) (symmetrization_symmetric A H) k hk
  have hker := fieldAmpleMultiplicationKernel K A.toGrp A.smooth A.proper
    A.geometricallyConnected (symmetrization A H) (isAmple_symmetrization A H hH) k hk hpow
  have hiso := fieldFiniteKernelIsogeny K A.toGrp (GroupScheme.multiplication A.toGrp (k : ℤ))
    A.smooth A.proper A.geometricallyConnected hker
  refine ⟨hiso, fun x => ?_⟩
  have h := polarizedFiniteFlatRank K A.X g hg inferInstance inferInstance
    (GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom hiso.1 hiso.2.1 (symmetrization A H)
    (isAmple_symmetrization A H hH) (k * k) (Nat.mul_pos hk hk) hpow x
  simpa only [← pow_two, ← pow_mul] using h

/-- Natural multiples of the identity are the published multiplication maps. -/
lemma groupHom_nsmul_id_eq_multiplication {S : Scheme.{u}} (A : AbelianScheme S) (k : ℕ) :
    groupHom (k • 𝟙 A) = GroupScheme.multiplication A.toGrp (k : ℤ) := by
  change (𝟙 A.toGrp) ^ k = (𝟙 A.toGrp) ^ (k : ℤ)
  rw [zpow_natCast]

/-- Over an algebraically closed field, given the symmetric multiplication
formula, `6 • polarization` is finite and flat of constant native rank
`6 ^ (2 * g) * d ^ 2`. -/
theorem Datum.sixfoldPolarization_degree_of_symmetricMultiplication
    (symm : FieldSymmetricMultiplicationPullbackStatement.{u})
    {P : Prerequisites.{u}} {K : Type u} [Field K] [IsAlgClosed K] {g d n : ℕ}
    (a : Datum P (Spec (CommRingCat.of K)) g d n) :
    IsFinite (hom (6 • a.polarization)) ∧ Flat (hom (6 • a.polarization)) ∧
      HasConstantDegree (hom (6 • a.polarization)) (6 ^ (2 * g) * d ^ 2) := by
  obtain ⟨hiso, hrank⟩ := multiplication_isIsogeny_finrank_of_symmetricMultiplication symm
    a.abelian g a.dimension a.cubicBundle a.cubicBundle_isAmple 6 (by norm_num)
  have h6 : hom ((6 : ℕ) • 𝟙 a.abelian) =
      (GroupScheme.multiplication a.abelian.toGrp ((6 : ℕ) : ℤ)).hom.hom.left := by
    change (groupHom ((6 : ℕ) • 𝟙 a.abelian)).hom.hom.left = _
    rw [groupHom_nsmul_id_eq_multiplication]
  have hfin : IsFinite (hom ((6 : ℕ) • 𝟙 a.abelian)) := by
    rw [h6]
    exact hiso.1
  have hflat : Flat (hom ((6 : ℕ) • 𝟙 a.abelian)) := by
    rw [h6]
    exact hiso.2.1
  have hdeg : HasConstantDegree (hom ((6 : ℕ) • 𝟙 a.abelian)) (6 ^ (2 * g)) := by
    intro y
    rw [h6]
    exact hrank y
  exact sixfoldPolarizationDegreeReduction P K g d n a hfin hflat hdeg

/-- The cubic-fibre cohomology theorem follows from higher-cohomology vanishing
for ample line bundles, the symmetric multiplication formula and the
Euler-characteristic square formula for Mumford maps. -/
theorem cubicFibreCohomology_of_inputs
    (vanishing : AmpleLineBundleHigherCohomologyVanishingStatement.{u})
    (symm : FieldSymmetricMultiplicationPullbackStatement.{u})
    (eulerSquare : AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}) :
    CubicFibreCohomologyStatement.{u} := by
  intro P K _ _ g d n _ a
  have hv : ∀ i : ℕ, 0 < i →
      IsZero ((relativeCohomology a.abelian.X.hom i).obj a.cubicBundle.obj) :=
    vanishing K a.abelian a.cubicBundle a.cubicBundle_isAmple
  refine ⟨hv, ?_⟩
  have hfc := a.cubicBundle_hasFiniteCohomology
  refine a.cubicBundle_finrank_of_vanishing_of_eulerSquare hfc hv ?_
  obtain ⟨B, evaluationB, M, evaluation, hmap⟩ := cubicBundleMumford P K g d n a
  obtain ⟨hfin, hflat, hdeg⟩ := a.sixfoldPolarization_degree_of_symmetricMultiplication symm
  let y := hom (6 • a.polarization) (unitSection a.abelian (IsLocalRing.closedPoint K))
  have h := eulerSquare P.preservation P.square K a.abelian a.dualWitness.hasDual
    a.cubicBundle a.cubicBundle_isAmple hfc B evaluationB M evaluation
    (groupHom (6 • a.polarization)).hom.hom hmap.symm hfin hflat y
  have h2 := congrArg (fun r : ℕ => (r : ℤ)) (hdeg y)
  calc eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj hfc ^ 2
      = ((hom (6 • a.polarization)).finrank y : ℤ) := h
    _ = ((6 ^ (2 * g) * d ^ 2 : ℕ) : ℤ) := h2
    _ = (6 : ℤ) ^ (2 * g) * (d : ℤ) ^ 2 := by push_cast; ring

/-- The cubic-fibre cohomology theorem follows from the balanced cube identity
and the Euler-characteristic square formula for Mumford maps. -/
theorem cubicFibreCohomology_of_cube
    (cube : FieldCubePullbackStatement.{u})
    (eulerSquare : AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}) :
    CubicFibreCohomologyStatement.{u} :=
  cubicFibreCohomology_of_inputs (ampleLineBundleHigherCohomologyVanishing_of_cube cube)
    (fieldSymmetricMultiplicationPullbackOfCube cube) eulerSquare

/-- With the published balanced cube identity, the cubic-fibre cohomology
theorem follows from the Euler-characteristic square formula alone. -/
theorem cubicFibreCohomology_of_eulerSquare
    (eulerSquare : AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}) :
    CubicFibreCohomologyStatement.{u} :=
  cubicFibreCohomology_of_cube fieldCubePullback eulerSquare

/-- Over an algebraically closed field, the cubic diagonal bundle of a polarized
datum has no higher cohomology, and its global sections have dimension `6^g*d`. -/
theorem cubicFibreCohomology : CubicFibreCohomologyStatement.{u} :=
  cubicFibreCohomology_of_eulerSquare algClosedFieldAmpleMumfordEulerSquare

end Langlands.AbelianScheme.PolarizedFiniteLevel
