import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof

/-! # Cohomology of the powers of the cubic bundle over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.GroupScheme

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The `k`-th power of the cubic bundle, realized as the `3k`-th tensor power of the
canonical bundle. -/
def Datum.cubicPowerBundle (a : Datum P S g d n) (k : ℕ) : LineBundle a.abelian.X.left :=
  ⟨tensorPow a.canonicalBundle.obj (3 * k),
    tensorPow_isLocallyFreeRankOne _ a.canonicalBundle (3 * k)⟩

/-- The `3k`-th power of the canonical bundle is the `k`-th power of the cubic bundle. -/
def Datum.cubicPowerBundleIso (a : Datum P S g d n) (k : ℕ) :
    (a.cubicPowerBundle k).obj ≅ tensorPow a.cubicBundle.obj k :=
  (tensorPowMulIso a.canonicalBundle.obj 3 k).symm

/-- Positive powers of the cubic bundle are ample over every field. -/
lemma Datum.cubicPowerBundle_isAmple {K : Type u} [Field K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) (hk : 0 < k) :
    (a.cubicPowerBundle k).IsAmple :=
  positiveTensorPowerAmple _ a.canonicalBundle (a.cubicPowerBundle k) (3 * k) (by omega)
    a.canonicalBundle_isAmple ⟨Iso.refl _⟩

/-- The powers of the cubic bundle have finite cohomology over every field. -/
theorem Datum.cubicPowerBundle_hasFiniteCohomology {K : Type u} [Field K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) :
    HasFiniteCohomology a.abelian.X.hom (a.cubicPowerBundle k).obj := by
  obtain ⟨h, _⟩ := smoothProperLineBundleEulerPolynomial K a.abelian.X g
    a.dimension inferInstance inferInstance a.canonicalBundle
  exact h (3 * k)

/-- The Mumford map of the `k`-th power of the cubic bundle is `(6k) • polarization`. -/
theorem Datum.cubicPowerBundleMumford {K : Type u} [Field K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) :
    ∃ (B : LineBundle (Spec (CommRingCat.of K)))
      (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection a.abelian)).obj
        (a.cubicPowerBundle k).obj) B.obj ≅ structureSheaf (Spec (CommRingCat.of K)))
      (M : LineBundle a.abelian.X.left)
      (evaluation : tensorObj (LineBundle.normalize P.preservation a.abelian.X.hom
        (unitSection a.abelian) (unitSection_comp a.abelian) (a.cubicPowerBundle k) B
        evaluationB).obj.carrier M.obj ≅ structureSheaf a.abelian.X.left),
      mumfordSchemeMapOfLineBundle P.preservation a.abelian (a.cubicPowerBundle k) B evaluationB
        M evaluation P.square a.dualWitness.hasDual =
          (groupHom ((6 * k) • a.polarization)).hom.hom := by
  obtain ⟨B, evaluationB, M, evaluation, hmap⟩ :=
    polarizationDiagonalMumford P.preservation P.square P.universality P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      (Spec (CommRingCat.of K)) a.abelian a.dualWitness.hasDual a.dualWitness.geometry
      a.dualWitness.inverseBundle a.dualWitness.evaluation a.polarization a.polarized
  change mumfordSchemeMapOfLineBundle P.preservation a.abelian a.canonicalBundle B
    evaluationB M evaluation P.square a.dualWitness.hasDual =
      (groupHom (2 • a.polarization)).hom.hom at hmap
  obtain ⟨Bk, ⟨evaluationBk⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection a.abelian)).obj (a.cubicPowerBundle k))
  obtain ⟨Mk, ⟨evaluationk⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((RigidifiedLineBundle.forget _).obj (LineBundle.normalize P.preservation
      a.abelian.X.hom (unitSection a.abelian) (unitSection_comp a.abelian)
      (a.cubicPowerBundle k) Bk evaluationBk))
  refine ⟨Bk, evaluationBk, Mk, evaluationk, ?_⟩
  have h := mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass P a.abelian a.dualWitness
    a.canonicalBundle B evaluationB M evaluation (a.cubicPowerBundle k) Bk evaluationBk
    Mk evaluationk (3 * k) (isoClass_tensorPow P.preservation a.canonicalBundle (3 * k))
  dsimp only at h
  rw [hmap] at h
  have hn : (groupHom ((6 * k) • a.polarization)).hom.hom =
      ((groupHom (2 • a.polarization)).hom.hom) ^ (3 * k) := by
    rw [← groupHom_nsmul_hom]
    congr 3
    rw [smul_smul]
    congr 1
    ring
  exact h.trans hn.symm

/-- Over an algebraically closed field, `(6k) • polarization` is finite and flat of
constant native rank `(6k) ^ (2g) * d ^ 2`, for every positive `k`. -/
theorem Datum.multiplePolarization_degree {K : Type u} [Field K] [IsAlgClosed K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) (hk : 0 < k) :
    IsFinite (hom ((6 * k) • a.polarization)) ∧ Flat (hom ((6 * k) • a.polarization)) ∧
      HasConstantDegree (hom ((6 * k) • a.polarization)) ((6 * k) ^ (2 * g) * d ^ 2) := by
  obtain ⟨hiso, hrank⟩ := multiplication_isIsogeny_finrank_of_symmetricMultiplication
    (fieldSymmetricMultiplicationPullbackOfCube fieldCubePullback)
    a.abelian g a.dimension a.cubicBundle a.cubicBundle_isAmple (6 * k) (by omega)
  have h6 : hom ((6 * k) • 𝟙 a.abelian) =
      (GroupScheme.multiplication a.abelian.toGrp ((6 * k : ℕ) : ℤ)).hom.hom.left := by
    change (groupHom ((6 * k) • 𝟙 a.abelian)).hom.hom.left = _
    rw [groupHom_nsmul_id_eq_multiplication]
  have hfin : IsFinite (hom ((6 * k) • 𝟙 a.abelian)) := by
    rw [h6]
    exact hiso.1
  have hflat : Flat (hom ((6 * k) • 𝟙 a.abelian)) := by
    rw [h6]
    exact hiso.2.1
  have hdeg : HasConstantDegree (hom ((6 * k) • 𝟙 a.abelian)) ((6 * k) ^ (2 * g)) := by
    intro y
    rw [h6]
    exact hrank y
  let : IsFinite (hom a.polarization) := a.polarized.1.1
  let : Flat (hom a.polarization) := a.polarized.1.2.1
  let : IsLocallyNoetherian (a.dualWitness.dual P).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (a.dualWitness.dual P).X.hom
  have hcomp : hom ((6 * k) • 𝟙 a.abelian) ≫ hom a.polarization =
      hom ((6 * k) • a.polarization) := by
    rw [← hom_comp, Preadditive.nsmul_comp, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcomp]
    infer_instance
  · rw [← hcomp]
    infer_instance
  · have h := Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition
      a.abelian.X.left a.abelian.X.left (a.dualWitness.dual P).X.left
      (hom ((6 * k) • 𝟙 a.abelian)) (hom a.polarization)
      ((6 * k) ^ (2 * g)) (d ^ 2) hdeg a.degree
    simpa only [HasConstantDegree, hcomp] using h

/-- Over an algebraically closed field, the `k`-th power of the cubic bundle (`k > 0`)
has no higher cohomology and `(6k)^g * d` independent global sections. -/
theorem Datum.cubicPowerFibreCohomology {K : Type u} [Field K] [IsAlgClosed K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) (hk : 0 < k) :
    (∀ i : ℕ, 0 < i →
        IsZero ((relativeCohomology a.abelian.X.hom i).obj (a.cubicPowerBundle k).obj)) ∧
      Module.finrank K ((relativeCohomology a.abelian.X.hom 0).obj
        (a.cubicPowerBundle k).obj) = (6 * k) ^ g * d := by
  have hv : ∀ i : ℕ, 0 < i →
      IsZero ((relativeCohomology a.abelian.X.hom i).obj (a.cubicPowerBundle k).obj) :=
    ampleLineBundleHigherCohomologyVanishing_of_cube fieldCubePullback K a.abelian
      (a.cubicPowerBundle k) (a.cubicPowerBundle_isAmple k hk)
  refine ⟨hv, ?_⟩
  have hfc := a.cubicPowerBundle_hasFiniteCohomology k
  apply finrank_eq_of_higherCohomology_isZero_of_eulerSquare K _
    a.abelian.X.hom (a.cubicPowerBundle k).obj hfc ((6 * k) ^ g * d) hv
  obtain ⟨B, evaluationB, M, evaluation, hmap⟩ := a.cubicPowerBundleMumford k
  obtain ⟨hfin, hflat, hdeg⟩ := a.multiplePolarization_degree k hk
  let y := hom ((6 * k) • a.polarization) (unitSection a.abelian (IsLocalRing.closedPoint K))
  have h := algClosedFieldAmpleMumfordEulerSquare P.preservation P.square K a.abelian
    a.dualWitness.hasDual (a.cubicPowerBundle k) (a.cubicPowerBundle_isAmple k hk) hfc B
    evaluationB M evaluation (groupHom ((6 * k) • a.polarization)).hom.hom hmap.symm hfin
    hflat y
  have h2 := congrArg (fun r : ℕ => (r : ℤ)) (hdeg y)
  calc eulerCharacteristic a.abelian.X.hom (a.cubicPowerBundle k).obj hfc ^ 2
      = ((hom ((6 * k) • a.polarization)).finrank y : ℤ) := h
    _ = (((6 * k) ^ (2 * g) * d ^ 2 : ℕ) : ℤ) := h2
    _ = (((6 * k) ^ g * d : ℕ) : ℤ) ^ 2 := by push_cast; ring

end Langlands.AbelianScheme.PolarizedFiniteLevel
