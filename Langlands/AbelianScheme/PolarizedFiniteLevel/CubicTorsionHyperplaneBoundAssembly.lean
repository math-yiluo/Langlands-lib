import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionHyperplaneBezoutReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof

/-! # The torsion-hyperplane count from four published geometric statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {P : Prerequisites.{u}} {K : Type u} [Field K] {g d n : ℕ}

/-- Every actual line bundle on the abelian scheme of a datum over a field has finite
cohomology. -/
lemma Datum.lineBundle_hasFiniteCohomology (a : Datum P (Spec (CommRingCat.of K)) g d n)
    (L : LineBundle a.abelian.X.left) : HasFiniteCohomology a.abelian.X.hom L.obj :=
  Langlands.AlgebraicGeometry.Modules.smoothProperLineBundleFiniteCohomology K
    a.abelian.X.left a.abelian.X.hom inferInstance inferInstance L

/-- **Squared Euler characteristics of cubic powers.** Over an algebraically closed field,
the scaling statement and the inverse-symmetry statement give
`χ(M^k)^2 = k^(2g) χ(M)^2` for the cubic bundle `M` and every positive `k`. -/
theorem Datum.cubicBundle_eulerCharacteristic_tensorPow_sq
    (hS : AlgClosedFieldAmpleEulerInverseScalingStatement.{u})
    (hI : AlgClosedFieldEulerInverseSymmetryStatement.{u}) [IsAlgClosed K]
    (a : Datum P (Spec (CommRingCat.of K)) g d n) (k : ℕ) (hk : 0 < k)
    (hM : HasFiniteCohomology a.abelian.X.hom a.cubicBundle.obj)
    (hMk : HasFiniteCohomology a.abelian.X.hom (tensorPow a.cubicBundle.obj k)) :
    eulerCharacteristic a.abelian.X.hom (tensorPow a.cubicBundle.obj k) hMk ^ 2 =
      (k : ℤ) ^ (2 * g) * eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj hM ^ 2 := by
  obtain ⟨N, ⟨eN⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf a.cubicBundle
  obtain ⟨Nk, ⟨eNk⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    (⟨tensorPow a.cubicBundle.obj k, tensorPow_isLocallyFreeRankOne _ a.cubicBundle k⟩ :
      LineBundle a.abelian.X.left)
  have hN := a.lineBundle_hasFiniteCohomology N
  have hNk := a.lineBundle_hasFiniteCohomology Nk
  set x := eulerCharacteristic a.abelian.X.hom (tensorPow a.cubicBundle.obj k) hMk
  set y := eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj hM
  have hscale : x * eulerCharacteristic a.abelian.X.hom Nk.obj hNk =
      (k : ℤ) ^ (2 * g) * (y * eulerCharacteristic a.abelian.X.hom N.obj hN) :=
    hS K a.abelian g a.dimension a.cubicBundle N a.cubicBundle_isAmple ⟨eN⟩ k hk Nk ⟨eNk⟩
      hM hN hMk hNk
  have hsymN : eulerCharacteristic a.abelian.X.hom N.obj hN = (-1) ^ g * y :=
    hI K a.abelian g a.dimension a.cubicBundle N ⟨eN⟩ hM hN
  have hsymNk : eulerCharacteristic a.abelian.X.hom Nk.obj hNk = (-1) ^ g * x :=
    hI K a.abelian g a.dimension
      ⟨tensorPow a.cubicBundle.obj k, tensorPow_isLocallyFreeRankOne _ a.cubicBundle k⟩
      Nk ⟨eNk⟩ hMk hNk
  have hu : ((-1 : ℤ) ^ g) * (-1) ^ g = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (-1 : ℤ) ^ g * hscale - (-1 : ℤ) ^ g * x * hsymNk +
    (-1 : ℤ) ^ g * (k : ℤ) ^ (2 * g) * y * hsymN - (x ^ 2 - (k : ℤ) ^ (2 * g) * y ^ 2) * hu

/-- **The Euler coefficient of the cubic bundle.** Over an algebraically closed field, the
scaling, inverse-symmetry and cubic-fibre cohomology statements give `6^g * d` as the
degree-`g` coefficient of the actual Euler polynomial of the cubic bundle of a datum
with `0 < d`. -/
theorem Datum.cubicBundle_eulerPolynomial_coeff_of_fibreInputs
    (hS : AlgClosedFieldAmpleEulerInverseScalingStatement.{u})
    (hI : AlgClosedFieldEulerInverseSymmetryStatement.{u})
    (hC : CubicFibreCohomologyStatement.{u}) [IsAlgClosed K] (hd : 0 < d)
    (a : Datum P (Spec (CommRingCat.of K)) g d n) :
    (lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g = 6 ^ g * d := by
  have : IsNoetherian a.abelian.X.left := field_isNoetherian a.abelian
  have : a.abelian.X.left.IsSeparated := field_isSeparated a.abelian
  obtain ⟨hv, hdim⟩ := hC P K g d n hd a
  have hM := a.lineBundle_hasFiniteCohomology a.cubicBundle
  have hχ : eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj hM =
      ((6 ^ g * d : ℕ) : ℤ) := by
    rw [(eulerCharacteristicBasic K _ a.abelian.X.hom).2.2.2.2 _ hM hv, hdim]
  have h := lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq a.abelian.X.hom
    a.cubicBundle g (field_topologicalKrullDim a.dimension).le (6 ^ g * d)
    (fun k hk hk' => by
      rw [a.cubicBundle_eulerCharacteristic_tensorPow_sq hS hI k hk hM hk', hχ]
      ring)
    (fun h1 => by
      rw [eulerCharacteristic_eq_of_iso a.abelian.X.hom h1 hM (tensorPowOneIso _), hχ]
      positivity)
  rw [h]
  push_cast
  rfl

/-- **Conditional form of the target.** The torsion-hyperplane bound follows from the
symmetric multiplication-pullback statement, the Euler scaling statement, the Euler
inverse-symmetry statement and the cubic-fibre cohomology statement. -/
theorem cubicTorsionHyperplaneBound_of_fibreInputs
    (hB : GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u})
    (hS : AlgClosedFieldAmpleEulerInverseScalingStatement.{u})
    (hI : AlgClosedFieldEulerInverseSymmetryStatement.{u})
    (hC : CubicFibreCohomologyStatement.{u}) :
    CubicTorsionHyperplaneBoundStatement.{u} :=
  cubicTorsionHyperplaneBound_of_symmetricPullback hB
    (fun _ _ _ _ _ _ _ _ hd a => a.cubicBundle_eulerPolynomial_coeff_of_fibreInputs hS hI hC hd)

/-- The reduction proved in this module (internal): the symmetric multiplication-pullback,
Euler scaling, Euler inverse-symmetry and cubic-fibre cohomology statements together imply
the torsion-hyperplane bound. It does not assert any of the four premises. -/
def CubicTorsionHyperplaneBoundReductionStatement : Prop :=
  GroupScheme.FieldSymmetricMultiplicationPullbackStatement.{u} →
    AlgClosedFieldAmpleEulerInverseScalingStatement.{u} →
      AlgClosedFieldEulerInverseSymmetryStatement.{u} →
        CubicFibreCohomologyStatement.{u} →
          CubicTorsionHyperplaneBoundStatement.{u}

theorem cubicTorsionHyperplaneBoundReduction :
    CubicTorsionHyperplaneBoundReductionStatement.{u} :=
  cubicTorsionHyperplaneBound_of_fibreInputs

end Langlands.AbelianScheme.PolarizedFiniteLevel
