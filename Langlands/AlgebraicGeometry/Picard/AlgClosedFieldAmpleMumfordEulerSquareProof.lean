import Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof
import Langlands.AlgebraicGeometry.Picard.MumfordProductEulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Modules.SmoothProperLineBundleFiniteCohomologyProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Proof of the Euler-characteristic square formula for the ample Mumford map -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Over a field, the carrier `L ⊗ π^* B` of the normalized bundle is isomorphic to `L`, because
every line bundle `B` on `Spec K` is trivial. -/
theorem nonempty_normalize_carrier_iso
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left) (B : LineBundle (Spec (CommRingCat.of K)))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf (Spec (CommRingCat.of K))) :
    Nonempty ((LineBundle.normalize preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier ≅ L.obj) := by
  obtain ⟨t⟩ := fieldLineBundleTriviality K B
  exact ⟨(tensorFunctor A.X.left).mapIso ((Iso.refl L.obj).prod
      ((Scheme.Modules.pullback A.X.hom).mapIso t ≪≫ pullbackUnitIso A.X.hom)) ≪≫
    tensorRightUnitor L.obj⟩

/-- The dual-side Euler characteristic and the inverse symmetry `χ(M) = (-1)^g χ(N)` together
imply the Euler-characteristic square formula for the Mumford map of an ample line bundle. -/
theorem algClosedFieldAmpleMumfordEulerSquare_of_dual_of_symmetry
    (dual : AlgClosedFieldMumfordDualEulerStatement.{u})
    (symmetry : AlgClosedFieldEulerInverseSymmetryStatement.{u}) :
    AlgClosedFieldAmpleMumfordEulerSquareStatement.{u} := by
  intro preservation square K _ _ A hA L _ h B evaluationB M evaluation f hf hfin hflat y
  obtain ⟨g, hg⟩ := Tate.exists_hasRelativeDimension A
  let N : LineBundle A.X.left := (RigidifiedLineBundle.forget (unitSection A)).obj
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B
      evaluationB)
  have hN : HasFiniteCohomology A.X.hom N.obj :=
    smoothProperLineBundleFiniteCohomology K A.X.left A.X.hom inferInstance inferInstance N
  have hM : HasFiniteCohomology A.X.hom M.obj :=
    smoothProperLineBundleFiniteCohomology K A.X.left A.X.hom inferInstance inferInstance M
  have hQ := hasFiniteCohomology_mumfordAddition_tensor_snd A N M hN hM
  have e₁ := dual preservation square K A hA L B evaluationB M evaluation f hf hfin hflat g hg
    hQ y
  have e₂ := eulerCharacteristic_mumfordAddition_tensor_snd A N M hN hM hQ
  have e₃ := symmetry K A g hg N M ⟨evaluation⟩ hN hM
  obtain ⟨eNL⟩ := nonempty_normalize_carrier_iso preservation K A L B evaluationB
  have e₄ : eulerCharacteristic A.X.hom N.obj hN = eulerCharacteristic A.X.hom L.obj h :=
    eulerCharacteristic_eq_of_iso A.X.hom hN h eNL
  have hsign : ((-1 : ℤ) ^ g) * (-1) ^ g = 1 := by
    rw [← mul_pow]
    norm_num
  calc eulerCharacteristic A.X.hom L.obj h ^ 2
      = ((-1 : ℤ) ^ g * (-1) ^ g) * eulerCharacteristic A.X.hom N.obj hN ^ 2 := by
        rw [hsign, one_mul, e₄]
    _ = (-1) ^ g * (eulerCharacteristic A.X.hom N.obj hN *
          ((-1) ^ g * eulerCharacteristic A.X.hom N.obj hN)) := by ring
    _ = (-1) ^ g * (eulerCharacteristic A.X.hom N.obj hN *
          eulerCharacteristic A.X.hom M.obj hM) := by rw [e₃]
    _ = (-1) ^ g * ((-1) ^ g * (f.left.finrank y : ℤ)) := by
        rw [← e₂]
        exact congrArg ((-1 : ℤ) ^ g * ·) e₁
    _ = (f.left.finrank y : ℤ) := by rw [← mul_assoc, hsign, one_mul]

/-- The dual-side Euler characteristic implies the Euler-characteristic square formula for the
Mumford map of an ample line bundle; the inverse symmetry is the published
`algClosedFieldEulerInverseSymmetry`. -/
theorem algClosedFieldAmpleMumfordEulerSquare_of_dual
    (dual : AlgClosedFieldMumfordDualEulerStatement.{u}) :
    AlgClosedFieldAmpleMumfordEulerSquareStatement.{u} :=
  algClosedFieldAmpleMumfordEulerSquare_of_dual_of_symmetry dual
    algClosedFieldEulerInverseSymmetry

/-- The Euler-characteristic square formula for the Mumford map of an ample line bundle over an
algebraically closed field: `χ(L)^2 = f.left.finrank y` at every point `y` of the dual. -/
theorem algClosedFieldAmpleMumfordEulerSquare :
    AlgClosedFieldAmpleMumfordEulerSquareStatement.{u} :=
  algClosedFieldAmpleMumfordEulerSquare_of_dual algClosedFieldMumfordDualEuler

end Langlands.AbelianScheme
