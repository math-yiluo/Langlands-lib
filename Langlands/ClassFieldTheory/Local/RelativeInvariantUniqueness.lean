import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyInflationProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof
import Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof
import Langlands.LocalField.Uniformizer
import Langlands.ClassFieldTheory.Local.RelativeInvariantEquivalences

/-! # Uniqueness of normalized finite relative local invariants -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local.InvariantFamily

universe u

open AbsoluteInvariantAssembly Langlands.LocalClassField

variable {p : ℕ} [Fact p.Prime]

/-- Arithmetic normalization determines the invariant on each actual unramified stage. -/
theorem relative_eq_localInvariantFamily_stage (J : InvariantFamily.{u,u} p)
    (hJ : J.ArithmeticNormalization) (F : PadicField.{u} p) (S : Stage F)
    (x : relativeCohomology F.Carrier S.field 2) :
    J.relative F S.field x = (localInvariantFamily unramifiedH2Exhaustion p).relative F S.field x := by
  let I := localInvariantFamily unramifiedH2Exhaustion p
  let : NeZero (Module.finrank F.Carrier S.field) := ⟨Module.finrank_pos.ne'⟩
  let π := LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData
  have hπ : F.canonicalTopologicalData.ord (π : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord _
  let c := cyclicClass F.Carrier S.field S.coordinate.toMonoidHom π
  have hc : IsFundamentalClass F.Carrier S.field (I.relative F S.field) c :=
    localInvariantFamilyArithmetic unramifiedH2Exhaustion p F S.field
      (Module.finrank F.Carrier S.field) S.coordinate S.coordinate_arithmetic π hπ
  have hgen : AddSubgroup.zmultiples c = ⊤ :=
    ((I.fundamentalClasses_of_relativeImages
      (localInvariantFamilyRelativeImages unramifiedH2Exhaustion p) F S.field).2 c hc).2
  have hx : x ∈ AddSubgroup.zmultiples c := hgen ▸ AddSubgroup.mem_top x
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [map_zsmul, map_zsmul]
  congr 1
  exact (hJ F S.field (Module.finrank F.Carrier S.field) S.coordinate
    S.coordinate_arithmetic π hπ).trans hc.symm

/-- Inflation compatibility and arithmetic normalization uniquely determine every
finite relative local invariant. No absolute invariant law is needed. -/
theorem relative_eq_localInvariantFamily (J : InvariantFamily.{u,u} p)
    (hInf : J.InflationCompatibility) (hNorm : J.ArithmeticNormalization)
    (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] (x : relativeCohomology F.Carrier L 2) :
    J.relative F L x = (localInvariantFamily unramifiedH2Exhaustion p).relative F L x := by
  let I := localInvariantFamily unramifiedH2Exhaustion p
  have hIInf : I.InflationCompatibility := localInvariantFamilyInflation unramifiedH2Exhaustion p
  let f := closureEmbedding F.Carrier L
  let S := f.fieldRange
  let xS := relativeH2Equiv f.equivFieldRange x
  obtain ⟨M, hGal, hUnr, b, hb⟩ := unramifiedH2Exhaustion p F
    (closureInflation F.Carrier S 2 xS)
  let U : Stage F := ⟨M, hGal, hUnr⟩
  let N : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) := S ⊔ U.field
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier N := { }
  let : Algebra S N := (IntermediateField.inclusion (show S ≤ N from le_sup_left)).toAlgebra
  let : Algebra U.field N :=
    (IntermediateField.inclusion (show U.field ≤ N from le_sup_right)).toAlgebra
  let : IsScalarTower F.Carrier S N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier U.field N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S N (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower U.field N (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional S N := Module.Finite.right F.Carrier S N
  let : FiniteDimensional U.field N := Module.Finite.right F.Carrier U.field N
  have heq : relativeInflation F.Carrier S N 2 xS =
      relativeInflation F.Carrier U.field N 2 b := by
    apply (AbsoluteH2Assembly.closureInflationExactness F.Carrier N).1
    rw [closureInflationTowerCompatibility, closureInflationTowerCompatibility]
    exact hb.symm
  have hS : J.relative F S xS = I.relative F S xS := by
    calc
      J.relative F S xS = J.relative F N (relativeInflation F.Carrier S N 2 xS) :=
        (hInf F S N xS).symm
      _ = J.relative F N (relativeInflation F.Carrier U.field N 2 b) := congrArg _ heq
      _ = J.relative F U.field b := hInf F U.field N b
      _ = I.relative F U.field b := relative_eq_localInvariantFamily_stage J hNorm F U b
      _ = I.relative F N (relativeInflation F.Carrier U.field N 2 b) :=
        (hIInf F U.field N b).symm
      _ = I.relative F N (relativeInflation F.Carrier S N 2 xS) := congrArg _ heq.symm
      _ = I.relative F S xS := hIInf F S N xS
  let : Algebra L S := f.equivFieldRange.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier L S :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.equivFieldRange.commutes r).symm)
  have htransport : relativeInflation F.Carrier L S 2 x = xS :=
    ArithmeticNormalizationProof.relativeInflation_eq_relativeH2Equiv
      f.equivFieldRange (fun _ => rfl) x
  calc
    J.relative F L x = J.relative F S (relativeInflation F.Carrier L S 2 x) :=
      (hInf F L S x).symm
    _ = I.relative F S (relativeInflation F.Carrier L S 2 x) := by rw [htransport]; exact hS
    _ = I.relative F L x := hIInf F L S x

/-- Any two inflation-compatible arithmetically normalized relative invariant
families agree on every finite Galois extension. Their absolute maps are unrestricted. -/
theorem relative_eq_of_normalized (I J : InvariantFamily.{u,u} p)
    (hIInf : I.InflationCompatibility) (hINorm : I.ArithmeticNormalization)
    (hJInf : J.InflationCompatibility) (hJNorm : J.ArithmeticNormalization)
    (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] : I.relative F L = J.relative F L := by
  ext x
  exact (relative_eq_localInvariantFamily I hIInf hINorm F L x).trans
    (relative_eq_localInvariantFamily J hJInf hJNorm F L x).symm

/-- Normalization alone also forces injectivity and the exact relative image. -/
theorem relativeImages_of_normalized (J : InvariantFamily.{u,u} p)
    (hInf : J.InflationCompatibility) (hNorm : J.ArithmeticNormalization) :
    J.RelativeImages := by
  intro F L _ _ _ _
  have he : J.relative F L = (localInvariantFamily unramifiedH2Exhaustion p).relative F L := by
    ext x
    exact relative_eq_localInvariantFamily J hInf hNorm F L x
  rw [he]
  exact localInvariantFamilyRelativeImages unramifiedH2Exhaustion p F L

/-- The supplied normalized invariant as an equivalence onto its exact image,
without assuming a relative-image law separately. -/
def normalizedRelativeInvariantEquiv (J : InvariantFamily.{u,u} p)
    (hInf : J.InflationCompatibility) (hNorm : J.ArithmeticNormalization)
    (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] :
    relativeCohomology F.Carrier L 2 ≃+
      denominatorSubgroup (Module.finrank F.Carrier L) :=
  J.relativeInvariantEquiv (J.relativeImages_of_normalized hInf hNorm) F L

@[simp] theorem normalizedRelativeInvariantEquiv_apply (J : InvariantFamily.{u,u} p)
    (hInf : J.InflationCompatibility) (hNorm : J.ArithmeticNormalization)
    (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] (x : relativeCohomology F.Carrier L 2) :
    (J.normalizedRelativeInvariantEquiv hInf hNorm F L x : RationalModIntegers) =
      J.relative F L x := rfl

end Langlands.ClassFieldTheory.Local.InvariantFamily
