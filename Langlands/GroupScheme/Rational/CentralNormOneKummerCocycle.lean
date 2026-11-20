import Langlands.ClassField.Global.FundamentalClassReduction
import Langlands.GroupScheme.Rational.CentralNormOneCocycleLift

/-! # Kummer cocycles of tensor radicals with prescribed norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra Langlands.LocalClassField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [Field B] [Algebra F B]

/-- A radical of a base extension unit, with a specified scalar norm. -/
structure NormPowerTensorRadical (E : Type u) [Field E] [Algebra F E]
    (n : ℕ) (b : Bˣ) (s : Fˣ) where
  /-- The actual tensor unit. -/
  tensorUnit : (B ⊗[F] E)ˣ
  pow_eq : tensorUnit ^ n = leftTensorUnit b
  norm_eq : tensorNormUnits F B E tensorUnit = Units.map (algebraMap F E).toMonoidHom s

/-- A global pair satisfying the norm-power equation has a tensor radical with that
norm on a finite Galois refinement of any given coefficient cover. -/
theorem exists_normPowerTensorRadical [NumberField F] [NumberField B]
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (n : ℕ) (hn : 0 < n) (b : Bˣ) (s : Fˣ) (hs : normUnits F B b = s ^ n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E), Nonempty (NormPowerTensorRadical E n b s) := by
  let : NumberField L := NumberField.of_module_finite F L
  obtain ⟨D, _, _, ⟨j⟩⟩ := GroupScheme.exists_finite_galois_algHom F B
  let : NumberField D := NumberField.of_module_finite F D
  obtain ⟨K, _, _, _, _, _, _, _, _⟩ := FundamentalClass.exists_galois_tower F L D
  let jB := (IsScalarTower.toAlgHom F D K).comp j
  let : Algebra B K := jB.toRingHom.toAlgebra
  let : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq fun x => (jB.commutes x).symm
  obtain ⟨E, _, _, _, _, _, _, z, hz⟩ :=
    exists_tensorUnit_root n hn.ne' (leftTensorUnit (F := F) (L := K) b)
  let : Algebra B E := Algebra.compHom E (algebraMap B K)
  let : Algebra L E := Algebra.compHom E (algebraMap L K)
  let : IsScalarTower B K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower L K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F B E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K E, IsScalarTower.algebraMap_apply B K E,
      ← IsScalarTower.algebraMap_apply F B K]
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K E, IsScalarTower.algebraMap_apply L K E,
      ← IsScalarTower.algebraMap_apply F L K]
  have hz' : z ^ n = leftTensorUnit b := hz.trans (extendTensorUnit_leftTensorUnit E b)
  let N := tensorNormUnits F B E
  let i := Units.map (algebraMap F E).toMonoidHom
  have hnormpow : (N z) ^ n = (i s) ^ n := calc
    _ = N (z ^ n) := (map_pow N z n).symm
    _ = N (leftTensorUnit b) := congrArg N hz'
    _ = i (normUnits F B b) := tensorNormUnits_left b
    _ = (i s) ^ n := by rw [hs, map_pow]
  let a := i s / N z
  have ha : a ^ n = 1 := by
    change (i s / N z) ^ n = 1
    rw [div_pow, hnormpow, div_self']
  obtain ⟨q, hq, hqN⟩ := exists_tensorNorm_torsion_lift (F := F) (B := B) n a ha
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨⟨z * q, ?_, ?_⟩⟩⟩
  · rw [mul_pow, hz', hq, mul_one]
  · change N (z * q) = i s
    rw [map_mul, show N q = a from hqN]
    exact mul_div_cancel _ _

variable {E : Type u} [Field E] [Algebra F E] {n : ℕ} {b : Bˣ} {s : Fˣ}

/-- The values of a tensor radical coboundary have exponent dividing `n`. -/
theorem NormPowerTensorRadical.coboundary_pow_eq_one
    (r : NormPowerTensorRadical E n b s) (σ : Gal(E/F)) :
    tensorCoboundary r.tensorUnit σ ^ n = 1 := by
  rw [tensorCoboundary, div_pow, ← map_pow, r.pow_eq, tensorAction_leftTensorUnit, div_self']

/-- The values of the tensor radical coboundary have norm one. -/
theorem NormPowerTensorRadical.coboundary_norm_eq_one [FiniteDimensional F B]
    (r : NormPowerTensorRadical E n b s) (σ : Gal(E/F)) :
    tensorNormUnits F B E (tensorCoboundary r.tensorUnit σ) = 1 := by
  have hfix : σ • Units.map (algebraMap F E).toMonoidHom s =
      Units.map (algebraMap F E).toMonoidHom s := Units.ext (σ.commutes (s : F))
  rw [tensorCoboundary, map_div, tensorNormUnits_action, r.norm_eq, hfix, div_self']

/-- A tensor radical defines a crossed cocycle of tensor units. -/
theorem tensorCoboundary_mul (z : (B ⊗[F] E)ˣ) (σ τ : Gal(E/F)) :
    tensorCoboundary z (σ * τ) = tensorAction F B E σ (tensorCoboundary z τ) * tensorCoboundary z σ := by
  simp only [tensorCoboundary, tensorAction_mul, map_div]
  rw [div_mul_div_cancel]

end Langlands.ClassField.Global.TensorUnitShapiro

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.ClassField.Global.TensorUnitShapiro

set_option backward.isDefEq.respectTransparency false

variable {F B E : Type u} [Field F] [Field B] [Field E] [Algebra F B] [Algebra F E]
  [FiniteDimensional F B] {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (n : ℕ) (e : kernel f ≅ WeilGm.normOneTorsion F B n)

/-- The norm-one torsion point coordinates detect every point of the actual kernel. -/
theorem kernelTensorUnitMap_normOne_injective :
    Function.Injective (kernelTensorUnitMap (kernelNormOneToWeil n e) E) := by
  intro x y h
  apply (kernelNormOneEquiv n e E).injective
  apply Subtype.ext
  simpa only [kernelNormOneEquiv_val n e] using h

/-- The inverse kernel equivalence recovers the given norm-one torsion unit. -/
theorem kernelTensorUnitMap_kernelNormOneEquiv_symm
    (t : WeilGm.normOneTorsionUnits (B := B) n (CommAlgCat.of F E)) :
    kernelTensorUnitMap (kernelNormOneToWeil n e) E ((kernelNormOneEquiv n e E).symm t) = t.val := by
  rw [← kernelNormOneEquiv_val n e, MulEquiv.apply_symm_apply]

variable [FiniteDimensional F E] [IsGalois F E] {b : Bˣ} {s : Fˣ}

/-- A tensor Kummer radical with scalar norm gives a natural cocycle of the
norm-one torsion kernel over the same Galois cover. -/
def normOneKummerKernelCocycle (r : NormPowerTensorRadical E n b s) :
    Cocycle (kernel f) (GaloisCocycle.cover F E) := by
  let d (σ : Gal(E/F)) : GaloisCocycle.cover F E ⟶ (kernel f).X :=
    (kernelNormOneEquiv n e E).symm ⟨tensorCoboundary r.tensorUnit σ,
      (mem_rootsOfUnity n _).mpr (r.coboundary_pow_eq_one σ), r.coboundary_norm_eq_one σ⟩
  let j := kernelTensorUnitMap (kernelNormOneToWeil n e) E
  have hd (σ : Gal(E/F)) : j (d σ) = tensorCoboundary r.tensorUnit σ :=
    kernelTensorUnitMap_kernelNormOneEquiv_symm n e _
  refine GaloisCocycle.ofValues d (fun σ τ => ?_)
  apply kernelTensorUnitMap_normOne_injective n e
  change j (d (σ * τ)) = j (d σ * GaloisPoint.conjugate F E (kernel f) σ (d τ))
  have hσ : j (GaloisPoint.conjugate F E (kernel f) σ (d τ)) =
      tensorAction F B E σ (j (d τ)) :=
    kernelTensorUnitMap_naturality (kernelNormOneToWeil n e) σ.toAlgHom (d τ)
  rw [map_mul, hσ, hd, hd, hd, mul_comm]
  exact tensorCoboundary_mul r.tensorUnit σ τ

/-- The natural kernel cocycle has the prescribed tensor coboundary coordinates. -/
theorem kernelTensorUnitMap_value_normOneKummerKernelCocycle
    (r : NormPowerTensorRadical E n b s) (σ : Gal(E/F)) :
    kernelTensorUnitMap (kernelNormOneToWeil n e) E
      (GaloisCocycle.value (normOneKummerKernelCocycle n e r) σ) =
        tensorCoboundary r.tensorUnit σ := by
  unfold normOneKummerKernelCocycle
  rw [GaloisCocycle.value_ofValues]
  exact kernelTensorUnitMap_kernelNormOneEquiv_symm n e _

end Langlands.GroupScheme.IsCentralIsogeny
