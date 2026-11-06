import Langlands.Representation.Jacquet.CompatibleCoefficientActions
import Langlands.Representation.Jacquet.StableCompressionPropagation
import Langlands.Representation.Plancherel.RationalNormalizedInducedSpecializationStatement
import Langlands.LinearAlgebra.StableEndomorphismBaseChange

/-! Compact fixed vectors and fixed compression powers under scalar specialization. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Compact.CoefficientSpecialization

universe uR uG uV uW

variable (R : Type uR) [CommRing R] [Algebra R ℂ]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
variable [SMulCommClass ℂ R V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
variable [HasCompatibleCoefficients R ρ]
variable (f : ρ.IntertwiningMap τ)
variable (hf : ∀ (r : R) (v : V), f (r • v) = algebraMap R ℂ r • f v)

/-- A complex intertwiner with the evaluation scalar law, bundled semilinearly. -/
def evaluation : V →ₛₗ[algebraMap R ℂ] W where
  toFun := f
  map_add' := map_add f
  map_smul' := hf

/-- Scalar extension of the full evaluation map. -/
def scalarExtension : ℂ ⊗[R] V →ₗ[ℂ] W :=
  Plancherel.scalarExtensionOfSemilinear (evaluation R ρ τ f hf)

/-- Semilinear evaluation restricted to the actual fixed-vector carriers. -/
def fixedEvaluation (H : Subgroup G) :
    fixedVectors ρ H →ₛₗ[algebraMap R ℂ] fixedVectors τ H where
  toFun := fixedVectorsMap f H
  map_add' := map_add (fixedVectorsMap f H)
  map_smul' r v := Subtype.ext (hf r v.val)

/-- The canonical scalar-extension map between the actual fixed modules. -/
def fixedScalarExtension (H : Subgroup G) :
    ℂ ⊗[R] fixedVectors ρ H →ₗ[ℂ] fixedVectors τ H :=
  Plancherel.scalarExtensionOfSemilinear (fixedEvaluation R ρ τ f hf H)

omit [TopologicalSpace G] [IsTopologicalGroup G] [SMulCommClass ℂ R V] in
@[simp] theorem fixedScalarExtension_tmul (H : Subgroup G)
    (z : ℂ) (v : fixedVectors ρ H) :
    fixedScalarExtension R ρ τ f hf H (z ⊗ₜ[R] v) =
      z • fixedVectorsMap f H v := rfl

/-- The actual fixed inclusion over the coefficient ring. -/
def fixedInclusion (H : Subgroup G) : fixedVectors ρ H →ₗ[R] V :=
  (coefficientFixedVectors R ρ H).subtype

variable (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Compact averaging retracts the actual fixed inclusion coefficient-linearly. -/
def fixedRetraction : V →ₗ[R] fixedVectors ρ K.toSubgroup where
  toFun v := ⟨averageMap ρ hρ K hK v, averageMap_mem_fixedVectors ρ hρ K hK v⟩
  map_add' v w := Subtype.ext ((averageMap ρ hρ K hK).map_add v w)
  map_smul' r v := by
    apply Subtype.ext
    have h := LinearMap.congr_fun
      (averageMap_commute ρ ρ hρ hρ K hK (Jacquet.coefficientIntertwiner R ρ r)) v
    exact h.symm

omit [Algebra R ℂ] in
@[simp] theorem fixedRetraction_fixedInclusion (v : fixedVectors ρ K.toSubgroup) :
    fixedRetraction R ρ hρ K hK (fixedInclusion R ρ K.toSubgroup v) = v :=
  Subtype.ext (averageMap_id ρ hρ K hK v.val v.property)

include hρ hτ hK in
/-- A full scalar-extension bijection restricts to a scalar-extension bijection
on compact fixed vectors, using the split compact average. -/
theorem fixedScalarExtension_bijective
    (hbij : Function.Bijective (scalarExtension R ρ τ f hf)) :
    Function.Bijective (fixedScalarExtension R ρ τ f hf K.toSubgroup) := by
  let i := fixedInclusion R ρ K.toSubgroup
  let p := fixedRetraction R ρ hρ K hK
  let t := fixedScalarExtension R ρ τ f hf K.toSubgroup
  let F := scalarExtension R ρ τ f hf
  have hpi : p.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact fixedRetraction_fixedInclusion R ρ hρ K hK v
  have hpiB : (p.baseChange ℂ).comp (i.baseChange ℂ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  have hi : Function.Injective (i.baseChange ℂ) :=
    (show Function.LeftInverse (p.baseChange ℂ) (i.baseChange ℂ) from
      fun x => LinearMap.congr_fun hpiB x).injective
  have hinc : (fixedVectors τ K.toSubgroup).subtype.comp t =
      F.comp (i.baseChange ℂ) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z v => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have havg : (fixedVectors τ K.toSubgroup).subtype.comp
        (t.comp (p.baseChange ℂ)) = (averageMap τ hτ K hK).comp F := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z v =>
        change z • f (averageMap ρ hρ K hK v) =
          averageMap τ hτ K hK (z • f v)
        rw [map_smul]
        exact congrArg (fun w : W => z • w)
          (LinearMap.congr_fun (averageMap_commute ρ τ hρ hτ K hK f) v)
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro x y hxy
    apply hi
    apply hbij.injective
    exact (LinearMap.congr_fun hinc x).symm.trans
      ((congrArg Subtype.val hxy).trans (LinearMap.congr_fun hinc y))
  · intro w
    obtain ⟨x, hx⟩ := hbij.surjective w.val
    refine ⟨p.baseChange ℂ x, Subtype.ext ?_⟩
    change (t (p.baseChange ℂ x)).val = w.val
    have hxavg := LinearMap.congr_fun havg x
    change (t (p.baseChange ℂ x)).val =
      averageMap τ hτ K hK (scalarExtension R ρ τ f hf x) at hxavg
    rw [hx] at hxavg
    exact hxavg.trans (averageMap_id τ hτ K hK w.val w.property)

/-- The canonical compact-fixed equivalence induced by full scalar specialization. -/
def fixedScalarExtensionEquiv
    (hbij : Function.Bijective (scalarExtension R ρ τ f hf)) :
    ℂ ⊗[R] fixedVectors ρ K.toSubgroup ≃ₗ[ℂ] fixedVectors τ K.toSubgroup :=
  LinearEquiv.ofBijective (fixedScalarExtension R ρ τ f hf K.toSubgroup)
    (fixedScalarExtension_bijective R ρ τ f hf hρ hτ K hK hbij)

/-- The actual compressed action with its compatible coefficient linearity. -/
def compression (g : G) : Module.End R (fixedVectors ρ K.toSubgroup) :=
  Jacquet.CompressionCoefficients.map R (Jacquet.compressedAction ρ hρ K hK g)
    (Jacquet.compressedAction_coefficient_smul R ρ hρ K hK g)

omit [Algebra R ℂ] in
@[simp] theorem compression_pow_apply (g : G) (b : ℕ)
    (v : fixedVectors ρ K.toSubgroup) :
    (compression R ρ hρ K hK g ^ b) v =
      (Jacquet.compressedAction ρ hρ K hK g ^ b) v :=
  Jacquet.CompressionCoefficients.map_pow_apply _ _ _ _ _

/-- Every compression power intertwines under the canonical fixed specialization. -/
theorem fixedScalarExtension_compression_pow (g : G) (b : ℕ) :
    (fixedScalarExtension R ρ τ f hf K.toSubgroup).comp
        ((compression R ρ hρ K hK g).baseChange ℂ ^ b) =
      (Jacquet.compressedAction τ hτ K hK g ^ b).comp
        (fixedScalarExtension R ρ τ f hf K.toSubgroup) := by
  rw [← LinearMap.baseChange_pow]
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
      change z • fixedVectorsMap f K.toSubgroup ((compression R ρ hρ K hK g ^ b) v) =
        (Jacquet.compressedAction τ hτ K hK g ^ b) (z • fixedVectorsMap f K.toSubgroup v)
      rw [compression_pow_apply, map_smul]
      exact congrArg (fun w : fixedVectors τ K.toSubgroup => z • w)
        (Jacquet.compressedAction_pow_natural ρ τ hρ hτ K hK g f b v)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A stable compression power specializes with exactly the same exponent. -/
theorem compressedAction_stablePower
    (hbij : Function.Bijective (scalarExtension R ρ τ f hf)) (g : G) (b : ℕ)
    (hstable : LinearAlgebra.StableEndomorphism.Stable
      (Jacquet.compressedAction ρ hρ K hK g ^ b)) :
    LinearAlgebra.StableEndomorphism.Stable
      (Jacquet.compressedAction τ hτ K hK g ^ b) := by
  have hk : LinearMap.ker (compression R ρ hρ K hK g ^ b) =
      LinearMap.ker ((compression R ρ hρ K hK g ^ b) ^ 2) := by
    ext v
    have hv := SetLike.ext_iff.mp hstable.1 v
    simpa only [LinearMap.mem_ker, pow_two, Module.End.mul_apply,
      compression_pow_apply] using hv
  have hr : LinearMap.range (compression R ρ hρ K hK g ^ b) =
      LinearMap.range ((compression R ρ hρ K hK g ^ b) ^ 2) := by
    ext v
    have hv := SetLike.ext_iff.mp hstable.2 v
    simpa only [LinearMap.mem_range, pow_two, Module.End.mul_apply,
      compression_pow_apply] using hv
  exact LinearAlgebra.StableEndomorphism.stable_of_equiv
    (fixedScalarExtensionEquiv R ρ τ f hf hρ hτ K hK hbij)
    ((compression R ρ hρ K hK g).baseChange ℂ ^ b)
    (Jacquet.compressedAction τ hτ K hK g ^ b)
    (fixedScalarExtension_compression_pow R ρ τ f hf hρ hτ K hK g b)
    (LinearAlgebra.StableEndomorphism.stablePower_baseChange
      (compression R ρ hρ K hK g) b hk hr)

end Langlands.Compact.CoefficientSpecialization
