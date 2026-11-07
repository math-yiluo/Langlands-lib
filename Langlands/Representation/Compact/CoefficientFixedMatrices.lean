import Langlands.Representation.Compact.CoefficientSpecialization
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

open scoped TensorProduct
open MeasureTheory

namespace Langlands.Compact.CoefficientSpecialization

universe uR uG uV uW un

variable (R : Type uR) [CommRing R] [Algebra R ℂ]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
  [SMulCommClass ℂ R V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
  [HasCompatibleCoefficients R ρ]
variable (f : ρ.IntertwiningMap τ)
  (hf : ∀ (r : R) (v : V), f (r • v) = algebraMap R ℂ r • f v)
  (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hbij : Function.Bijective (scalarExtension R ρ τ f hf))
  {n : Type un}
  (e : Module.Basis n R (fixedVectors ρ K.toSubgroup))

/-- The actual fixed-space basis obtained by scalar extension and evaluation. -/
def specializedBasis : Module.Basis n ℂ (fixedVectors τ K.toSubgroup) :=
  (e.baseChange ℂ).map (fixedScalarExtensionEquiv R ρ τ f hf hρ hτ K hK hbij)

@[simp] theorem specializedBasis_apply (j : n) :
    specializedBasis R ρ τ f hf hρ hτ K hK hbij e j =
      fixedVectorsMap f K.toSubgroup (e j) := by
  change fixedScalarExtension R ρ τ f hf K.toSubgroup
    ((e.baseChange ℂ) j) = _
  rw [Module.Basis.baseChange_apply, fixedScalarExtension_tmul, one_smul]

/-- Coordinates of an evaluated fixed vector are evaluated coefficient coordinates. -/
theorem specializedBasis_repr (v : fixedVectors ρ K.toSubgroup) (i : n) :
    (specializedBasis R ρ τ f hf hρ hτ K hK hbij e).repr
      (fixedVectorsMap f K.toSubgroup v) i =
      algebraMap R ℂ (e.repr v i) := by
  let t := fixedScalarExtensionEquiv R ρ τ f hf hρ hτ K hK hbij
  have ht : t (1 ⊗ₜ[R] v) = fixedVectorsMap f K.toSubgroup v := by
    change fixedScalarExtension R ρ τ f hf K.toSubgroup (1 ⊗ₜ[R] v) = _
    rw [fixedScalarExtension_tmul, one_smul]
  change (e.baseChange ℂ).repr (t.symm (fixedVectorsMap f K.toSubgroup v)) i = _
  rw [← ht, LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]

/-- Every actual Hecke-compressed matrix entry is an evaluated coefficient. -/
theorem specializedBasis_fixedMatrix [MeasurableSpace G] [BorelSpace G] [Fintype n]
    (μ : Measure G) [μ.IsHaarMeasure] (g : G) (i j : n) :
    UnitarizabilityContinuation.fixedMatrix μ hτ hK
      (specializedBasis R ρ τ f hf hρ hτ K hK hbij e) τ g i j =
      algebraMap R ℂ
        (e.repr (Hecke.fixedProjection μ ρ hρ K hK (ρ g (e j))) i) := by
  change (specializedBasis R ρ τ f hf hρ hτ K hK hbij e).repr
    (Hecke.fixedProjection μ τ hτ K hK
      (τ g (specializedBasis R ρ τ f hf hρ hτ K hK hbij e j))) i = _
  rw [specializedBasis_apply]
  have hfg : τ g (fixedVectorsMap f K.toSubgroup (e j) : W) = f (ρ g (e j)) :=
    (Representation.IntertwiningMap.isIntertwining ρ τ f g (e j)).symm
  rw [hfg, ← Hecke.fixedProjection_intertwiner μ ρ hρ K hK hτ f]
  exact specializedBasis_repr R ρ τ f hf hρ hτ K hK hbij e _ i

end Langlands.Compact.CoefficientSpecialization
