import Langlands.TraceFormula.RationalLocalGeneralLinear
import Langlands.Global.RationalGLWeakApproximation
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicSpaceLocalFields
import Langlands.Group.GL.FiniteProductCartan

/-! # Weak approximation in the local tensor groups of a Weil restriction -/

noncomputable section

namespace Langlands.TraceFormula

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.GeneralLinear
open scoped NumberField FiniteExtension TensorProduct

universe u

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

section Coordinates

variable (v : Langlands.Global.FinitePlace K) [FiniteDimensional K L]

local notation "Kᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)
local notation "Places" => FinitePlacesAbove L v

local instance : Algebra Kᵥ Eᵥ := LocalBaseChangeAlgebra.algebra K L (.inr v)
local instance : IsModuleTopology Kᵥ Eᵥ := LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)

omit [FiniteDimensional K L] in
private theorem aboveCompletion_isModuleTopology (q : Places) :
    IsModuleTopology Kᵥ (q.1.adicCompletion L) := by
  let : NontriviallyNormedField Kᵥ := AdelicSpaceLocalFields.normedField (𝓞 K) K v
  let : FiniteDimensional Kᵥ (q.1.adicCompletion L) := FiniteExtension.local_finite v q.1
  let : ContinuousSMul Kᵥ (q.1.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (FiniteExtension.continuous_completionMap v q.1)
  exact isModuleTopologyOfFiniteDimensional (𝕜 := Kᵥ) (E := q.1.adicCompletion L)

private def finiteTensorGLCoordinates (n : ℕ) :
    GeneralLinear n Eᵥ ≃ₜ* (∀ q : Places, GeneralLinear n (q.1.adicCompletion L)) :=
  let e : Eᵥ ≃ₐ[Kᵥ] (∀ q : Places, q.1.adicCompletion L) :=
    AlgEquiv.ofBijective (finiteTensorMap (L := L) v) ((completedTensorComparison K L).1 v)
  let _ : ∀ q : Places, IsModuleTopology Kᵥ (q.1.adicCompletion L) :=
    aboveCompletion_isModuleTopology K L v
  generalLinearEquivPi n e.toRingEquiv
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap)

private theorem finiteTensorGLCoordinates_rational (n : ℕ) (g : RationalGL L n) (q : Places) :
    finiteTensorGLCoordinates K L v n
        (Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr v)).toRingHom g) q =
      Matrix.GeneralLinearGroup.map (algebraMap L (q.1.adicCompletion L)) g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change finiteTensorMap (L := L) v ((1 : Kᵥ) ⊗ₜ[K] g i j) q =
    algebraMap L (q.1.adicCompletion L) (g i j)
  exact finiteTensorMap_one_tmul v (g i j) q

end Coordinates

omit [NumberField K] in
private theorem upperPlaceLabel_injective (S : Finset (Langlands.Global.FinitePlace K)) :
    Function.Injective (fun i : Σ v : S, FinitePlacesAbove L v.val => i.2.val) := by
  rintro ⟨v, q⟩ ⟨w, p⟩ h
  have hvw : v = w := Subtype.ext (calc
    v.val = q.val.under (𝓞 K) := (finitePlacesAbove_under v.val q).symm
    _ = p.val.under (𝓞 K) := congrArg (fun z : Langlands.Global.FinitePlace L => z.under (𝓞 K)) h
    _ = w.val := finitePlacesAbove_under w.val p)
  subst w
  exact congrArg (Sigma.mk v) (Subtype.ext h)

/-- Upper rational matrices are dense in the actual local tensor matrix groups
at any finite set of finite places of the base. -/
def LocalTensorRationalDensityStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (S : Finset (Langlands.Global.FinitePlace K)),
    DenseRange (fun g : RationalGL L n => fun v : S =>
      Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L (.inr v.val)).toRingHom g)

set_option maxHeartbeats 1200000 in
theorem localTensorRationalDensity : LocalTensorRationalDensityStatement.{u} := by
  classical
  intro K L _ _ _ _ _ _ n S
  let J := Σ v : S, FinitePlacesAbove L v.val
  let : Fintype J := Fintype.ofFinite J
  let label : J ↪ Langlands.Global.FinitePlace L :=
    ⟨fun j => j.2.val, upperPlaceLabel_injective K L S⟩
  let W := Finset.univ.map label
  let idx : J ≃ W := Equiv.ofBijective
    (fun j => ⟨label j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => label.injective (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hw
      exact ⟨j, Subtype.ext hj⟩⟩
  let H := (Homeomorph.piCongrLeft
    (Y := fun w : W => GeneralLinear n (FiniteCompletion L w.val)) idx).symm
  have hFlat : DenseRange (fun g : RationalGL L n => fun j : J =>
      Matrix.GeneralLinearGroup.map (algebraMap L (FiniteCompletion L (label j))) g) :=
    H.surjective.denseRange.comp (rationalGLWeakApproximation L n W) H.continuous
  let regroup (x : ∀ j : J, GeneralLinear n (FiniteCompletion L (label j))) :
      ∀ v : S, ∀ q : FinitePlacesAbove L v.val, GeneralLinear n (FiniteCompletion L q.val) :=
    fun v q => x ⟨v, q⟩
  have hregroup : Function.Surjective regroup :=
    fun x => ⟨fun j => x j.1 j.2, rfl⟩
  have hc : Continuous regroup :=
    continuous_pi fun v => continuous_pi fun q => continuous_apply (⟨v, q⟩ : J)
  have hGrouped : DenseRange (fun g : RationalGL L n => fun v : S =>
      fun q : FinitePlacesAbove L v.val =>
        Matrix.GeneralLinearGroup.map (algebraMap L (FiniteCompletion L q.val)) g) :=
    hregroup.denseRange.comp hFlat hc
  let chart := Homeomorph.piCongrRight fun v : S => (finiteTensorGLCoordinates K L v.val n).toHomeomorph
  convert chart.symm.surjective.denseRange.comp hGrouped chart.symm.continuous using 1
  funext g
  apply chart.injective
  rw [Function.comp_apply, chart.apply_symm_apply]
  funext v q
  exact finiteTensorGLCoordinates_rational K L v.val n g q

end Langlands.TraceFormula
