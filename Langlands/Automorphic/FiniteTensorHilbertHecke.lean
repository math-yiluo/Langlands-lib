import Langlands.Automorphic.FiniteTensorHilbertFixed
import Langlands.Automorphic.FiniteTensorHilbertSmoothComponents
import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Hecke.FiniteSampling
import Mathlib.Algebra.Algebra.Equiv

/-! # Compact-open Hecke actions on entire closed Hilbert tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorHilbertHeckeAux

open MeasureTheory

universe uG uW uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ G W) (S : Subrepresentation τ)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The genuine corner action on the full invariant subspace's fixed vectors.
Only its ambient smooth intersection needs to be a smooth representation. -/
def cornerAction :
    Hecke.HeckeAlgebra.Corner μ K hK →ₐ[ℂ]
      Module.End ℂ (fixedVectors S.toRepresentation K.toSubgroup) :=
  ((TensorHilbertFixedAux.fixedInfSmoothEquiv τ S K).conjAlgEquiv ℂ).toAlgHom.comp
    (Hecke.cornerAction μ
      (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation
      (TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation _ inf_le_right) K hK)

/-- The actual-vector identification intertwines the whole corner action. -/
theorem cornerAction_smooth (f : Hecke.HeckeAlgebra.Corner μ K hK)
    (x : fixedVectors
      (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation K.toSubgroup) :
    cornerAction τ S μ K hK f (TensorHilbertFixedAux.fixedInfSmoothEquiv τ S K x) =
      TensorHilbertFixedAux.fixedInfSmoothEquiv τ S K
        (Hecke.cornerAction μ
          (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation
          (TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation _ inf_le_right)
          K hK f x) := by
  simp only [cornerAction, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Every full fixed vector is acted on by a finite weighted sum of the
unchanged ambient group operators; samples depend only on the corner element. -/
theorem cornerAction_eq_sum (f : Hecke.HeckeAlgebra.Corner μ K hK)
    (x : fixedVectors S.toRepresentation K.toSubgroup) :
    let t := Hecke.fixedLevelActionSamples μ K
      (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)
      (Hecke.HeckeAlgebra.Corner.rightInvariant μ K hK f)
    (cornerAction τ S μ K hK f x).val.val =
      ∑ i, t.coefficients i • τ (t.points i) x.val.val := by
  let A := S ⊓ Langlands.smoothSubrepresentation τ
  let x' := (TensorHilbertFixedAux.fixedInfSmoothEquiv τ S K).symm x
  have h := Hecke.fixedLevelActionSamples_action μ K
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)
    (Hecke.HeckeAlgebra.Corner.rightInvariant μ K hK f)
    A.toRepresentation
    (TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation _ inf_le_right)
    x'.val x'.property
  have hv := congrArg A.toSubmodule.subtype h
  simp only [map_sum, map_smul] at hv
  exact hv

/-- A genuine equivalence onto the ambient smooth intersection transports the
original factor's integrated corner action to the full fixed-space action. -/
theorem cornerAction_factor {A : Type uA} [AddCommGroup A] [Module ℂ A]
    {σ : Representation ℂ G A} (hσ : IsSmooth σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : Hecke.HeckeAlgebra.Corner μ K hK)
    (x : fixedVectors σ K.toSubgroup) :
    TensorHilbertFixedAux.factorFixedEquiv τ S e K
        (Hecke.cornerAction μ σ hσ K hK f x) =
      cornerAction τ S μ K hK f
        (TensorHilbertFixedAux.factorFixedEquiv τ S e K x) := by
  dsimp only [TensorHilbertFixedAux.factorFixedEquiv, LinearEquiv.trans_apply]
  rw [Hecke.cornerAction_equiv μ σ hσ K hK
    (TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation _ inf_le_right) e]
  exact (cornerAction_smooth τ S μ K hK f
    (fixedVectorsEquiv e K.toSubgroup x)).symm

end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertHeckeRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertHeckeFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertHeckeLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorHilbertHeckeMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorHilbertHeckeBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Every compact-open corner acts on the full closed slice's fixed vectors,
using the actual local group and a specified genuine Haar measure. -/
def sliceHilbertCornerAction (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v))) :=
  TensorHilbertHeckeAux.cornerAction
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y) μ K hK

end FiniteTensorPresentation
end Langlands.Automorphic
