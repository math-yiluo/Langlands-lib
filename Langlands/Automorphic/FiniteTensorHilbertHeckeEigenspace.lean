import Langlands.Automorphic.FiniteTensorHilbertHeckeBounded
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! # Closed joint Hecke eigenspaces in actual completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorHilbertHeckeAux

universe uA uB

variable {ι : Type uI}
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- The actual intersection of ordinary eigenspaces for a specified family.
No commutation or existence of nonzero eigenvectors is required. -/
def jointEigenspace (T : ι → Module.End ℂ A) (c : ι → ℂ) : Submodule ℂ A :=
  ⨅ i, Module.End.eigenspace (T i) (c i)

theorem mem_jointEigenspace_iff (T : ι → Module.End ℂ A) (c : ι → ℂ) (x : A) :
    x ∈ jointEigenspace T c ↔ ∀ i, T i x = c i • x := by
  simp only [jointEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Intertwining by a genuine equivalence preserves all specified eigen-equations. -/
theorem mem_jointEigenspace_equiv_iff (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) (x : A) :
    e x ∈ jointEigenspace U c ↔ x ∈ jointEigenspace T c := by
  rw [mem_jointEigenspace_iff, mem_jointEigenspace_iff]
  constructor
  · intro hx i
    apply e.injective
    rw [h, hx i, map_smul]
  · intro hx i
    rw [← h, hx i, map_smul]

/-- Restrict the same equivalence to the actual joint eigenspaces. -/
def jointEigenspaceEquiv (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    jointEigenspace T c ≃ₗ[ℂ] jointEigenspace U c where
  toFun x := ⟨e x, (mem_jointEigenspace_equiv_iff e T U c h x).mpr x.property⟩
  invFun y := ⟨e.symm y, (mem_jointEigenspace_equiv_iff e T U c h (e.symm y)).mp
    (by simpa only [e.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' a x := Subtype.ext (e.map_smul a x)

theorem jointEigenspaceEquiv_apply_val (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) (x : jointEigenspace T c) :
    (jointEigenspaceEquiv e T U c h x).val = e x := rfl

theorem jointEigenspaceEquiv_symm_apply_val (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) (y : jointEigenspace U c) :
    ((jointEigenspaceEquiv e T U c h).symm y).val = e.symm y := rfl

/-- Nonzero joint eigenspaces correspond, without asserting their existence. -/
theorem jointEigenspace_ne_bot_iff (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    jointEigenspace U c ≠ ⊥ ↔ jointEigenspace T c ≠ ⊥ := by
  rw [← Submodule.nontrivial_iff_ne_bot, ← Submodule.nontrivial_iff_ne_bot]
  exact (jointEigenspaceEquiv e T U c h).toEquiv.nontrivial_congr.symm

section Normed

variable {H : Type uB} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- An arbitrary intersection of continuous-operator eigenspaces is closed. -/
theorem isClosed_jointEigenspace (T : ι → H →L[ℂ] H) (c : ι → ℂ) :
    IsClosed (jointEigenspace (fun i => (T i).toLinearMap) c : Set H) := by
  simp only [jointEigenspace, Submodule.coe_iInf]
  exact isClosed_iInter (fun i => ContinuousLinearMap.isClosed_eigenspace (T i) (c i))

end Normed

open MeasureTheory
universe uG uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ G W) (S : Subrepresentation τ)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Joint eigenspace of the genuine corner operators on the entire fixed space. -/
def cornerJointEigenspace (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    Submodule ℂ (fixedVectors S.toRepresentation K.toSubgroup) :=
  jointEigenspace (fun i => cornerAction τ S μ K hK (f i)) c

/-- The original smooth factor's joint eigenspace is identified through the
same original-factor fixed-space equivalence. -/
def factorJointCornerEquiv {σ : Representation ℂ G A} (hσ : IsSmooth σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    jointEigenspace (fun i => Hecke.cornerAction μ σ hσ K hK (f i)) c ≃ₗ[ℂ]
      cornerJointEigenspace τ S μ K hK f c :=
  jointEigenspaceEquiv (TensorHilbertFixedAux.factorFixedEquiv τ S e K)
    _ _ c (fun i x => cornerAction_factor τ S μ K hK hσ e (f i) x)

section Bounded

variable {H : Type uW} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (τH : Representation ℂ G H) (SH : Subrepresentation τH)
variable (hτ : ∀ (g : G) (x : H), ‖τH g x‖ = ‖x‖)

/-- Forgetting the continuous maps yields exactly the same joint submodule. -/
theorem cornerJointEigenspace_eq_continuous
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    cornerJointEigenspace τH SH μ K hK f c =
      jointEigenspace
        (fun i => (cornerContinuousAction μ K hK τH SH hτ (f i)).toLinearMap) c := rfl

include hτ in
/-- Closedness uses boundedness of the unchanged full-fixed-space operators. -/
theorem cornerJointEigenspace_isClosed
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    IsClosed (cornerJointEigenspace τH SH μ K hK f c :
      Set (fixedVectors SH.toRepresentation K.toSubgroup)) := by
  rw [cornerJointEigenspace_eq_continuous μ K hK τH SH hτ f c]
  exact isClosed_jointEigenspace _ c

end Bounded
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ι : Type uI}

local instance tensorHilbertEigenspaceRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorHilbertEigenspaceMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorHilbertEigenspaceBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual joint eigenspace inside the full closed tensor-slice fixed space. -/
def sliceHilbertJointCornerEigenspace (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v)))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :=
  TensorHilbertHeckeAux.cornerJointEigenspace
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y) μ K hK f c

/-- Recover the original admissible factor's same joint eigen-equations,
retaining the explicit nonzero complementary tensor. -/
def factorHilbertJointCornerEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (hA : IsAdmissible (ρ v))
    (μ : Measure (FiniteLocalGL F n v)) [μ.IsHaarMeasure]
    (K : OpenSubgroup (FiniteLocalGL F n v))
    (hK : IsCompact (K : Set (FiniteLocalGL F n v)))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :=
  TensorHilbertHeckeAux.factorJointCornerEquiv
    (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)
    (P.sliceHilbertRange b v y) μ K hK hA.1
    (P.factorHilbertSmoothEquiv b v y hy hA) f c

end FiniteTensorPresentation
end Langlands.Automorphic
