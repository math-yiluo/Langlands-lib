import Langlands.Automorphic.TransposeAmbient
import Langlands.Global.ArchimedeanTransposeSmooth
import Langlands.Automorphic.FiniteDifferential

/-! # Inverse-transpose pullback on actual finite-smooth adelic functions -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear NumberField IsDedekindDomain
open ContinuousRationalFunctions

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance transposeFiniteRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance transposeFiniteContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance transposeFiniteSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _

/-- Smooth archimedean slices are preserved by the continuous inverse-transpose pullback. -/
theorem continuousTranspose_mem_infiniteSmooth {f : ContinuousRationalFunctions K n}
    (hf : f ∈ infiniteSmoothSubrepresentation K n) :
    continuousTranspose K n f ∈ infiniteSmoothSubrepresentation K n := by
  change f ∈ (⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b)) at hf
  change continuousTranspose K n f ∈ (⨅ b : FiniteAdelicGL K n,
    (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b))
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf ⊢
  intro b
  rw [infiniteSlice_continuousTranspose]
  exact (ArchimedeanGL.smoothTranspose K n
    ⟨infiniteSlice K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) b) f, hf _⟩).property

private theorem continuousTranspose_mem_finiteSmoothRational
    {f : ContinuousRationalFunctions K n}
    (hf : f ∈ finiteSmoothRationalSubrepresentation K n) :
    continuousTranspose K n f ∈ finiteSmoothRationalSubrepresentation K n :=
  ⟨continuousTranspose_mem_infiniteSmooth K n hf.1,
    continuousTranspose_mem_finiteSmooth K n hf.2⟩

/-- The actual adelic function pullback, retaining infinite smoothness and a common finite level. -/
def finiteSmoothTranspose :
    FiniteSmoothRationalFunctions K n ≃ₗ[ℂ] FiniteSmoothRationalFunctions K n where
  toFun f := ⟨continuousTranspose K n f.val,
    continuousTranspose_mem_finiteSmoothRational K n f.property⟩
  invFun f := ⟨continuousTranspose K n f.val,
    continuousTranspose_mem_finiteSmoothRational K n f.property⟩
  left_inv f := Subtype.ext (continuousTranspose_involutive K n f.val)
  right_inv f := Subtype.ext (continuousTranspose_involutive K n f.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem finiteSmoothTranspose_val (f : FiniteSmoothRationalFunctions K n) :
    (finiteSmoothTranspose K n f).val = continuousTranspose K n f.val := rfl

@[simp]
theorem finiteSmoothTranspose_involutive (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n (finiteSmoothTranspose K n f) = f :=
  (finiteSmoothTranspose K n).left_inv f

@[simp]
theorem finiteSmoothTranspose_symm :
    (finiteSmoothTranspose K n).symm = finiteSmoothTranspose K n := rfl

@[simp]
theorem finiteSmoothSlice_transpose (b : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothSlice K n b (finiteSmoothTranspose K n f) =
      ArchimedeanGL.smoothTranspose K n
        (finiteSmoothSlice K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) b) f) := by
  apply Subtype.ext
  exact infiniteSlice_continuousTranspose K n b f.val

/-- Finite adelic translation is twisted by inverse transpose. -/
theorem finiteSmoothTranspose_finiteRightAction (d : FiniteAdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n
        (finiteSmoothFiniteRightAction K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) f) =
      finiteSmoothFiniteRightAction K n d (finiteSmoothTranspose K n f) := by
  apply Subtype.ext
  change continuousTranspose K n
      (continuousRightAction K n
        (AdelicGL.ofFinite K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d)) f.val) = _
  rw [continuousTranspose_rightAction, Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofFinite,
    inverseTranspose_involutive]
  rfl

/-- Full adelic translation is twisted on the finite-smooth ambient space. -/
theorem finiteSmoothTranspose_rightAction (g : AdelicGL K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n (finiteSmoothRightAction K n g f) =
      finiteSmoothRightAction K n (inverseTranspose n (AdeleRing (𝓞 K) K) g)
        (finiteSmoothTranspose K n f) := by
  apply Subtype.ext
  exact continuousTranspose_rightAction K n g f.val

/-- The actual enveloping algebra action has the differential inverse-transpose twist. -/
theorem finiteSmoothTranspose_envelopingAction
    (a : ArchimedeanGL.EnvelopingAlgebra K n) (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n
        (finiteSmoothEnvelopingAction K n (ArchimedeanGL.envelopingIota K n a) f) =
      finiteSmoothEnvelopingAction K n a (finiteSmoothTranspose K n f) := by
  apply finiteSmoothSlice_injective K n
  funext b
  simp only [finiteSmoothSlice_transpose, finiteSmoothSlice_envelopingAction,
    ArchimedeanGL.smoothTranspose_envelopingAction]

/-- Covariance restricts to the genuine differential center. -/
theorem finiteSmoothTranspose_centerAction (z : ArchimedeanGL.EnvelopingCenter K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n
        (finiteSmoothCenterAction K n (ArchimedeanGL.centerIota K n z) f) =
      finiteSmoothCenterAction K n z (finiteSmoothTranspose K n f) := by
  change finiteSmoothTranspose K n
      (finiteSmoothEnvelopingAction K n
        (ArchimedeanGL.centerInclusion K n (ArchimedeanGL.centerIota K n z)) f) = _
  rw [ArchimedeanGL.centerInclusion_centerIota]
  exact finiteSmoothTranspose_envelopingAction K n _ f

/-- The common center orbit, on the actual functions rather than individual slices, is transported. -/
theorem finiteSmoothCenterOrbitSpan_transpose (f : FiniteSmoothRationalFunctions K n) :
    (FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation K n) f).map
        (finiteSmoothTranspose K n).toLinearMap =
      FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation K n)
        (finiteSmoothTranspose K n f) := by
  unfold FiniteVectors.orbitSpan
  rw [Submodule.map_span]
  congr 1
  ext h
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨ArchimedeanGL.centerIota K n z, ?_⟩
    change finiteSmoothCenterAction K n (ArchimedeanGL.centerIota K n z)
      (finiteSmoothTranspose K n f) = finiteSmoothTranspose K n (finiteSmoothCenterAction K n z f)
    simpa only [ArchimedeanGL.centerIota_involutive] using
      (finiteSmoothTranspose_centerAction K n (ArchimedeanGL.centerIota K n z) f).symm
  · rintro ⟨z, rfl⟩
    exact ⟨finiteSmoothCenterAction K n (ArchimedeanGL.centerIota K n z) f,
      ⟨ArchimedeanGL.centerIota K n z, rfl⟩, finiteSmoothTranspose_centerAction K n z f⟩

/-- Pullback identifies the complete common center-orbit spaces. -/
def finiteSmoothTransposeCenterOrbitEquiv (f : FiniteSmoothRationalFunctions K n) :
    FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation K n) f ≃ₗ[ℂ]
      FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation K n)
        (finiteSmoothTranspose K n f) :=
  (finiteSmoothTranspose K n).ofSubmodules _ _ (finiteSmoothCenterOrbitSpan_transpose K n f)

/-- Simultaneous center finiteness is preserved and reflected. -/
theorem isCenterFinite_finiteSmoothTranspose_iff (f : FiniteSmoothRationalFunctions K n) :
    IsCenterFinite K n (finiteSmoothInclusion K n (finiteSmoothTranspose K n f)) ↔
      IsCenterFinite K n (finiteSmoothInclusion K n f) := by
  rw [isCenterFinite_iff_finiteSmoothCenterVector, isCenterFinite_iff_finiteSmoothCenterVector]
  exact (LinearMap.finite_iff_of_bijective
    (finiteSmoothTransposeCenterOrbitEquiv K n f).toLinearMap
    (finiteSmoothTransposeCenterOrbitEquiv K n f).bijective).symm

end Langlands.Automorphic
