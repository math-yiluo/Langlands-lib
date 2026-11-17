import Langlands.Global.AdelicGL
import Langlands.Group.GL.Maps

/-! # Inverse transpose and the adelic general linear group maps -/

noncomputable section
universe u

open NumberField IsDedekindDomain Langlands.Global Langlands.GeneralLinear

namespace Langlands.Global.AdelicGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem ext_infinite_finite {g g' : AdelicGL K n} (h1 : infinite K n g = infinite K n g')
    (h2 : finite K n g = finite K n g') : g = g' := by
  rw [← pair_projections K n g, ← pair_projections K n g', h1, h2]

@[simp]
theorem infinite_ofInfinite (x : InfiniteAdelicGL K n) : infinite K n (ofInfinite K n x) = x := by
  apply Units.ext; rfl

@[simp]
theorem finite_ofInfinite (x : InfiniteAdelicGL K n) : finite K n (ofInfinite K n x) = 1 := by
  apply Units.ext; rfl

@[simp]
theorem infinite_ofFinite (x : FiniteAdelicGL K n) : infinite K n (ofFinite K n x) = 1 := by
  apply Units.ext; rfl

@[simp]
theorem finite_ofFinite (x : FiniteAdelicGL K n) : finite K n (ofFinite K n x) = x := by
  apply Units.ext; rfl

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

theorem inverseTranspose_rational (g : RationalGL K n) :
    inverseTranspose n (AdeleRing (𝓞 K) K) (AdelicGL.rational K n g) =
      AdelicGL.rational K n (inverseTranspose n K g) := by
  apply Units.ext
  ext i j
  simp only [inverseTranspose_entry, ← map_inv, AdelicGL.rational_apply]

end Langlands.Automorphic

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

theorem infinite_inverseTranspose (g : AdelicGL F n) :
    AdelicGL.infinite F n (GeneralLinear.inverseTranspose n (AdeleRing (𝓞 F) F) g) =
      GeneralLinear.inverseTranspose n _ (AdelicGL.infinite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.infinite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.infinite_apply]

theorem finite_inverseTranspose (g : AdelicGL F n) :
    AdelicGL.finite F n (GeneralLinear.inverseTranspose n (AdeleRing (𝓞 F) F) g) =
      GeneralLinear.inverseTranspose n _ (AdelicGL.finite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.finite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.finite_apply]

theorem inverseTranspose_ofFinite (l : FiniteAdelicGL F n) :
    GeneralLinear.inverseTranspose n (AdeleRing (𝓞 F) F) (AdelicGL.ofFinite F n l) =
      AdelicGL.ofFinite F n (GeneralLinear.inverseTranspose n _ l) := by
  refine AdelicGL.ext_infinite_finite F n ?_ ?_
  · rw [infinite_inverseTranspose, AdelicGL.infinite_ofFinite, AdelicGL.infinite_ofFinite,
      map_one]
  · rw [finite_inverseTranspose, AdelicGL.finite_ofFinite, AdelicGL.finite_ofFinite]

theorem inverseTranspose_ofInfinite (x : InfiniteAdelicGL F n) :
    GeneralLinear.inverseTranspose n (AdeleRing (𝓞 F) F) (AdelicGL.ofInfinite F n x) =
      AdelicGL.ofInfinite F n (GeneralLinear.inverseTranspose n _ x) := by
  refine AdelicGL.ext_infinite_finite F n ?_ ?_
  · rw [infinite_inverseTranspose, AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofInfinite]
  · rw [finite_inverseTranspose, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofInfinite,
      map_one]

end Langlands.Global.RankinSelbergGlobal.Unfolding
