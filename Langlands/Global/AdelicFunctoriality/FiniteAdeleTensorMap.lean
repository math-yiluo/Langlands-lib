/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper

Modified by Worker 300 (2026): reformulate the canonical finite-adele base-change map
of Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:75-127 and 255-270, through
Mathlib's universal property `AlgHom.liftEquiv` in the left tensor order
`A_K ⊗[K] L`, using the Library's scoped finite-adele algebra and inclusion.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.FiniteAdeleAlgebra

/-! # The canonical map `A_K ⊗[K] L → A_L` of finite adele rings

For a finite extension `L / K` of number fields, the finite adeles of `L` are an
algebra over the finite adeles of `K` through `finiteAdeleInclusion`. The canonical
map from the base change `A_K ⊗[K] L` sends `x ⊗ l` to the product of the image of
`x` and the diagonal image of `l`.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteAdeleExtension

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The `K`-algebra structure on the finite adeles of `L` obtained by restricting
the `L` diagonal along `K → L`. It is not an instance: as an instance it would apply
to every `K` with `[Algebra K L]`, including `K = L`, where it would compete with
Mathlib's `Algebra L (FiniteAdeleRing (𝓞 L) L)`. -/
abbrev finiteAdeleCoefficientAlgebra : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

omit [NumberField K] in
/-- The coefficient scalar map is `K → L → A_L`. -/
theorem finiteAdeleCoefficientAlgebra_algebraMap :
    letI := finiteAdeleCoefficientAlgebra K L
    algebraMap K (FiniteAdeleRing (𝓞 L) L) =
      (algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L) := rfl

omit [NumberField K] in
/-- The coefficient algebra is compatible with the `L` diagonal. -/
theorem finiteAdeleCoefficientAlgebra_isScalarTower :
    letI := finiteAdeleCoefficientAlgebra K L
    IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  letI := finiteAdeleCoefficientAlgebra K L
  .of_algebraMap_eq fun _ => rfl

/-- The coefficient algebra is compatible with the finite-adele inclusion. -/
theorem finiteAdeleCoefficientAlgebra_isScalarTower_finiteAdeleRing :
    letI := finiteAdeleCoefficientAlgebra K L
    IsScalarTower K (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
  letI := finiteAdeleCoefficientAlgebra K L
  haveI := finiteAdeleCoefficientAlgebra_isScalarTower K L
  FiniteAdeleExtension.instIsScalarTower

/-- The canonical `A_K`-algebra map `A_K ⊗[K] L → A_L`, the base change of the
diagonal `L → A_L`. -/
def finiteAdeleTensorMap :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L →ₐ[FiniteAdeleRing (𝓞 K) K] FiniteAdeleRing (𝓞 L) L :=
  letI := finiteAdeleCoefficientAlgebra K L
  haveI := finiteAdeleCoefficientAlgebra_isScalarTower K L
  haveI := finiteAdeleCoefficientAlgebra_isScalarTower_finiteAdeleRing K L
  AlgHom.liftEquiv K (FiniteAdeleRing (𝓞 K) K) L (FiniteAdeleRing (𝓞 L) L)
    (IsScalarTower.toAlgHom K L (FiniteAdeleRing (𝓞 L) L))

variable {K L}

/-- The pure-tensor evaluation of the canonical map. -/
@[simp] theorem finiteAdeleTensorMap_tmul (x : FiniteAdeleRing (𝓞 K) K) (l : L) :
    finiteAdeleTensorMap K L (x ⊗ₜ[K] l) =
      finiteAdeleInclusion x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l := rfl

/-- The coordinate of a pure-tensor image at a finite place `q` of `L`. -/
theorem finiteAdeleTensorMap_tmul_apply (x : FiniteAdeleRing (𝓞 K) K) (l : L)
    (q : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleTensorMap K L (x ⊗ₜ[K] l) q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) *
        algebraMap L (q.adicCompletion L) l := rfl

theorem finiteAdeleTensorMap_one_tmul (l : L) :
    finiteAdeleTensorMap K L (1 ⊗ₜ[K] l) = algebraMap L (FiniteAdeleRing (𝓞 L) L) l := by
  rw [finiteAdeleTensorMap_tmul, map_one, one_mul]

theorem finiteAdeleTensorMap_tmul_one (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleTensorMap K L (x ⊗ₜ[K] 1) = finiteAdeleInclusion x := by
  rw [finiteAdeleTensorMap_tmul, map_one, mul_one]

end Langlands.Global.AdelicFunctoriality
