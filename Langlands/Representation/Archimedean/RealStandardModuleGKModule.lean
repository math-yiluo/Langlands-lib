import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.RealStandardModuleFourier
import Langlands.Representation.Archimedean.RealGenericParameterReduction

/-!
# The `(𝔤𝔩_n(ℝ), O(n))`-module of a real standard module

The real standard module `realStandardModule n ds` is stable under right translation by all of
`GL_n(ℝ)` and under right derivatives. Its `O(n)`-finite functions are therefore stable under
right translation by `O(n)` and under right derivatives, and they form a
`(𝔤𝔩_n(ℝ), O(n))`-module `(realStandardRep n ds, realStandardLie n ds)`. The identity map is an
`IsRealStandardIntertwiner` map from the `O(n)`-finite functions to this module.
-/

noncomputable section

open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-! ## Stability of `realStandardModule` -/

/-- The real standard module is stable under right translation by every element of
`GL_n(ℝ)`. -/
theorem rightTranslation_mem_realStandardModule_of_mem {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ realStandardModule N ds)
    (s : Langlands.GeneralLinear N ℝ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) s f ∈ realStandardModule N ds :=
  rightTranslation_mem_realStandardModule hf s
    (rightTranslation_mem_principalSeries _ (realStandardModule_le_principalSeries N ds hf) s)

/-- The real standard module is stable under right derivatives along every real matrix. -/
theorem rightDerivative_mem_realStandardModule_of_mem {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ realStandardModule N ds)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    rightDerivative (matrixModel ℝ N) X f ∈ realStandardModule N ds :=
  rightDerivative_mem_realStandardModule hf X
    (rightDerivative_mem_principalSeries _ (realStandardModule_le_principalSeries N ds hf) X)

/-- Every function of the real standard module is smooth. -/
theorem contMDiff_of_mem_realStandardModule {N : ℕ} {ds : List RealBlock}
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ realStandardModule N ds) :
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f :=
  (realStandardModule_le_principalSeries N ds hf).1

/-- The `O(n)`-finite functions of a real standard module are stable under right translation
by `O(n)`. -/
theorem rightTranslation_mem_kFiniteFunctions_realStandardModule (n : ℕ) (ds : List RealBlock)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) :=
  rightTranslation_mem_kFiniteFunctions _ _
    (fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k) hf hk

/-- The `O(n)`-finite functions of a real standard module are stable under right derivatives
along `𝔤𝔩_n(ℝ)`. -/
theorem rightDerivative_mem_kFiniteFunctions_realStandardModule (n : ℕ) (ds : List RealBlock)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X f ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) :=
  ⟨rightDerivative_mem_realStandardModule_of_mem hf.1 X,
    rightDerivative_mem_kFiniteVectors _ _
      (fun _ hg => contMDiff_of_mem_realStandardModule hg)
      (fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k) hf X⟩

/-! ## The `(𝔤, K)`-module -/

/-- Right translation by `O(n)` on the `O(n)`-finite functions of the real standard module of
`ds`. -/
def realStandardRep (n : ℕ) (ds : List RealBlock) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ)
      (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :=
  kFiniteRep (realStandardModule n ds)
    fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k

/-- The right-derivative action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on the `O(n)`-finite functions of the
real standard module of `ds`. -/
def realStandardLie (n : ℕ) (ds : List RealBlock) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆
      Module.End ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :=
  kFiniteLie (realStandardModule n ds) (fun _ hf => contMDiff_of_mem_realStandardModule hf)
    (fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k)
    (fun X _ hf => rightDerivative_mem_realStandardModule_of_mem hf X)

@[simp]
theorem realStandardRep_apply_coe (n : ℕ) (ds : List RealBlock)
    (k : Matrix.unitaryGroup (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ((realStandardRep n ds k f : kFiniteFunctions (realStandardModule n ds)
        (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (Unitary.toUnits k) f :=
  rfl

theorem realStandardLie_one_tmul_apply_coe (n : ℕ) (ds : List RealBlock)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ((realStandardLie n ds (1 ⊗ₜ X) f : kFiniteFunctions (realStandardModule n ds)
        (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X f :=
  kFiniteLie_one_tmul_apply_coe _ _ _ _ X f

/-- The `O(n)`-finite functions of the real standard module of `ds` form a
`(𝔤𝔩_n(ℝ), O(n))`-module under right translation and right derivatives. -/
theorem isRealGKModule_realStandardModule (n : ℕ) (ds : List RealBlock) :
    IsRealGKModule n (realStandardRep n ds) (realStandardLie n ds) :=
  isRealGKModule_kFinite _ _ _ _

/-- The identity map is an `IsRealStandardIntertwiner` map from the `O(n)`-finite functions of
the real standard module of `ds` to the `(𝔤𝔩_n(ℝ), O(n))`-module
`(realStandardRep n ds, realStandardLie n ds)`. -/
theorem isRealStandardIntertwiner_id (n : ℕ) (ds : List RealBlock) :
    IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) ds
      LinearMap.id := by
  refine ⟨fun k f =>
      ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, ?_⟩⟩
  · apply Subtype.ext
    rw [LinearMap.id_apply, LinearMap.id_apply, realStandardRep_apply_coe]
    have hk : (Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) =
        (k : Langlands.GeneralLinear n ℝ) :=
      Units.ext rfl
    rw [hk]
  · apply Subtype.ext
    rw [LinearMap.id_apply, LinearMap.id_apply, realStandardLie_one_tmul_apply_coe]

end Langlands.Archimedean
