import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Automorphic.CuspidalL2.Basics

/-! # Sphericity of the dual cusp form

If the cusp form of `xd` is the dual `φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp form `φ` of `x`, and
`x` is fixed by `GL_n(𝒪_v)` at every finite place `v ∉ S`, then so is `xd`. -/

noncomputable section
universe u
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global Langlands.Automorphic
open Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

local instance contragredientDualSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance contragredientDualSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F

namespace ContragredientDual

/-! ### Transpose inverse on finite adelic and local matrices -/

/-- Transpose inverse commutes with the projection to the infinite factor. -/
theorem infinite_inverseTranspose (n : ℕ) (g : AdelicGL F n) :
    AdelicGL.infinite F n (GeneralLinear.inverseTranspose n (Adeles F) g) =
      GeneralLinear.inverseTranspose n (InfiniteAdeleRing F) (AdelicGL.infinite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.infinite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.infinite_apply]

/-- Transpose inverse commutes with the projection to the finite factor. -/
theorem finite_inverseTranspose (n : ℕ) (g : AdelicGL F n) :
    AdelicGL.finite F n (GeneralLinear.inverseTranspose n (Adeles F) g) =
      GeneralLinear.inverseTranspose n (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (AdelicGL.finite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.finite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.finite_apply]

/-- Transpose inverse commutes with the inclusion of the finite factor. -/
theorem inverseTranspose_ofFinite (n : ℕ) (d : FiniteAdelicGL F n) :
    GeneralLinear.inverseTranspose n (Adeles F) (AdelicGL.ofFinite F n d) =
      AdelicGL.ofFinite F n
        (GeneralLinear.inverseTranspose n (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) d) := by
  apply AdelicGL.ext_infinite_finite
  · rw [infinite_inverseTranspose, AdelicGL.infinite_ofFinite, AdelicGL.infinite_ofFinite,
      map_one]
  · rw [finite_inverseTranspose, AdelicGL.finite_ofFinite, AdelicGL.finite_ofFinite]

/-- Transpose inverse commutes with the projection to a finite place. -/
theorem localProjection_inverseTranspose (n : ℕ) (v : FinitePlace F) (g : FiniteAdelicGL F n) :
    FiniteAdelicGL.localProjection F n v
        (GeneralLinear.inverseTranspose n (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) g) =
      GeneralLinear.inverseTranspose n (FiniteCompletion F v)
        (FiniteAdelicGL.localProjection F n v g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [FiniteAdelicGL.localProjection_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, FiniteAdelicGL.localProjection_apply]

/-- Transpose inverse commutes with the inclusion of a finite place. -/
theorem inverseTranspose_localInclusion (n : ℕ) (v : FinitePlace F) (k : FiniteLocalGL F n v) :
    GeneralLinear.inverseTranspose n (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (FiniteAdelicGL.localInclusion F n v k) =
      FiniteAdelicGL.localInclusion F n v (GeneralLinear.inverseTranspose n _ k) := by
  apply FiniteAdelicGL.ext_localProjection
  intro w
  rw [localProjection_inverseTranspose]
  by_cases hw : w = v
  · subst w
    simp only [FiniteAdelicGL.localProjection_localInclusion]
  · simp only [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw, map_one]

/-- `GL_n(𝒪_v)` is stable under transpose inverse. -/
theorem inverseTranspose_mem_localIntegral (n : ℕ) (v : FinitePlace F)
    {k : FiniteLocalGL F n v} (hk : k ∈ FiniteAdelicGL.localIntegral F n v) :
    GeneralLinear.inverseTranspose n _ k ∈ FiniteAdelicGL.localIntegral F n v := by
  rw [FiniteAdelicGL.mem_localIntegral] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GeneralLinear.inverseTranspose_entry]
    exact hk.2 j i
  · rw [← map_inv, GeneralLinear.inverseTranspose_entry, inv_inv]
    exact hk.1 j i

/-- Transpose inverse of a finite adelic point. -/
theorem iota_ofFinite (n : ℕ) (d : FiniteAdelicGL F n) :
    iota F n ((E n).symm (AdelicGL.ofFinite F n d)) =
      (E n).symm (AdelicGL.ofFinite F n (GeneralLinear.inverseTranspose n _ d)) := by
  apply (E n).injective
  rw [adelicEquiv_iota, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    inverseTranspose_ofFinite]

/-! ### Cusp functions -/

variable [CompactSpace (AdeleQuotient F)]

/-- The finite action on a cuspidal realization is right translation of its cusp functions. -/
theorem cuspFunction_finiteRepresentation {r : ℕ} (T : CuspidalOperatorRealization F r)
    (d : FiniteAdelicGL F (r + 1)) (x : T.Space) (p : Points F (r + 1)) :
    cuspFunction F T (T.realization.finiteRepresentation d x) p =
      cuspFunction F T x (p * (E (r + 1)).symm (AdelicGL.ofFinite F (r + 1) d)) := by
  refine (congrFun (cuspFunction_eq F T (T.realization.finiteRepresentation d x)) p).trans ?_
  refine Eq.trans ?_ (congrFun (cuspFunction_eq F T x) _).symm
  have h : GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
        (p * (E (r + 1)).symm (AdelicGL.ofFinite F (r + 1) d)) =
      GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) p * AdelicGL.ofFinite F (r + 1) d := by
    rw [map_mul]
    congr 1
    exact MulEquiv.apply_symm_apply (E (r + 1)) _
  show ContinuousRationalFunctions.evaluate F (r + 1)
      (T.realization.toContinuous (T.realization.finiteRepresentation d x))
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) p) =
    ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x)
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
        (p * (E (r + 1)).symm (AdelicGL.ofFinite F (r + 1) d)))
  exact (OperatorRealization.evaluate_finiteRepresentation T.realization d x _).trans
    (congrArg (ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x))
      h.symm)

/-- A vector of a cuspidal realization is determined by its cusp function. -/
theorem cuspFunction_injective {r : ℕ} (T : CuspidalOperatorRealization F r) :
    Function.Injective (cuspFunction F T) := by
  intro x y h
  apply T.realization.toContinuous_injective
  apply ContinuousRationalFunctions.toContinuousMap_injective
  ext g
  have hg := congrFun h ((E (r + 1)).symm g)
  rw [cuspFunction_eq F T x, cuspFunction_eq F T y] at hg
  change ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x)
      (E (r + 1) ((E (r + 1)).symm g)) =
    ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous y)
      (E (r + 1) ((E (r + 1)).symm g)) at hg
  rw [MulEquiv.apply_symm_apply] at hg
  exact hg

end ContragredientDual

variable [CompactSpace (AdeleQuotient F)]

open ContragredientDual in
/-- **Sphericity transfer.** If the cusp function of `xd` is the dual of that of `x`, and `x`
is fixed by `GL_n(𝒪_v)` at every finite place `v ∉ S`, then so is `xd`. -/
theorem isSphericalOutside_of_cuspFunction_eq_dual {r : ℕ}
    (T Td : CuspidalOperatorRealization F r) (S : Finset (FinitePlace F))
    (x : T.Space) (xd : Td.Space)
    (hxd : cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x))
    (hx : IsSphericalOutside F T S x) : IsSphericalOutside F Td S xd := by
  intro v hv k hk
  apply cuspFunction_injective F Td
  funext p
  have hφ := cuspFunction_rational_mul F T x
  rw [cuspFunction_finiteRepresentation, hxd, dualFunction_eq F _ hφ, dualFunction_eq F _ hφ,
    iota_mul, iota_ofFinite, inverseTranspose_localInclusion,
    ← cuspFunction_finiteRepresentation,
    hx v hv _ (inverseTranspose_mem_localIntegral F (r + 1) v hk)]

section Statement

/-- **Sphericity of the dual cusp form** (packaged). For every number field `F` with
`F \ 𝔸_F` compact, all actual cuspidal realizations `T` and `Td` of `GL_(r+1)`, every finite
set `S` of finite places, and vectors `x` of `T` and `xd` of `Td`: if the cusp function of `xd`
is the dual `φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp function `φ` of `x`, and `x` is fixed by
`GL_(r+1)(𝒪_v)` at every finite place `v ∉ S`, then so is `xd`. -/
def ContragredientDualSphericalStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T Td : CuspidalOperatorRealization F r) (S : Finset (FinitePlace F))
    (x : T.Space) (xd : Td.Space),
    cuspFunction F Td xd = dualFunction F (r + 1) (cuspFunction F T x) →
    IsSphericalOutside F T S x → IsSphericalOutside F Td S xd

/-- Proof of `ContragredientDualSphericalStatement`. -/
theorem contragredientDualSpherical : ContragredientDualSphericalStatement.{u} :=
  fun F _ _ _ _ T Td S x xd hxd hx =>
    isSphericalOutside_of_cuspFunction_eq_dual F T Td S x xd hxd hx

end Statement

end Langlands.Global.RankinSelbergGlobal
