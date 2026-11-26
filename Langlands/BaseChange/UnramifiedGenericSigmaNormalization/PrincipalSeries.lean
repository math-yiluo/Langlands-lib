import Langlands.BaseChange.UnramifiedGenericSigmaNormalizationStatement
import Langlands.BaseChange.SphericalCosetDescent
import Langlands.ClassFieldTheory.Local.UniverseZero.UniverseZeroModel
import Langlands.LocalField.PadicTowerModuleTopology
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof

/-!
# The canonical action on unramified principal series

The entrywise field automorphism preserves the Borel inducing action. Its pullback on
sections fixes spherical vectors by the Iwasawa decomposition and evaluation at the identity.
-/

noncomputable section

namespace Langlands.BaseChange.UnramifiedSigma

open GeneralLinear Correspondence Unramified SphericalExistence Whittaker
open scoped NNReal

universe uF uE

variable {p : ℕ} [Fact p.Prime]

local instance fieldTopology (L : PadicField.{u} p) : TopologicalSpace L.Carrier :=
  L.canonicalTopologicalData.topology

local instance fieldValuativeRel (L : PadicField.{u} p) : ValuativeRel L.Carrier :=
  L.canonicalTopologicalData.valuativeRel

local instance fieldLocalField (L : PadicField.{u} p) : IsNonarchimedeanLocalField L.Carrier :=
  L.canonicalTopologicalData.localField

variable (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) {r : ℕ} (z : Fin (r + 1) → ℂˣ)

local notation "K" => E.Carrier
local notation "G" => GeneralLinear (r + 1) K
local notation "B" => borelShape r
set_option quotPrecheck false in
local notation "P" => (B).parabolic K
local notation "I" => principalSeriesOfTuple E z
local notation "τ" => borelInducing E z
local notation "T" => E.canonicalTopologicalData

local instance glTopology (n : ℕ) : TopologicalSpace (GeneralLinear n K) :=
  (T).generalLinearTopology n

local instance glTopologicalGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n K) :=
  (T).generalLinearTopologicalGroup n

private theorem ord_sigma (a : K) : (T).ord (σ a) = (T).ord a :=
  LocalClassField.UniverseZero.ord_eq_of_algEquiv (σ.restrictScalars (Padic p)) (T) (T) a

private theorem determinantNorm_sigma {n : ℕ} (g : GeneralLinear n K) :
    (T).determinantNorm n (entrywiseAut σ n g) = (T).determinantNorm n g := by
  apply Units.ext
  apply NNReal.eq
  rw [(T).determinantNorm_coe, (T).determinantNorm_coe]
  change (T).normalizedAbs (↑(Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.map (σ : K →+* K) g)) : K) = _
  rw [Matrix.GeneralLinearGroup.map_det]
  change (T).normalizedAbs (σ (determinant g : K)) = (T).normalizedAbs (determinant g : K)
  rw [(T).normalizedAbs_of_ne_zero ((map_ne_zero σ).mpr (determinant g).ne_zero),
    (T).normalizedAbs_of_ne_zero (determinant g).ne_zero, ord_sigma F E σ]

private theorem halfModulus_sigma (b : P) :
    (T).parabolicHalfModulus B (parabolicAut σ B b) = (T).parabolicHalfModulus B b := by
  apply Units.ext
  simp only [(T).parabolicHalfModulus_apply, (T).leviHalfModulus_apply,
    leviProjection_parabolicAut, (T).leviModulus_apply, leviAut_apply,
    determinantNorm_sigma F E σ]

/-- The full normalized Borel covariance is unchanged by the entrywise field action. -/
theorem borelInducing_sigma (b : P) : τ (parabolicAut σ B b) = τ b := by
  have hblock (i : Fin (r + 1)) (g : GeneralLinear 1 K) :
      blockCharacters E z i (entrywiseAut σ 1 g) = blockCharacters E z i g := by
    apply LinearMap.ext
    intro x
    change (z i ^ (T).ord (↑(Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (σ : K →+* K) g)) : K) : ℂˣ) • x =
      (z i ^ (T).ord (determinant g : K) : ℂˣ) • x
    rw [Matrix.GeneralLinearGroup.map_det]
    change (z i ^ (T).ord (σ (determinant g : K)) : ℂˣ) • x = _
    rw [ord_sigma F E σ]
  have hlevi (m : (B).Levi K) :
      (B).blockTensor (blockCharacters E z) (leviAut σ B m) =
        (B).blockTensor (blockCharacters E z) m := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, BlockShape.blockTensor_tprod,
      leviAut_apply]
    congr 1
    funext i
    exact LinearMap.congr_fun (hblock i (m i)) (v i)
  apply LinearMap.ext
  intro v
  change ((T).parabolicHalfModulus B (parabolicAut σ B b) : ℂ) •
      (B).blockTensor (blockCharacters E z) ((B).leviProjection K (parabolicAut σ B b)) v =
    ((T).parabolicHalfModulus B b : ℂ) •
      (B).blockTensor (blockCharacters E z) ((B).leviProjection K b) v
  rw [halfModulus_sigma F E σ, leviProjection_parabolicAut, hlevi]

/-- The canonical σ-intertwiner on the actual normalized principal series is pullback
by the inverse entrywise automorphism. -/
def principalIntertwiner : SigmaIntertwiner σ (r + 1) I := by
  let : IsModuleTopology F.Carrier E.Carrier := PadicField.padicTowerModuleTopology p F E
  exact Induction.transportSmoothEquiv P (entrywiseAut σ (r + 1))
    (continuous_entrywiseAut σ (r + 1)) (continuous_entrywiseAut_symm σ (r + 1))
    (parabolicAut σ B) (fun _ => rfl) (LinearEquiv.refl ℂ _)
    (fun b v => (LinearMap.congr_fun (borelInducing_sigma F E σ z b) v).symm)

@[simp]
theorem eval_principalIntertwiner (f : Induction.SmoothFunctions P τ) (g : G) :
    Induction.eval P τ (principalIntertwiner F E σ z f) g =
      Induction.eval P τ f (entrywiseAut σ.symm (r + 1) g) := rfl

/-- Spherical sections are determined by evaluation at the identity. The canonical
intertwiner preserves that evaluation and fixes the spherical subspace pointwise. -/
theorem principalIntertwiner_spherical (f : Induction.SmoothFunctions P τ)
    (hf : f ∈ fixedVectors I (sphericalSubgroup E r)) :
    principalIntertwiner F E σ z f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change Induction.eval P τ (principalIntertwiner F E σ z f) g = Induction.eval P τ f g
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul_spherical E g
  have hfix (g : G) (hg : g ∈ sphericalSubgroup E r) :
      Induction.eval P τ f g = Induction.eval P τ f 1 := by
    have h := congrArg (fun v => Induction.eval P τ v 1) (hf ⟨g, hg⟩)
    change Induction.eval P τ f (1 * g) = _ at h
    simpa only [one_mul] using h
  rw [eval_principalIntertwiner, map_mul]
  change Induction.eval P τ f
    (((parabolicAut σ.symm B b : P) : G) * entrywiseAut σ.symm (r + 1) k) = _
  calc
    _ = τ (parabolicAut σ.symm B b) (Induction.eval P τ f (entrywiseAut σ.symm (r + 1) k)) :=
      f.val.property _ _
    _ = τ b (Induction.eval P τ f k) := by
      rw [borelInducing_sigma F E σ.symm z, hfix k hk,
        hfix _ (entrywiseAut_mem_sphericalSubgroup F E σ.symm hk)]
    _ = _ := (f.val.property b k).symm

/-- The rank-one inducing characters and preservation of Whittaker type give
the one-dimensional functional space of the actual principal series. -/
theorem principalSeries_whittakerType (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K) :
    RankinSelberg.IsOfWhittakerType r (standardCharacter ψ r) I := by
  exact RankinSelberg.normalizedProductWhittakerType.{uE, 0} p E ψ r (r + 1)
    (fun _ => 0) (by simp) (blockCharacters E z)
    (fun i => RankinSelberg.scalar_isOfWhittakerType_rankOne ψ _
      (blockCharacters_isAdmissible E z i).1)

end Langlands.BaseChange.UnramifiedSigma
