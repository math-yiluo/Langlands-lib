import Langlands.HarmonicAnalysis.Distribution.Subspace
import Langlands.Representation.Hecke.BiInvariantProduct
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration

/-! Finite spherical expansions of normalized radical integrals on the two-block Levi. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg
open Langlands.Unramified

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance constantTermExpansionFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance constantTermExpansionFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance constantTermExpansionFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance constantTermExpansionFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier

private def parabolicPointHomeomorph : (B).Levi F.Carrier × Rect ≃ₜ (B).parabolic F.Carrier where
  toFun z := ⟨parabolicPoint h z, parabolicPoint_mem h z⟩
  invFun q := parabolicCoord h q
  left_inv := parabolicCoord_parabolicPoint h
  right_inv q := Subtype.ext (parabolicPoint_parabolicCoord h q)
  continuous_toFun := (continuous_parabolicPoint h F.Carrier).subtype_mk _
  continuous_invFun := continuous_parabolicCoord h F.Carrier

private theorem isLocallyConstant_leviHalfModulus :
    IsLocallyConstant (fun L : (B).Levi F.Carrier =>
      (F.canonicalTopologicalData.leviHalfModulus B L : ℂ)) := by
  let δ := F.canonicalTopologicalData.leviHalfModulus B
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro L
  refine ⟨(fun x => L⁻¹ * x) ⁻¹' (δ.ker : Set ((B).Levi F.Carrier)),
    (F.canonicalTopologicalData.isOpen_ker_leviHalfModulus B).preimage
      (continuous_const.mul continuous_id), by simp, ?_⟩
  intro x hx
  have he : δ (L⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at he
  exact congrArg Units.val he.symm

set_option maxHeartbeats 1000000 in
/-- The normalized radical integral of a spherical function is a finite sum
of tensors of spherical functions on the two standard block factors. -/
theorem exists_twoBlock_sphericalConstantTerm_expansion
    (f : SphericalHeckeAlgebra F t) (dx : Measure Rect) [dx.IsAddHaarMeasure] :
    ∃ (N : ℕ) (α : Fin N → SphericalHeckeAlgebra F (m 0))
      (β : Fin N → SphericalHeckeAlgebra F (m 1)),
      ∀ L : (B).Levi F.Carrier,
        (F.canonicalTopologicalData.leviHalfModulus B L : ℂ) *
          (∫ x, f (parabolicPoint h (L, x)) ∂dx) = ∑ j, α j (L 0) * β j (L 1) := by
  let T := F.canonicalTopologicalData
  let δ := T.leviHalfModulus B
  let f₀ := (Hecke.HeckeAlgebra.Corner.toBiInvariant (sphericalHaar F t)
    (sphericalOpenSubgroup F t) (sphericalOpenSubgroup_isCompact F t) f).val
  let fP := Hecke.TestFunction.pullback (parabolicPointHomeomorph F h)
    (f₀.restrictClosed ((B).isClosed_parabolic F.Carrier))
  let A : SchwartzBruhat ((B).Levi F.Carrier) := fP.partialIntegral dx
  let Φ : SchwartzBruhat ((B).Levi F.Carrier) := ⟨fun L => (δ L : ℂ) * A L,
    (isLocallyConstant_leviHalfModulus F h).comp₂ A.locallyConstant (· * ·),
    A.hasCompactSupport.mul_left⟩
  have hΦ (L : (B).Levi F.Carrier) :
      Φ L = (δ L : ℂ) * (∫ x, f (parabolicPoint h (L, x)) ∂dx) := rfl
  have hLeft (k L : (B).Levi F.Carrier)
      (hk : ∀ i : Fin 2, k i ∈ sphericalOpenSubgroup F (m i)) : Φ (k * L) = Φ L := by
    rw [hΦ, hΦ, map_mul, leviHalfModulus_eq_one_of_forall_spherical F h k hk, one_mul]
    congr 1
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    have hp : parabolicPoint h (k * L, x) =
        (B).leviEmbedding F.Carrier k * parabolicPoint h (L, x) := by
      simp only [parabolicPoint, map_mul, mul_assoc]
    exact (congrArg (fun g => f g) hp).trans
      (Hecke.HeckeAlgebra.Corner.leftInvariant _ _ _ f
        ⟨_, leviEmbedding_mem_spherical_of_forall F h k hk⟩ _)
  have hRight (k L : (B).Levi F.Carrier)
      (hk : ∀ i : Fin 2, k i ∈ sphericalOpenSubgroup F (m i)) : Φ (L * k) = Φ L := by
    rw [hΦ, hΦ, map_mul, leviHalfModulus_eq_one_of_forall_spherical F h k hk, mul_one]
    congr 1
    let c (x : Rect) := (k 0).val * x * ((k 1)⁻¹ : GeneralLinear (m 1 + 1) F.Carrier).val
    have hc : Continuous c := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have hMap : Measure.map c dx = dx := by
      have hScale := padicRectangularHaarScaling F T (m 0 + 1) (m 1 + 1) dx (k 0) (k 1)
      rw [determinantNorm_eq_one_of_mem_spherical F (hk 0),
        determinantNorm_eq_one_of_mem_spherical F (hk 1)] at hScale
      simpa only [Units.val_one, one_pow, div_one, inv_one, one_smul] using hScale
    have hCont : Continuous (fun x : Rect => f (parabolicPoint h (L, x))) :=
      f₀.continuous.comp ((continuous_parabolicPoint h F.Carrier).comp
        (continuous_const.prodMk continuous_id))
    calc
      _ = ∫ x, f (parabolicPoint h (L, c x)) ∂dx := by
        apply integral_congr_ae
        refine ae_of_all _ fun x => ?_
        change f (parabolicPoint h (L * k, x)) = f (parabolicPoint h (L, c x))
        rw [parabolicPoint_mul_levi_right h L k x]
        exact Hecke.HeckeAlgebra.Corner.rightInvariant _ _ _ f
          ⟨_, leviEmbedding_mem_spherical_of_forall F h k hk⟩ _
      _ = ∫ x, f (parabolicPoint h (L, x)) ∂Measure.map c dx :=
        (integral_map hc.measurable.aemeasurable hCont.aestronglyMeasurable).symm
      _ = _ := by rw [hMap]
  let e := Homeomorph.piFinTwo (fun i : Fin 2 => GeneralLinear (m i + 1) F.Carrier)
  let ψ := Hecke.TestFunction.pullback e.symm Φ
  let K₀ := sphericalOpenSubgroup F (m 0)
  let K₁ := sphericalOpenSubgroup F (m 1)
  let K := K₀.toSubgroup.prod K₁.toSubgroup
  have eMul (a b : (B).Levi F.Carrier) : e (a * b) = e a * e b := rfl
  have eSymmMul (a b : GeneralLinear (m 0 + 1) F.Carrier × GeneralLinear (m 1 + 1) F.Carrier) :
      e.symm (a * b) = e.symm a * e.symm b := by
    apply e.injective
    rw [e.apply_symm_apply, eMul, e.apply_symm_apply, e.apply_symm_apply]
  have hK (k : K) : ∀ i : Fin 2, e.symm k.val i ∈ sphericalOpenSubgroup F (m i) := by
    have he : (e.symm k.val 0, e.symm k.val 1) = k.val := e.apply_symm_apply _
    intro i
    fin_cases i
    · change e.symm k.val 0 ∈ K₀
      have he₀ : e.symm k.val 0 = k.val.1 := congrArg Prod.fst he
      exact he₀.symm ▸ k.property.1
    · change e.symm k.val 1 ∈ K₁
      have he₁ : e.symm k.val 1 = k.val.2 := congrArg Prod.snd he
      exact he₁.symm ▸ k.property.2
  have hψ : ψ ∈ Hecke.TestFunction.biInvariant K K := by
    constructor
    · intro k z
      change Φ (e.symm (k.val * z)) = Φ (e.symm z)
      rw [eSymmMul]
      exact hLeft _ _ (hK k)
    · intro k z
      change Φ (e.symm (z * k.val)) = Φ (e.symm z)
      rw [eSymmMul]
      exact hRight _ _ (hK k)
  obtain ⟨N, α, β, hsum⟩ := Hecke.TestFunction.exists_biInvariant_tensor_expansion ψ hψ
  let c₀ := Hecke.HeckeAlgebra.Corner.toBiInvariant (sphericalHaar F (m 0)) K₀
    (sphericalOpenSubgroup_isCompact F (m 0))
  let c₁ := Hecke.HeckeAlgebra.Corner.toBiInvariant (sphericalHaar F (m 1)) K₁
    (sphericalOpenSubgroup_isCompact F (m 1))
  refine ⟨N, c₀.symm ∘ α, c₁.symm ∘ β, fun L => ?_⟩
  rw [← hΦ]
  have hsumL := hsum (L 0) (L 1)
  change Φ (e.symm (e L)) = _ at hsumL
  rwa [e.symm_apply_apply] at hsumL

end Langlands.BaseChange
