import Langlands.Global.RankinSelberg.RealGodementCanonicalCoefficient
import Langlands.Representation.Archimedean.RealExponentDeformation

/-! # Compact and Lie equivariance of the canonical real Jacquet map -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.Whittaker
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PrincipalSeriesExtension RealGodementProfiles

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)
local notation "P" => (Fin (r + 1) → ℂ)
local notation "L" => (Fin (r + 1) → Fin 2)
local notation "X" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "V(" p "," z ")" => Automorphic.realStandardKFinite (r + 1) (characterList p z)
local notation "Dᵣ" => rightDerivative (matrixModel ℝ (r + 1))

private theorem eq_of_compactRestriction_eq {p : L} {z : P} {f f' : V(p,z)}
    (h : compactRestriction f.val = compactRestriction f'.val) : f = f' := by
  apply Subtype.ext
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.property.1.1 f'.property.1.1
  intro g hg
  let k : U := ⟨g.val, hg⟩
  have hk : Unitary.toUnits k = g := Units.ext rfl
  have he := congrFun h k
  change f.val (Unitary.toUnits k) = f'.val (Unitary.toUnits k) at he
  rwa [hk] at he

/-- Transfer a K-finite real character section to new exponents through its compact profile. -/
def characterSectionTransfer (p : L) (z w : P) : V(p,z) →ₗ[ℂ] V(p,w) := by
  let T : V(p,z) →ₗ[ℂ] (G → ℂ) := {
    toFun := fun f => standardSection w (compactRestriction f.val)
    map_add' := fun x y => (extensionLinear _).map_add (compactRestriction x.val) (compactRestriction y.val)
    map_smul' := fun c x => (extensionLinear _).map_smul c (compactRestriction x.val) }
  exact T.codRestrict _ fun f => standardSection_mem (isCompactProfile_compactRestriction f.property) w

@[simp] theorem compactRestriction_characterSectionTransfer (p : L) (z w : P) (f : V(p,z)) :
    compactRestriction (characterSectionTransfer p z w f).val = compactRestriction f.val :=
  compactRestriction_standardSection (compactRestriction f.val) w

@[simp] theorem characterSectionTransfer_self (p : L) (z : P) (f : V(p,z)) :
    characterSectionTransfer p z z f = f :=
  eq_of_compactRestriction_eq (compactRestriction_characterSectionTransfer p z z f)

private theorem holomorphic_canonicalTransfer (a : ℝˣ) (p : L) (z : P) (f : V(p,z))
    (Xs : List X) (g : G) :
    Differentiable ℂ (fun w : P => RealLocalWhittaker.iteratedRightDerivative r Xs
      (canonicalJacquetMap a p w (characterSectionTransfer p z w f)) g) := by
  let hφ := isCompactProfile_compactRestriction f.property
  have he (w : P) : canonicalJacquetMap a p w (characterSectionTransfer p z w f) =
      canonicalJacquetFamily a hφ w := canonicalJacquetMap_standardSection a hφ w
  simp only [he]
  exact (canonicalJacquetFamily_properties a hφ).2.2.1 Xs g

private theorem characterSectionTransfer_compactAction (p : L) (z w : P) (f : V(p,z)) (k : U) :
    characterSectionTransfer p z w (realStandardRep _ _ k f) =
      realStandardRep _ _ k (characterSectionTransfer p z w f) := by
  apply eq_of_compactRestriction_eq
  rw [compactRestriction_characterSectionTransfer, realStandardRep_apply_coe, realStandardRep_apply_coe]
  funext u
  have he := congrFun (compactRestriction_characterSectionTransfer p z w f) (u * k)
  change (characterSectionTransfer p z w f).val (Unitary.toUnits (u * k)) = f.val (Unitary.toUnits (u * k)) at he
  rw [map_mul] at he
  exact he.symm

/-- The canonical evaluation commutes with right translation by the orthogonal subgroup. -/
theorem canonicalJacquetMap_compactAction (a : ℝˣ) (p : L) (z : P) (f : V(p,z)) (k : U) :
    canonicalJacquetMap a p z (realStandardRep _ _ k f) =
      rightTranslation ℂ G (Unitary.toUnits k) (canonicalJacquetMap a p z f) := by
  let V₁ (w : P) := canonicalJacquetMap a p w (characterSectionTransfer p z w (realStandardRep _ _ k f))
  let V₂ (w : P) := rightTranslation ℂ G (Unitary.toUnits k)
    (canonicalJacquetMap a p w (characterSectionTransfer p z w f))
  have h₁ (g : G) : Differentiable ℂ (fun w => V₁ w g) :=
    holomorphic_canonicalTransfer a p z (realStandardRep _ _ k f) [] g
  have h₂ (g : G) : Differentiable ℂ (fun w => V₂ w g) :=
    holomorphic_canonicalTransfer a p z f [] (g * Unitary.toUnits k)
  have hEq : V₁ = V₂ := by
    apply eq_of_eqOn_realSpectralChamber h₁ h₂
    intro w hw g
    change canonicalJacquetMap a p w (characterSectionTransfer p z w (realStandardRep _ _ k f)) g =
      canonicalJacquetMap a p w (characterSectionTransfer p z w f) (g * Unitary.toUnits k)
    rw [canonicalJacquetMap_agrees a p hw, canonicalJacquetMap_agrees a p hw,
      characterSectionTransfer_compactAction, realStandardRep_apply_coe]
    exact additiveJacquetIntegral_rightTranslate a (characterSectionTransfer p z w f).val g (Unitary.toUnits k)
  have he := congrFun hEq z
  simpa only [V₁, V₂, characterSectionTransfer_self] using he

private theorem diagWeight_eq_sum (q : P) (Y : X) (g : G) :
    RealExponentDeformation.diagWeight q Y g =
      ∑ i, q i * RealExponentDeformation.diagWeight (Pi.single i 1) Y g := by
  unfold RealExponentDeformation.diagWeight
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [Pi.single_apply]

private theorem characterSectionTransfer_lieAction (p : L) (z : P) (f : V(p,z)) (Y : X) :
    let d (q : P) : V(p,q) := realStandardLie _ _ (1 ⊗ₜ Y) (characterSectionTransfer p z q f)
    ∀ q : P, d q = characterSectionTransfer p 0 q (d 0) +
      ∑ i : Fin (r + 1), q i • (characterSectionTransfer p (Pi.single i 1) q (d (Pi.single i 1)) -
        characterSectionTransfer p 0 q (d 0)) := by
  intro d q
  let F (w : P) := characterSectionTransfer p z w f
  have hProfile (w : P) : compactRestriction (F w).val = compactRestriction f.val :=
    compactRestriction_characterSectionTransfer p z w f
  have hAt (w : P) {g : G} (hg : g ∈ K) : (F w).val g = f.val g := by
    let u : U := ⟨g.val, hg⟩
    have hu : Unitary.toUnits u = g := Units.ext rfl
    have he := congrFun (hProfile w) u
    change (F w).val (Unitary.toUnits u) = f.val (Unitary.toUnits u) at he
    rwa [hu] at he
  have hD (w : P) (u : U) :
      compactRestriction (d w).val u = compactRestriction (d 0).val u +
        RealExponentDeformation.diagWeight w Y (Unitary.toUnits u) * compactRestriction f.val u := by
    change (realStandardLie _ _ (1 ⊗ₜ Y) (F w)).val (Unitary.toUnits u) =
      (realStandardLie _ _ (1 ⊗ₜ Y) (F 0)).val (Unitary.toUnits u) + _
    rw [realStandardLie_one_tmul_apply_coe, realStandardLie_one_tmul_apply_coe]
    have hEq : Set.EqOn (F w).val (F 0).val K := fun _ hk => (hAt w hk).trans (hAt 0 hk).symm
    have hu : Unitary.toUnits u ∈ K := u.property
    have he := RealExponentDeformation.rightDerivative_eq_of_eqOn_realPosition
      (F w).property.1.1 (F 0).property.1.1 hEq Y hu
    have hExp : (fun i : Fin (r + 1) => realPositionExponent (characterList p w) i -
        realPositionExponent (characterList p 0) i) = w := by
      funext i
      simp only [realPositionExponent_characterList, Pi.zero_apply, sub_zero]
    rw [hExp, hAt w hu] at he
    exact he
  apply eq_of_compactRestriction_eq
  let Q : V(p,q) →ₗ[ℂ] (U → ℂ) := compactRestriction.comp (V(p,q)).subtype
  change _ = Q (characterSectionTransfer p 0 q (d 0) +
    ∑ i : Fin (r + 1), q i • (characterSectionTransfer p (Pi.single i 1) q (d (Pi.single i 1)) -
      characterSectionTransfer p 0 q (d 0)))
  rw [map_add, map_sum]
  funext u
  simp only [map_smul, map_sub, Q, LinearMap.comp_apply, Submodule.subtype_apply,
    compactRestriction_characterSectionTransfer, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hD q u, diagWeight_eq_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hD (Pi.single i 1) u, add_sub_cancel_left, mul_assoc]

/-- The canonical evaluation commutes with real matrix Lie differentiation. -/
theorem canonicalJacquetMap_lieAction (a : ℝˣ) (p : L) (z : P) (f : V(p,z)) (Y : X) :
    canonicalJacquetMap a p z (realStandardLie _ _ (1 ⊗ₜ Y) f) =
      Dᵣ Y (canonicalJacquetMap a p z f) := by
  let F (q : P) := characterSectionTransfer p z q f
  let d (q : P) : V(p,q) := realStandardLie _ _ (1 ⊗ₜ Y) (F q)
  let A (q : P) := canonicalJacquetMap a p q (d q)
  let B (q : P) := Dᵣ Y (canonicalJacquetMap a p q (F q))
  have hA (g : G) : Differentiable ℂ (fun q => A q g) := by
    let A₀ (q : P) := canonicalJacquetMap a p q (characterSectionTransfer p 0 q (d 0)) g
    let Aᵢ (i : Fin (r + 1)) (q : P) :=
      canonicalJacquetMap a p q (characterSectionTransfer p (Pi.single i 1) q (d (Pi.single i 1))) g
    have h₀ : Differentiable ℂ A₀ := holomorphic_canonicalTransfer a p 0 (d 0) [] g
    have hᵢ (i : Fin (r + 1)) : Differentiable ℂ (Aᵢ i) :=
      holomorphic_canonicalTransfer a p (Pi.single i 1) (d (Pi.single i 1)) [] g
    have hExpr (q : P) : A q g = A₀ q + ∑ i, q i * (Aᵢ i q - A₀ q) := by
      change canonicalJacquetMap a p q (d q) g = _
      rw [show d q = _ from characterSectionTransfer_lieAction p z f Y q]
      simp only [map_add, map_sum, map_smul, map_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.sum_apply, A₀, Aᵢ, d, F]
    simp only [hExpr]
    exact h₀.add (Differentiable.fun_sum fun i _ =>
      ((ContinuousLinearMap.proj i : P →L[ℂ] ℂ).differentiable).mul ((hᵢ i).sub h₀))
  have hB (g : G) : Differentiable ℂ (fun q => B q g) :=
    holomorphic_canonicalTransfer a p z f [Y] g
  have he : A = B := by
    apply eq_of_eqOn_realSpectralChamber hA hB
    intro q hq g
    let hDom := isStrictlyDominant_characterList p hq
    have hMap (x : V(p,q)) : canonicalJacquetMap a p q x = additiveJacquetUniformLinear a hDom x :=
      (canonicalJacquetMap_agrees a p hq x).trans (additiveJacquetUniformLinear_apply a hDom x).symm
    change canonicalJacquetMap a p q (d q) g = Dᵣ Y (canonicalJacquetMap a p q (F q)) g
    rw [hMap, hMap]
    exact congrFun ((isRealUniformWhittakerIntertwiner_additiveJacquetUniformLinear a hDom).1.2.2.2.2
      Y (F q) (d q) (realStandardLie_one_tmul_apply_coe _ _ Y (F q))) g
  simpa only [A, B, d, F, characterSectionTransfer_self] using congrFun he z

/-- The canonical real Jacquet map is a Whittaker intertwiner of the actual standard
module at every character exponent vector. -/
def RealGodementCanonicalEquivarianceStatement (r : ℕ) : Prop :=
  ∀ (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    IsRealWhittakerIntertwiner r (characterList p z) (-a) (canonicalJacquetMap a p z)

theorem realGodementCanonicalEquivariance : RealGodementCanonicalEquivarianceStatement r := by
  intro a p z
  have hReg (f : V(p,z)) := canonicalJacquetMap_derivative_mem_regularFunctions a p z f []
  refine ⟨fun f => (hReg f).1, fun f => (hReg f).2.1, fun f => ?_, ?_, ?_⟩
  · obtain ⟨C, N, _, h⟩ := (hReg f).2.2
    exact ⟨C, N, h⟩
  · intro k f f' hf
    let u : U := ⟨k.val.val, k.property⟩
    have hu : Unitary.toUnits u = k.val := Units.ext rfl
    have he : f' = realStandardRep _ _ u f := by
      apply Subtype.ext
      rw [realStandardRep_apply_coe, hu]
      exact hf
    rw [he, ← hu]
    exact canonicalJacquetMap_compactAction a p z f u
  · intro Y f f' hf
    have he : f' = realStandardLie _ _ (1 ⊗ₜ Y) f :=
      Subtype.ext (hf.trans (realStandardLie_one_tmul_apply_coe _ _ Y f).symm)
    rw [he]
    exact canonicalJacquetMap_lieAction a p z f Y

end Langlands.Global.RankinSelbergGlobal.RealGodement
