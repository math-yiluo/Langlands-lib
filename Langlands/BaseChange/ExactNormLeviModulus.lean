import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration

/-! Determinant and half modulus comparisons at a cyclic norm. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.GeneralLinear Langlands.Unramified Langlands.Weil.Local
open scoped NNReal

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private theorem canonicalNorm_cyclicAut (x : E.Carrier) : E.canonicalNorm (σ x) = E.canonicalNorm x :=
  canonicalNorm_map E E (σ.restrictScalars (Padic p)).toAlgHom x

/-- The entrywise field automorphism preserves the standard integral subgroup. -/
theorem entrywiseAut_mem_sphericalOpenSubgroup {r : ℕ} {a : GeneralLinear (r + 1) E.Carrier}
    (ha : a ∈ sphericalOpenSubgroup E r) :
    entrywiseAut σ (r + 1) a ∈ sphericalOpenSubgroup E r := by
  let T := E.canonicalTopologicalData
  let 𝒪 := (ValuativeRel.valuation E.Carrier).integer
  have hInt {x : E.Carrier} (hx : x ∈ 𝒪) : σ x ∈ 𝒪 := by
    apply (T.canonicalNorm_le_one_iff_mem_integers (σ x)).mp
    rw [canonicalNorm_cyclicAut F E σ]
    exact (T.canonicalNorm_le_one_iff_mem_integers x).mpr hx
  obtain ⟨hA, hAinv⟩ := (Conductor.mem_integralSubgroup 𝒪 r a).mp ha
  apply (Conductor.mem_integralSubgroup 𝒪 r (entrywiseAut σ (r + 1) a)).mpr
  constructor
  · intro i j
    exact hInt (hA i j)
  · intro i j
    rw [← map_inv]
    exact hInt (hAinv i j)

/-- Applying a p-adic field automorphism to every entry preserves the
residue-normalized determinant character. -/
theorem padicDeterminantNorm_entrywiseAut (n : ℕ) (g : GeneralLinear n E.Carrier) :
    E.canonicalTopologicalData.determinantNorm n (entrywiseAut σ n g) =
      E.canonicalTopologicalData.determinantNorm n g := by
  apply Units.ext
  apply NNReal.eq
  rw [E.canonicalTopologicalData.determinantNorm_eq_canonicalNorm_pow_degree,
    E.canonicalTopologicalData.determinantNorm_eq_canonicalNorm_pow_degree]
  have hdet : (GeneralLinear.determinant (entrywiseAut σ n g) : E.Carrier) =
      σ (GeneralLinear.determinant g : E.Carrier) := by
    change ((g.val.map (σ : E.Carrier →+* E.Carrier)).det) = _
    exact (RingHom.map_det (σ : E.Carrier →+* E.Carrier) g.val).symm
  rw [hdet, canonicalNorm_cyclicAut F E σ]

private theorem determinantNorm_baseChange_pow [Module.Finite F.Carrier E.Carrier]
    (n : ℕ) (g : GeneralLinear n F.Carrier) :
    E.canonicalTopologicalData.determinantNorm n (baseChange F.Carrier E.Carrier n g) =
      (F.canonicalTopologicalData.determinantNorm n g) ^ Module.finrank F.Carrier E.Carrier := by
  apply Units.ext
  apply NNReal.eq
  rw [E.canonicalTopologicalData.determinantNorm_eq_canonicalNorm_pow_degree,
    Units.val_pow_eq_pow_val, NNReal.coe_pow,
    F.canonicalTopologicalData.determinantNorm_eq_canonicalNorm_pow_degree]
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier
  have hdet : (GeneralLinear.determinant (baseChange F.Carrier E.Carrier n g) : E.Carrier) =
      f (GeneralLinear.determinant g : F.Carrier) := by
    change ((g.val.map (algebraMap F.Carrier E.Carrier)).det) = _
    exact (RingHom.map_det (algebraMap F.Carrier E.Carrier) g.val).symm
  rw [hdet, canonicalNorm_map, ← pow_mul, Module.finrank_mul_finrank]

private theorem determinantNorm_cyclicNorm (n l : ℕ) (d : GeneralLinear n E.Carrier) :
    E.canonicalTopologicalData.determinantNorm n (cyclicNorm σ l d) =
      (E.canonicalTopologicalData.determinantNorm n d) ^ l := by
  induction l with
  | zero => simp only [cyclicNorm_zero, map_one, pow_zero]
  | succ l ih => rw [cyclicNorm_succ, map_mul, ih, padicDeterminantNorm_entrywiseAut F E, pow_succ]

/-- The residue-normalized determinant norms agree at an exact cyclic norm. -/
theorem determinantNorm_eq_of_exactNorm {n l : ℕ} (hσ : IsCyclicAlgebra σ l)
    (g : GeneralLinear n F.Carrier) (d : GeneralLinear n E.Carrier)
    (hd : cyclicNorm σ l d = baseChange F.Carrier E.Carrier n g) :
    E.canonicalTopologicalData.determinantNorm n d = F.canonicalTopologicalData.determinantNorm n g := by
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  have he := congrArg (E.canonicalTopologicalData.determinantNorm n) hd
  rw [determinantNorm_cyclicNorm F E σ, determinantNorm_baseChange_pow F E, hσ.2.1] at he
  apply Units.ext
  have hv := congrArg Units.val he
  simp only [Units.val_pow_eq_pow_val] at hv
  exact (pow_left_inj₀ zero_le zero_le hσ.pos.ne').mp hv

/-- The positive half moduli of the two parabolics agree at a blockwise exact norm. -/
theorem leviHalfModulus_eq_of_exactNorm {n l : ℕ} (B : BlockShape n)
    (L : B.Levi F.Carrier) (D : B.Levi E.Carrier) (hσ : IsCyclicAlgebra σ l)
    (hd : ∀ i, cyclicNorm σ l (D i) = baseChange F.Carrier E.Carrier (B.size i) (L i)) :
    E.canonicalTopologicalData.leviHalfModulus B D =
      F.canonicalTopologicalData.leviHalfModulus B L := by
  have hDet (i : Fin B.length) := determinantNorm_eq_of_exactNorm F E σ hσ (L i) (D i) (hd i)
  have hMod : E.canonicalTopologicalData.leviModulus B D = F.canonicalTopologicalData.leviModulus B L := by
    simp only [PadicField.TopologicalData.leviModulus_apply, hDet]
  apply Units.ext
  simp only [PadicField.TopologicalData.leviHalfModulus_apply, hMod]

/-- Twisted conjugation of the Levi element preserves the positive half modulus. -/
theorem leviHalfModulus_twistedConj {n : ℕ} (B : BlockShape n) (D U : B.Levi E.Carrier) :
    E.canonicalTopologicalData.leviHalfModulus B (U⁻¹ * D * leviAut σ B U) =
      E.canonicalTopologicalData.leviHalfModulus B D := by
  let κ := E.canonicalTopologicalData.leviHalfModulus B
  have hMod : E.canonicalTopologicalData.leviModulus B (leviAut σ B U) =
      E.canonicalTopologicalData.leviModulus B U := by
    simp only [PadicField.TopologicalData.leviModulus_apply, leviAut_apply, padicDeterminantNorm_entrywiseAut F E σ]
  have he : κ (leviAut σ B U) = κ U := by
    apply Units.ext
    simp only [κ, PadicField.TopologicalData.leviHalfModulus_apply, hMod]
  change κ _ = κ D
  rw [map_mul, map_mul, map_inv, he, mul_comm (κ U)⁻¹,
    mul_assoc, inv_mul_cancel, mul_one]

end Langlands.BaseChange
