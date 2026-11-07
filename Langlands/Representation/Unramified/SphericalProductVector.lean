import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Tensor.ExternalSubquotient
import Langlands.Group.GL.IntegralSubgroup

/-! Spherical vectors in normalized induction of norm-one-trivial factors. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The Levi projection of an integral parabolic matrix has norm-one block
 determinants, in every block size. -/
theorem blockLeviProjection_mem_normOneLevi_of_integral
    {n : ℕ} (B : GeneralLinear.BlockShape n) (g : B.parabolic F.Carrier)
    (hg : g.val ∈ GeneralLinearGroup.integralSubgroup (Fin n) T.Integers) :
    B.leviProjection F.Carrier g ∈ T.normOneLevi B := by
  have hK := (GeneralLinearGroup.mem_integralSubgroup (Fin n) T.Integers g.val).mp hg
  rw [T.mem_normOneLevi]
  intro i
  apply Unramified.SphericalExistence.determinantNorm_eq_one_of_integral F T
  · intro a b
    rw [B.leviProjection_apply]
    exact hK.1 _ _
  · intro a b
    rw [← Pi.inv_apply, ← map_inv, B.leviProjection_apply]
    exact hK.2 _ _

/-- Norm-one-trivial factors make the entire normalized inducing space fixed
by the intersection of the parabolic with the actual integral subgroup. -/
theorem normalizedProductInducing_eq_self_of_integral
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : ∀ i, fixedVectors (σ i) (T.determinantNorm (B.size i)).ker = ⊤)
    (g : B.parabolic F.Carrier)
    (hg : g.val ∈ GeneralLinearGroup.integralSubgroup (Fin n) T.Integers)
    (v : PiTensorProduct ℂ V) :
    twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier)) g v = v := by
  have hm := T.blockLeviProjection_mem_normOneLevi_of_integral B g hg
  have hhalf : T.parabolicHalfModulus B g = 1 := by
    rw [T.parabolicHalfModulus_apply]
    exact (T.leviHalfModulus_eq_one B _).mpr (T.normOneLevi_le_ker_leviModulus B hm)
  have hnorm := (T.mem_normOneLevi B _).mp hm
  have hact : ∀ i (w : V i), σ i (B.leviProjection F.Carrier g i) w = w := by
    intro i w
    have hw : w ∈ fixedVectors (σ i) (T.determinantNorm (B.size i)).ker := by
      rw [hσ i]
      trivial
    exact hw ⟨_, hnorm i⟩
  change (T.parabolicHalfModulus B g : ℂ) •
    B.blockTensor σ (B.leviProjection F.Carrier g) v = v
  rw [hhalf, Units.val_one, one_smul]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
      rw [map_smul, B.blockTensor_tprod]
      congr 2
      funext i
      exact hact i (w i)
  | add x y hx hy => rw [map_add, hx, hy]

end Langlands.PadicField.TopologicalData

namespace Langlands.Unramified.SphericalProduct

open Correspondence

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Iwasawa decomposition for every actual upper block parabolic. -/
theorem exists_parabolic_mul_spherical {r : ℕ} (B : GeneralLinear.BlockShape (r + 1))
    (g : GeneralLinear (r + 1) F.Carrier) :
    ∃ b : B.parabolic F.Carrier, ∃ k ∈ sphericalOpenSubgroup F r, g = b.val * k := by
  let := F.canonicalTopologicalData.valuativeRel
  obtain ⟨b, hb, k, hk, rfl⟩ :=
    GeneralLinear.Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F.Carrier) g
  exact ⟨⟨b, B.mem_parabolic_of_isUpperTriangular b hb⟩, k, hk, rfl⟩

/-- Every vector in the inducing tensor extends to a spherical smooth induced
function when each factor is trivial on its determinant norm-one subgroup. -/
theorem exists_fixed_productFunction {r : ℕ} (B : GeneralLinear.BlockShape (r + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : ∀ i, fixedVectors (σ i)
      (F.canonicalTopologicalData.determinantNorm (B.size i)).ker = ⊤)
    (v : PiTensorProduct ℂ V) :
    ∃ f : Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (F.canonicalTopologicalData.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))),
      Induction.eval _ _ f 1 = v ∧
      f ∈ fixedVectors (F.canonicalTopologicalData.normalizedProductInduced B σ)
        (sphericalSubgroup F r) := by
  apply SphericalExistence.exists_fixed_smoothFunction _ _ (sphericalOpenSubgroup F r)
    (exists_parabolic_mul_spherical F B) v
  intro g hg
  apply F.canonicalTopologicalData.normalizedProductInducing_eq_self_of_integral B σ hσ g
  exact (Conductor.mem_integralSubgroup _ r _).mp hg

/-- Choose a nonzero actual spherical vector in the normalized product of
nonzero norm-one-trivial factors. -/
def sphericalProductVector {r : ℕ} (B : GeneralLinear.BlockShape (r + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hV : ∀ i, Nontrivial (V i))
    (hσ : ∀ i, fixedVectors (σ i)
      (F.canonicalTopologicalData.determinantNorm (B.size i)).ker = ⊤) :
    {f : fixedVectors (F.canonicalTopologicalData.normalizedProductInduced B σ)
      (sphericalSubgroup F r) // f ≠ 0} := by
  letI := FiniteTensor.nontrivial_piTensorProduct hV
  let v := Classical.choose (exists_ne (0 : PiTensorProduct ℂ V))
  have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : PiTensorProduct ℂ V))
  let f := (exists_fixed_productFunction F B σ hσ v).choose
  have he := (exists_fixed_productFunction F B σ hσ v).choose_spec.1
  have hf := (exists_fixed_productFunction F B σ hσ v).choose_spec.2
  refine ⟨⟨f, hf⟩, ?_⟩
  intro hz
  apply hv
  rw [← he]
  change Induction.eval _ _ f 1 = 0
  have hz' : f = 0 := congrArg Subtype.val hz
  rw [hz']
  rfl

theorem normalizedProductInduced_fixedVectors_ne_bot
    {r : ℕ} (B : GeneralLinear.BlockShape (r + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hV : ∀ i, Nontrivial (V i))
    (hσ : ∀ i, fixedVectors (σ i)
      (F.canonicalTopologicalData.determinantNorm (B.size i)).ker = ⊤) :
    fixedVectors (F.canonicalTopologicalData.normalizedProductInduced B σ)
      (sphericalSubgroup F r) ≠ ⊥ := by
  let f := sphericalProductVector F B σ hV hσ
  intro h
  have hf : f.val.val = 0 := (Submodule.mem_bot ℂ).mp (h ▸ f.val.property)
  exact f.property (Subtype.ext hf)

end Langlands.Unramified.SphericalProduct
